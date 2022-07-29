// This file is part of bentley-ottmann.
//
// bentley-ottmann is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation,
// either version 3 of the License, or (at your option)
// any later version.
//
// bentley-ottmann is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty
// of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
// See the GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General
// Public License along with bentley-ottmann. If not, see
// <https://www.gnu.org/licenses/>.

mod edge;
mod linked_list;
mod priority_queue;
mod sweep_line;

use crate::{utils::approx_neq, EventType};
use alloc::vec::Vec;
use core::num::NonZeroUsize;
use edge::{BoEdge, Edges};
use geometry::{Edge, FillRule, Scalar, Trapezoid};
use linked_list::LinkedList;
use priority_queue::PriorityQueue;
use sweep_line::SweepLine;

use crate::Event;

/// The internal algorithm used to compute intersections and,
/// potentially, trapezoids.
#[derive(Debug)]
pub(crate) struct Algorithm<Num: Scalar, Variant> {
    /// The list of edges to be used in the algorithm.
    edges: Edges<Num>,
    /// The priority queue of events.
    event_queue: PriorityQueue<Num>,
    /// The sweep line.
    ///
    /// This contains the current Y coordinate as well as the list of
    /// active edges.
    sweep_line: SweepLine<Num>,
    /// The variant of the algorithm to use.
    ///
    /// This is either a ZST if we're looking for intersections, or
    /// contains a queue of trapezoids that we're looking for.
    variant: Variant,
}

/// The variant of the algorithm we are using.
pub(crate) trait Variant<Num: Scalar>: Sized {
    /// Some kind of input needed to create this variant.
    type Input;

    /// Create a new variant from the given input.
    fn new(input: Self::Input) -> Self;
    /// Complete the trapezoid computation if we've incremented the
    /// Y coordinate.
    fn increment_y(alg: &mut Algorithm<Num, Self>, new_y: Num);
    /// See if there are any stopped events we need to handle while
    /// starting a new line.
    fn handle_start_event(sw: &mut SweepLine<Num>, edge: &BoEdge<Num>, all: &Edges<Num>);
}

/// We are not concerned about trapezoids in this algorithm.\
#[derive(Debug)]
pub(crate) struct NoTrapezoids;

/// We are concerned about trapezoids in this algorithm.
#[derive(Debug)]
pub(crate) struct Trapezoids<Num> {
    /// The list of trapezoids to return.
    trapezoids: Vec<Trapezoid<Num>>,
    /// Have we fused together the leftovers yet?
    fused_leftovers: bool,
    /// The fill rule we use to create traps.
    fill_rule: FillRule,
}

impl<Num: Scalar, Var: Variant<Num>> Algorithm<Num, Var> {
    /// Create a new algorithm.
    pub(crate) fn new(segments: impl Iterator<Item = Edge<Num>>, input: Var::Input) -> Self {
        // collect the edges into a vector
        let edges: Edges<Num> = segments
            .enumerate()
            .map(|(i, segment)| {
                BoEdge::from_edge(
                    segment,
                    NonZeroUsize::new(i + 1).expect("cannot have more than usize::MAX - 1 edges"),
                )
            })
            .collect::<Vec<_>>()
            .into();

        // begin a heap consisting of the start events for every edge
        let pqueue: PriorityQueue<Num> = (&edges)
            .into_iter()
            .map(|edge| edge.start_event())
            .collect();

        tracing::trace!(
            "Collected segments into BO Edge structures: {:#?}",
            &edges
        );

        Self {
            edges,
            event_queue: pqueue,
            sweep_line: SweepLine::default(),
            variant: Var::new(input),
        }
    }

    /// Get the length of the queue of events.
    pub(crate) fn queue_len(&self) -> usize {
        self.event_queue.len()
    }

    /// Get the next event in the algorithm.
    pub(crate) fn next_event(&mut self) -> Option<Event<Num>> {
        // pop an event from the event queue
        let event = self.event_queue.pop()?;

        tracing::trace!(
            "Encountered event: {:#?}",
            &event
        );

        // if the Y coordinate is different from the last Y coordinate,
        // we need to emit one or more trapezoids
        Var::increment_y(self, event.point.y);
        self.sweep_line.set_current_y(event.point.y);

        match event.event_type {
            EventType::Start => {
                self.handle_start_event(&event);
            }
            EventType::Stop => {
                self.handle_stop_event(&event);
            }
            EventType::Intersection { .. } => {
                self.handle_intersection_event(&event);
            }
        }

        Some(event)
    }

    /// Handle a start event.
    fn handle_start_event(&mut self, event: &Event<Num>) {
        // add the edge to the sweep line
        let edge = self.edges.get(event.edge_id);
        self.sweep_line.add_edge(edge, &self.edges);

        // push a stop event to the event queue
        self.event_queue.push(edge.stop_event());

        // if we need to, handle trapezoid generation
        Var::handle_start_event(&mut self.sweep_line, edge, &self.edges);

        // determine if we intersect with the previous and next
        // active edges
        let intersects = {
            let prev = edge
                .prev()
                .map(|prev| self.edges.get(prev))
                .and_then(|prev| prev.intersection_event(edge));
            let next = edge
                .next()
                .map(|next| self.edges.get(next))
                .and_then(|next| intersection_event(next, edge));

            prev.into_iter().chain(next)
        };

        self.event_queue.extend(intersects);
    }

    /// Handle a stop event.
    fn handle_stop_event(&mut self, event: &Event<Num>) {
        // remove the edge from the sweep line
        let edge = self.edges.get(event.edge_id);
        let prev = edge.prev();
        let next = edge.next();
        self.sweep_line.remove_edge(edge, &self.edges);

        // if we have a previous and next edge, see if they intersect
        if let (Some(prev), Some(next)) = (prev, next) {
            let prev = self.edges.get(prev);
            let next = self.edges.get(next);
            let intersect = intersection_event(prev, next);
            self.event_queue.extend(intersect);
        }
    }

    /// Handle an intersection event.
    fn handle_intersection_event(&mut self, event: &Event<Num>) {
        // swap the edges in the sweep line
        let edge = self.edges.get(event.edge_id);
        self.sweep_line.swap_edge(edge, &self.edges);

        // the other edge should be before the current edge in the
        // sweep line
        let other = edge.prev().map(|prev| self.edges.get(prev));

        if let Some(other) = other {
            // calculate intersections with the lines before and after
            let intersects = {
                let prev = other
                    .prev()
                    .map(|prev| self.edges.get(prev))
                    .and_then(|prev| intersection_event(prev, other));
                let next = other
                    .next()
                    .map(|next| self.edges.get(next))
                    .and_then(|next| intersection_event(other, next));

                prev.into_iter().chain(next)
            };

            self.event_queue.extend(intersects)
        }
    }
}

impl<Num: Scalar> Algorithm<Num, Trapezoids<Num>> {
    /// Get the next trapezoid in the algorithm.
    pub(crate) fn next_trapezoid(&mut self) -> Option<Trapezoid<Num>> {
        loop {
            match self.variant.trapezoids.pop() {
                Some(trap) => return Some(trap),
                None => {
                    // try to repopulate the trapezoid list
                    // by fetching the next event
                    //
                    // if we're out of events, try to run through
                    // the last leftovers and squeeze trapezoids
                    // out of there
                    self.next_event().map(|_| ()).or_else(|| {
                        if self.variant.fused_leftovers {
                            None
                        } else {
                            self.variant.fused_leftovers = true;

                            self.variant.trapezoids.extend(
                                self.sweep_line
                                    .take_leftovers(&self.edges)
                                    .filter_map(|edge| {
                                        tracing::trace!("Completing trapezoid for: {}", edge.id());
                                        edge.complete_trapezoid(edge.edge().bottom, &self.edges)
                                    }),
                            );

                            Some(())
                        }
                    })?;
                }
            }
        }
    }

    /// Get the number of pending trapezoids.
    pub(crate) fn trapezoid_len(&self) -> usize {
        self.variant.trapezoids.len()
    }
}

fn intersection_event<Num: Scalar>(e1: &BoEdge<Num>, e2: &BoEdge<Num>) -> Option<Event<Num>> {
    // e1 and e2 are originally ordered by their top points
    // if the top point for e2 comes before e1, we've already
    // emitted the intersection event for e2 and e1
    if e2.lowest_y().x <= e1.lowest_y().x {
        return None;
    }

    e1.intersection_event(e2)
}

impl<Num: Scalar> Variant<Num> for NoTrapezoids {
    type Input = ();
    fn new(_: ()) -> Self {
        Self
    }
    fn increment_y(_alg: &mut Algorithm<Num, Self>, _new_y: Num) {}
    fn handle_start_event(_alg: &mut SweepLine<Num>, _edge: &BoEdge<Num>, _all: &Edges<Num>) {}
}

impl<Num: Scalar> Variant<Num> for Trapezoids<Num> {
    type Input = FillRule;

    fn new(input: Self::Input) -> Self {
        Self {
            fill_rule: input,
            fused_leftovers: false,
            trapezoids: Vec::new(),
        }
    }

    fn increment_y(alg: &mut Algorithm<Num, Self>, new_y: Num) {
        if approx_neq(alg.sweep_line.current_y(), new_y) {
            // we may need to iterate over the stopped lines to
            // see if there are any trapezoids we can use
            let leftover_edges = alg
                .sweep_line
                .take_leftovers(&alg.edges)
                .filter_map(|edge| edge.complete_trapezoid(edge.edge().bottom, &alg.edges));

            // combine that with the traps that the sweep line may be
            // generating for us
            alg.variant.trapezoids.extend(
                leftover_edges.chain(alg.sweep_line.trapezoids(alg.variant.fill_rule, &alg.edges)),
            );
        }
    }

    fn handle_start_event(sw: &mut SweepLine<Num>, edge: &BoEdge<Num>, all: &Edges<Num>) {
        // iterate over the leftover edges and see if we need
        for line in sw.leftovers(all) {
            if edge.edge().top <= line.edge().bottom && edge.colinear(line) {
                // remove the leftover and break
                edge.take_trapezoid(line);
                sw.remove_leftover(line, all);
                break;
            }
        }
    }
}
