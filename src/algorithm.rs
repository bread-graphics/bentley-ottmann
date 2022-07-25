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

//! Contains the actual implementation of the Bentley-Ottmann algorithm.
//!
//! The rest of the crate provides an iterator-oriented interface to the
//! Bentley-Ottmann algorithm.

use super::compare::{self, AbsoluteEq};
use crate::{Event, EventType};
use alloc::{collections::BinaryHeap, vec::Vec};
use core::{
    cell::{Cell, RefCell},
    cmp::{self, Reverse},
    iter::FusedIterator,
    num::NonZeroUsize,
};
use geometry::{Direction, Edge, FillRule, Line, Point2D, Scalar, Slope, Trapezoid};
use num_traits::Bounded;

/// The internal details of the algorithm.
pub(crate) struct Algorithm<Num> {
    /// All of the edges currently in the algorithm.
    edges: Edges<Num>,
    /// The current sweep line.
    ///
    /// Also contains a linked list of active edges.
    sweep_line: SweepLine<Num>,
    /// Priority queue of in-progress events.
    ///
    /// We use:
    ///  - Reverse to ensure it is a min heap
    ///  - AbsoluteEq to override PartialEq Rust trickiness
    ///  - EventOrder to ensure it's ordered by X
    event_queue: BinaryHeap<Reverse<AbsoluteEq<EventOrder<Num>>>>,
    /// Filling rule.
    ///
    /// Only relevant for trapezoidification.
    fill_rule: FillRule,
    /// List of trapezoids generated by the algorithm.
    trapezoids: Vec<Trapezoid<Num>>,
}

impl<Num: Scalar + Bounded + Default> Algorithm<Num> {
    pub(crate) fn new(segments: impl Iterator<Item = Edge<Num>>, fr: FillRule) -> Self {
        // collect the segments into an edge list
        let edges = segments
            .into_iter()
            .filter(|edge| {
                // edges with horizontal are forbidden
                if cfg!(debug_assertions) && edge.line.vector.x.is_zero() {
                    tracing::error!("Could not process vertical edge: {:?}", edge);
                    false
                } else {
                    true
                }
            })
            .enumerate()
            .map(|(i, edge)| {
                BoEdge::from_edge(
                    edge,
                    NonZeroUsize::new(i + 1)
                        .expect("cannot use more than std::usize::MAX segments"),
                )
            })
            .collect::<Vec<_>>();

        // make a start event for each edge and push it into a heap
        let mut heap = edges
            .iter()
            .map(|edge| Event {
                edge: edge.segment,
                event_type: EventType::Start,
                point: edge.lowest_x,
                edge_id: edge.id,
            })
            .map(|event| {
                // ensure this is a min-heap ordered by X first
                Reverse(AbsoluteEq(EventOrder(event)))
            })
            .collect::<BinaryHeap<_>>();

        // the heap will have at least double that capacity
        heap.reserve(heap.len() * 2);

        Algorithm {
            edges: Edges { edges },
            event_queue: heap,
            sweep_line: SweepLine::default(),
            trapezoids: Vec::new(),
            fill_rule: fr,
        }
    }
}

impl<Num: Scalar> Algorithm<Num> {
    pub(crate) fn next_trap(&mut self) -> Option<Trapezoid<Num>> {
        loop {
            match self.trapezoids.pop() {
                Some(trap) => return Some(trap),
                None => {
                    self.next_event::<true>()?;
                }
            }
        }
    }

    pub(crate) fn next_event<const GEN_TRAPS: bool>(&mut self) -> Option<Event<Num>> {
        // pop an event from the event queue
        let Reverse(AbsoluteEq(EventOrder(event))) = self.event_queue.pop()?;

        // check to ensure if we need to complete any trapezoids
        if approx_neq(self.sweep_line.current_y, event.point.y) && GEN_TRAPS {
            self.complete_trapezoids(&event);
        }

        // process the event
        match event.event_type {
            EventType::Start => {
                self.handle_start_event::<GEN_TRAPS>(&event);
            }
            EventType::Stop => {
                self.handle_stop_event::<GEN_TRAPS>(&event);
            }
            EventType::Intersection { other_edge_id, .. } => {
                self.handle_intersection(&event, other_edge_id);
            }
        }

        // return the event
        Some(event)
    }

    fn complete_trapezoids(&mut self, event: &Event<Num>) {
        // see if we need to iterate over a stopped line
        if let Some(line) = self.sweep_line.stopped.take() {
            // see if there are any stopped ones we need to iterate over
            for line in self.edges.get(line).iter(&self.edges) {
                if let Some(trap) = line.trapezoid.borrow_mut().take() {
                    self.trapezoids
                        .push(trap.complete(line.id, line.segment.bottom, &self.edges));
                }
            }
        }

        self.trapezoids.extend(
            self.sweep_line
                .traverse_trapezoids(self.fill_rule, &self.edges),
        );
        self.sweep_line.current_y = event.point.y;
    }

    fn handle_start_event<const GEN_TRAPS: bool>(&mut self, event: &Event<Num>) {
        // add the event to the sweep line
        let edge = self.edges.get(event.edge_id);
        self.sweep_line.add(edge, &self.edges);

        // push a corresponding stop event to the event queue
        let (p1, p2) = points_of_edge(&edge.segment);
        let (_, point) = compare::order_points(p1, p2);
        let stop_event = Event {
            point,
            event_type: EventType::Stop,
            edge: edge.segment,
            edge_id: edge.id,
        };
        self.event_queue
            .push(Reverse(AbsoluteEq(EventOrder(stop_event))));

        // determine if this is a continuation of the previously stopped
        // edge
        if GEN_TRAPS {
            if let Some(line) = self.sweep_line.stopped.take() {
                // see if there are any stopped ones we need to iterate over
                for line in self.edges.get(line).iter(&self.edges) {
                    if edge.segment.top <= line.segment.bottom && edge.colinear(line) {
                        // excise the line from the linked list
                        *edge.trapezoid.borrow_mut() = line.trapezoid.borrow_mut().take();

                        if line.prev.get().is_some() {
                            line.prev.set(line.next.get());
                        } else {
                            self.sweep_line.stopped = line.next.get();
                        }

                        if let Some(next) = line.next(&self.edges) {
                            next.prev.set(line.prev.get());
                        }

                        break;
                    }
                }
            }
        }

        // insert intersections with edges before and after this edge
        let prev = edge
            .prev(&self.edges)
            .and_then(|prev| intersection_event(prev, edge));
        let next = edge
            .next(&self.edges)
            .and_then(|next| intersection_event(edge, next));

        self.event_queue.extend(
            prev.into_iter()
                .chain(next)
                .map(|event| Reverse(AbsoluteEq(EventOrder(event)))),
        );
    }

    fn handle_stop_event<const GEN_TRAPS: bool>(&mut self, event: &Event<Num>) {
        // remove the event from the sweep line
        let edge = self.edges.get(event.edge_id);
        let prev = edge.prev(&self.edges);
        let next = edge.next(&self.edges);
        self.sweep_line.remove(edge, &self.edges);

        // we may have a continuation
        let trap = edge.trapezoid.borrow_mut();
        if trap.is_some() && GEN_TRAPS {
            // add in the continuation
            let stopped = self.sweep_line.stopped;
            edge.next.set(stopped);

            if let Some(stopped) = stopped {
                self.edges.get(stopped).link_prev(edge.id);
            }

            self.sweep_line.stopped = Some(edge.id);
            edge.prev.set(None);
        }

        if let (Some(prev), Some(next)) = (prev, next) {
            // insert intersection between them
            self.event_queue.extend(
                intersection_event(prev, next).map(|event| Reverse(AbsoluteEq(EventOrder(event)))),
            );
        }
    }

    fn handle_intersection(&mut self, event: &Event<Num>, other_edge_id: NonZeroUsize) {
        // swap thw two edges in the sweep line
        let edge = self.edges.get(event.edge_id);
        let other_edge = self.edges.get(other_edge_id);
        self.sweep_line.swap(edge, other_edge, &self.edges);

        // make sure the edges are adjacent (they should be)
        if edge.next.get() == Some(other_edge_id) {
            // add intersections between adjacent events
            let prev = edge
                .prev(&self.edges)
                .and_then(|prev| intersection_event(prev, edge));
            let next = other_edge
                .next(&self.edges)
                .and_then(|next| intersection_event(other_edge, next));

            self.event_queue.extend(
                prev.into_iter()
                    .chain(next)
                    .map(|event| Reverse(AbsoluteEq(EventOrder(event)))),
            );
        }
    }

    pub(crate) fn queue_len(&self) -> usize {
        self.event_queue.len()
    }

    pub(crate) fn pending_traps(&self) -> usize {
        self.trapezoids.len()
    }
}

/// Returns the intersection event for two lines if there is a valid
/// intersection event between them.
///
/// # Panics
///
/// This function will return `None` if the lines are parallel.
fn intersection_event<Num: Scalar>(line1: &BoEdge<Num>, line2: &BoEdge<Num>) -> Option<Event<Num>> {
    // tell if the lines even can be intersected
    if line1.highest_x.x <= line2.lowest_x.x {
        return None;
    }

    // equal lines are not intersected
    if line1.segment.line.point == line2.segment.line.point
        && line1.segment.line.vector == line2.segment.line.vector
    {
        return None;
    }

    // compare slopes to ensure the event is valid by using slopes to
    // try to see if the intersection has already occurred
    match Slope::from_line(line1.segment.line).partial_cmp(&Slope::from_line(line2.segment.line)) {
        Some(cmp::Ordering::Greater) => {}
        _ => return None,
    }

    // calculate the intersection point
    let intersect = line1.segment.line.intersection(&line2.segment.line)?;

    // if the intersection is outside the bounds of the lines, it
    // should be ignored
    if (line1.segment.top..line1.segment.bottom).contains(&intersect.y)
        && (line2.segment.top..line2.segment.bottom).contains(&intersect.y)
    {
        Some(Event {
            point: intersect,
            event_type: EventType::Intersection {
                other_edge: line2.segment,
                other_edge_id: line2.id,
            },
            edge_id: line1.id,
            edge: line1.segment,
        })
    } else {
        None
    }
}

/// A transparent struct to ensure that the event is ordered by its
/// X coordinate.
///
/// This allows the priority queue to function properly and yield
/// events in X order.
#[repr(transparent)]
struct EventOrder<Num>(Event<Num>);

impl<Num: Scalar> PartialEq for EventOrder<Num> {
    fn eq(&self, other: &Self) -> bool {
        self.0.point == other.0.point
    }
}

impl<Num: Scalar> PartialOrd for EventOrder<Num> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        match self.0.point.x.partial_cmp(&other.0.point.x) {
            Some(cmp::Ordering::Equal) => self.0.point.y.partial_cmp(&other.0.point.y),
            x => x,
        }
    }
}

/// The list of edges that we are currently using.
///
/// This list's elements should not change position. Mutation of the
/// elements should take place only through the interior mutability
/// within.
struct Edges<Num> {
    edges: Vec<BoEdge<Num>>,
}

impl<Num> Edges<Num> {
    fn get(&self, index: NonZeroUsize) -> &BoEdge<Num> {
        self.edges
            .get(index.get() - 1)
            .expect("Edge index out of bounds")
    }

    fn next_of(&self, edge: &BoEdge<Num>) -> Option<&BoEdge<Num>> {
        edge.next.get().map(|next| self.get(next))
    }

    fn prev_of(&self, edge: &BoEdge<Num>) -> Option<&BoEdge<Num>> {
        edge.prev.get().map(|prev| self.get(prev))
    }
}

/// The sweep line algorithm.
///
/// This contains the current Y coordinate of the sweep line and the
/// list of edges that are currently being processed.
struct SweepLine<Num> {
    /// The head of the linked list making of the edges.
    head: EdgeId,
    stopped: EdgeId,
    current_edge: EdgeId,
    current_y: Num,
}

impl<Num: Bounded> Default for SweepLine<Num> {
    fn default() -> Self {
        Self {
            head: None,
            stopped: None,
            current_edge: None,
            current_y: Num::min_value(),
        }
    }
}

impl<Num: Scalar> SweepLine<Num> {
    /// Compare two edges using the sweep line.
    fn cmp(&self, edge1: &BoEdge<Num>, edge2: &BoEdge<Num>) -> Option<cmp::Ordering> {
        match compare::compare_lines_at_x(edge1.segment.line, edge2.segment.line, self.current_y) {
            Some(cmp::Ordering::Equal) => edge1.segment.bottom.partial_cmp(&edge2.segment.bottom),
            x => x,
        }
    }

    /// Add an edge to the sweep line.
    ///
    /// This function curates a linked list among the edges, and then
    /// sets the current line to the given edge.
    fn add(&mut self, edge: &BoEdge<Num>, all: &Edges<Num>) {
        match self.current_edge {
            Some(current_id) => {
                let current_edge = all.get(current_id);

                // update the linked list
                match self.cmp(current_edge, edge).expect(EXPECTED_NOT_NAN) {
                    cmp::Ordering::Less => {
                        // insert this edge before the next edge
                        let mut valid = current_id;
                        let mut next = current_edge.next.get();

                        while let Some(next_id) = next {
                            // get the next one and compare
                            let current_next = all.get(next_id);

                            match self.cmp(current_next, edge).expect(EXPECTED_NOT_NAN) {
                                cmp::Ordering::Less => {
                                    // keep going
                                    valid = next_id;
                                    next = current_next.next.get();
                                }
                                _ => {
                                    // this is good
                                    break;
                                }
                            }
                        }

                        // update the linked list
                        all.get(valid).link_next(edge.id);
                        edge.link_prev(valid);
                        edge.next.set(next);

                        if let Some(next) = next {
                            all.get(next).link_prev(edge.id);
                        }
                    }
                    cmp::Ordering::Greater => {
                        // insert this edge after the previous edge
                        let mut valid = current_id;
                        let mut prev = current_edge.prev.get();

                        while let Some(prev_id) = prev {
                            // get the previous one and compare
                            let current_prev = all.get(prev_id);

                            match self.cmp(current_prev, edge).expect(EXPECTED_NOT_NAN) {
                                cmp::Ordering::Greater => {
                                    // keep going
                                    valid = prev_id;
                                    prev = current_prev.prev.get();
                                }
                                _ => {
                                    // this is good
                                    break;
                                }
                            }
                        }

                        // update the linked list
                        all.get(valid).link_prev(edge.id);
                        edge.link_next(valid);
                        edge.prev.set(prev);

                        if let Some(prev) = prev {
                            all.get(prev).link_next(edge.id);
                        } else {
                            self.head = Some(edge.id);
                        }
                    }
                    cmp::Ordering::Equal => {
                        // insert this edge one before the current edge
                        edge.next.set(current_edge.next.get());
                        edge.link_prev(current_id);

                        if let Some(ne) = current_edge.next(all) {
                            ne.link_prev(edge.id);
                        }

                        current_edge.link_next(edge.id);
                    }
                }
            }
            None => {
                // insert the current edge into self as head of the list
                self.head = Some(edge.id);
                edge.next.set(None);
            }
        }

        // set current edge to this edge
        self.current_edge = Some(edge.id);
    }

    /// Remove an edge from the sweep line.
    fn remove(&mut self, edge: &BoEdge<Num>, all: &Edges<Num>) {
        // set edge->prev->next to edge->next
        if let Some(prev) = edge.prev.get() {
            all.get(prev).next.set(edge.next.get());
        } else {
            // this is the head
            self.head = edge.next.get();
        }

        // set edge->next->prev to edge->prev
        if let Some(next) = edge.next.get() {
            all.get(next).prev.set(edge.prev.get());
        }

        // if this edge is the current edge, set the edge to one of
        // its neighbors
        if self.current_edge == Some(edge.id) {
            match edge.prev.get() {
                Some(prev) => {
                    self.current_edge = Some(prev);
                }
                None => {
                    self.current_edge = edge.next.get();
                }
            }
        }
    }

    /// Swap the positions of two edges in the sweep line.
    ///
    /// This swaps them such that left is immediately before right.
    fn swap(&mut self, left: &BoEdge<Num>, right: &BoEdge<Num>, all: &Edges<Num>) {
        // swap the left->prev->next for right
        if let Some(prev) = left.prev.get() {
            all.get(prev).link_next(right.id);
        } else {
            // this is the head
            self.head = Some(right.id);
        }

        // swap the right->next->prev for left
        if let Some(next) = right.next.get() {
            all.get(next).link_prev(left.id);
        }

        left.next.set(right.next.get());
        right.link_next(left.id);
        right.prev.set(left.prev.get());
        left.link_prev(right.id);
    }

    /// Begin generating trapezoids.
    fn traverse_trapezoids<'a>(
        &'a mut self,
        fill_rule: FillRule,
        all: &'a Edges<Num>,
    ) -> impl Iterator<Item = Trapezoid<Num>> + 'a {
        let mut leftmost = self.head;
        let mut in_out = 0isize;
        let current_y = self.current_y;

        let mask = match fill_rule {
            FillRule::Winding => 1isize,
            FillRule::EvenOdd => -1,
        };

        self.head
            .map(|leftmost| all.get(leftmost))
            .into_iter()
            .flat_map(|leftmost| leftmost.iter(all))
            .flat_map(move |current| {
                // if this isn't the head and the trapezoid is complete...
                let mut delayed_trap = None;

                if Some(current.id) != leftmost {
                    let mut current_trap = current.trapezoid.borrow_mut();
                    if current_trap.is_some() {
                        // ...delay it until the next trapezoid
                        let left = all.get(leftmost.unwrap());
                        let mut left_trap = left.trapezoid.borrow_mut();

                        if left_trap.is_none() && left.colinear(current) {
                            // continue the trapezoid
                            *left_trap = current_trap.take();
                        } else {
                            // end the trapezoid
                            delayed_trap = left_trap
                                .take()
                                .map(|left_trap| left_trap.complete(left.id, current_y, all));
                        }
                    }
                }

                // figure out if this edge counts
                match current.segment.direction {
                    Direction::Backwards => in_out -= 1,
                    Direction::Forward => in_out += 1,
                }

                let main_trap = if in_out & mask == 0 {
                    // skip colinear edges
                    match current.next.get() {
                        Some(edge) if current.colinear(all.get(edge)) => None,
                        _ => {
                            let left = all.get(leftmost.unwrap());
                            let trap = left.handle_trapezoids(current, current_y, all);
                            leftmost = current.next.get();
                            trap
                        }
                    }
                } else {
                    None
                };

                delayed_trap.into_iter().chain(main_trap)
            })
    }
}

/// The segment type used within the Bentley-Ottmann algorithm.
#[derive(Debug, Clone)]
struct BoEdge<Num> {
    /// The segment that this edge wraps around.
    segment: Edge<Num>,
    /// The lowest X coordinate for this edge.
    lowest_x: Point2D<Num>,
    /// The highest X coordinate for this edge.
    highest_x: Point2D<Num>,
    /// A unique ID used to identify this edge.
    id: NonZeroUsize,
    /// The previous edge in the sweep line.
    prev: Cell<EdgeId>,
    /// The next edge in the sweep line.
    next: Cell<EdgeId>,
    /// A partial trapezoid in the process of being built
    /// by this edge.
    trapezoid: RefCell<Option<PartialTrapezoid<Num>>>,
}

impl<Num: Scalar> BoEdge<Num> {
    // link convenience functions
    fn link_prev(&self, prev: NonZeroUsize) {
        self.prev.set(Some(prev));
    }

    fn link_next(&self, next: NonZeroUsize) {
        self.next.set(Some(next));
    }

    fn next<'all>(&self, all: &'all Edges<Num>) -> Option<&'all BoEdge<Num>> {
        all.next_of(self)
    }

    fn prev<'all>(&self, all: &'all Edges<Num>) -> Option<&'all BoEdge<Num>> {
        all.prev_of(self)
    }

    fn iter<'all>(&self, all: &'all Edges<Num>) -> impl Iterator<Item = &'all BoEdge<Num>> {
        EdgeIterator {
            current_id: Some(self.id),
            all,
        }
    }

    /// Either start a new trapezoid or continue an existing one.
    ///
    /// Returns a trapezoid if one was actually finished.
    fn handle_trapezoids(
        &self, // implied to be left edge
        right: &BoEdge<Num>,
        top: Num,
        all: &Edges<Num>,
    ) -> Option<Trapezoid<Num>> {
        let mut cur_trap = self.trapezoid.borrow_mut();

        // do we already have a current trapezoid
        match &mut *cur_trap {
            cur_trap @ None => {
                // we may create a new one if we aren't colinear with the new edge
                if !self.colinear(right) {
                    // create a new trapezoid
                    *cur_trap = Some(PartialTrapezoid {
                        right: right.id,
                        top,
                    });
                }
            }
            Some(trap) => {
                // we might just be continuing another edge
                if self.colinear(right) {
                    trap.right = right.id;
                } else {
                    // end the trap using this edge
                    let trap = cur_trap.take().unwrap();
                    return Some(trap.complete(self.id, top, all));
                }
            }
        }

        None
    }

    fn colinear(&self, other: &Self) -> bool {
        colinear(&self.segment.line, &other.segment.line)
    }
}

impl<Num: Scalar + Default> BoEdge<Num> {
    fn from_edge(edge: Edge<Num>, id: NonZeroUsize) -> Self {
        let (p1, p2) = points_of_edge(&edge);

        let (lowest_x, highest_x) = if p1.x < p2.x { (p1, p2) } else { (p2, p1) };

        BoEdge {
            segment: edge,
            lowest_x,
            highest_x,
            id,
            prev: Cell::new(None),
            next: Cell::new(None),
            trapezoid: RefCell::new(None),
        }
    }
}

/// A partial trapezoid, for tesselation.
#[derive(Debug, Clone)]
struct PartialTrapezoid<Num> {
    /// The right edge for this trapezoid.
    right: NonZeroUsize,
    /// The top edge for this trapezoid.
    top: Num,
}

impl<Num: Clone> PartialTrapezoid<Num> {
    fn complete(self, left: NonZeroUsize, bottom: Num, all: &Edges<Num>) -> Trapezoid<Num> {
        let PartialTrapezoid { right, top } = self;
        let left = all.get(left);
        let right = all.get(right);

        Trapezoid {
            left: left.segment.line.clone(),
            right: right.segment.line.clone(),
            bottom,
            top,
        }
    }
}

/// Tell if two `Line`s are colinear.
fn colinear<Num: Scalar>(l1: &Line<Num>, l2: &Line<Num>) -> bool {
    let eq = l1.equation();

    // if the two lines are colinear, both of l2's points will have a
    // distance of 0 from l1's equation.
    let p1 = l2.point;
    let p2 = p1 + l2.vector;

    approx_eq(eq.distance_to_point(&p1), Num::ZERO)
        && approx_eq(eq.distance_to_point(&p2), Num::ZERO)
}

fn points_of_edge<Num: Scalar>(edge: &Edge<Num>) -> (Point2D<Num>, Point2D<Num>) {
    let p1 = Point2D::new(x_for_y(&edge.line, edge.top), edge.top);
    let p2 = Point2D::new(x_for_y(&edge.line, edge.bottom), edge.bottom);

    (p1, p2)
}

fn x_for_y<Num: Scalar>(line: &Line<Num>, y: Num) -> Num {
    line.equation()
        .solve_x_for_y(y)
        .expect("unexpected vertical line")
}

fn approx_eq<Num: Scalar>(a: Num, b: Num) -> bool {
    (a - b).abs() < Num::EPSILON
}

fn approx_neq<Num: Scalar>(a: Num, b: Num) -> bool {
    !approx_eq(a, b)
}

struct EdgeIterator<'all, Num> {
    current_id: EdgeId,
    all: &'all Edges<Num>,
}

impl<'all, Num> Iterator for EdgeIterator<'all, Num> {
    type Item = &'all BoEdge<Num>;

    fn next(&mut self) -> Option<Self::Item> {
        let edge = self.all.get(self.current_id?);
        self.current_id = edge.next.get();
        Some(edge)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.current_id.is_some() as usize, None)
    }
}

impl<'all, Num> FusedIterator for EdgeIterator<'all, Num> {}

type EdgeId = Option<NonZeroUsize>;

const EXPECTED_NOT_NAN: &str = "Expected non-NaN values";
