//                Copyright John Nunley, 2022
// Distributed under the Boost Software License, Version 1.0.
//        (See accompanying file LICENSE or copy at
//          https://www.boost.org/LICENSE_1_0.txt)

//! A pure-Rust implementation of the [Bentley-Ottmann algorithm] for 
//! finding intersections between line segments.
//! 
//! The Bentley-Ottmann algorithm finds the intersections between a set of
//! line segments. It operates in `O((n + k) log n)` time. It functions
//! by creating a set of "start", "stop" and "intersect" events, and then
//! using a priority queue of those events to calculate which lines
//! should be considered for intersection.
//! 
//! The algorithm operates under certain assumptions.
//! 
//! - There are no vertical segments (e.g. segments with the same two `x`
//!   coordinates).
//! - Segments that intersect at their endpoints are not considered.
//! - Three or more lines do not share a common intersection.
//! - No two lines intersect at the same point.
//! 
//! The [`bentley_ottmann`] function runs the algorithm in the form of
//! an iterator over the intersections. Certain applications may find
//! the [`bentley_ottmann_events`] function, which iterates over *all*
//! of the events instead of just intersections, more useful.
//!
//! [Bentley-Ottmann algorithm]: https://en.wikipedia.org/wiki/Bentley%E2%80%93Ottmann_algorithm

#![no_std]
#![forbid(unsafe_code, rust_2018_idioms)]

extern crate alloc;

use alloc::{collections::BinaryHeap, vec::Vec};
use core::{
    cell::Cell,
    cmp::{self, Reverse},
    iter::FusedIterator,
    num::NonZeroUsize,
};
use geometry::{Edge, Line, Point2D, Scalar, Slope};
use num_traits::Bounded;

mod compare;
use compare::AbsoluteEq;

/// The whole point.
/// 
/// This function iterates over the intersections between the given
/// line segments. It returns an iterator over the intersections.
/// 
/// The iterator does not yield intersections lazily; the entire 
/// `segments` iterator is consumed before the iterator is created.
pub fn bentley_ottmann<Num: Scalar + Bounded>(
    segments: impl IntoIterator<Item = Edge<Num>>,
) -> impl FusedIterator<Item = Point2D<Num>> {
    bentley_ottmann_events(segments).filter_map(|event| {
        if matches!(event.event_type, EventType::Intersection { .. }) {
            Some(event.point)
        } else {
            None
        }
    })
}

/// Get an iterator over the Bentley-Ottmann algorithm's output.
/// 
/// This function returns an iterator over the Bentley-Ottmann algorithm's
/// events. The iterator yields all of the events, not just intersections.
/// 
/// The iterator does not yield intersections lazily; the entire
/// `segments` iterator is consumed before the iterator is created.
pub fn bentley_ottmann_events<Num: Scalar + Bounded>(
    segments: impl IntoIterator<Item = Edge<Num>>,
) -> BentleyOttmann<Num> { 
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
                NonZeroUsize::new(i + 1).expect("cannot use more than std::usize::MAX segments"),
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

    BentleyOttmann {
        edges: Edges { edges },
        event_queue: heap,
        sweep_line: SweepLine::default(),
    }
}

/// An event that may occur in the Bentley-Ottmann algorithm.
pub struct Event<Num> {
    /// The edge that this event is associated with.
    pub edge: Edge<Num>,
    /// The event type.
    pub event_type: EventType<Num>,
    /// The point that this event is associated with.
    pub point: Point2D<Num>,
    /// The index of the edge that this event is associated with.
    /// 
    /// It is shifted up by one so that we can take advantage
    /// of niching the `NonZeroUsize` structure.
    pub edge_id: NonZeroUsize,
}

/// The type of event that may occur in the Bentley-Ottmann algorithm.
pub enum EventType<Num> {
    /// A start event, or the beginning of a segment.
    Start,
    /// A stop event, or the end of a segment.
    Stop,
    /// An intersection event.
    Intersection {
        /// The other edge we intersect with.
        other_edge: Edge<Num>,
        /// The other ID of the edge we intersect with.
        other_edge_id: NonZeroUsize,
    },
}

/// An iterator over the Bentley-Ottmann algorithm's output.
/// 
/// This is the iterator returned by [`bentley_ottmann_events`].
pub struct BentleyOttmann<Num> {
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
}

impl<Num: Scalar> Iterator for BentleyOttmann<Num> {
    type Item = Event<Num>;

    fn next(&mut self) -> Option<Self::Item> {
        // pop an event from the event queue
        let Reverse(AbsoluteEq(EventOrder(event))) = self.event_queue.pop()?;

        // process the event
        match event.event_type {
            EventType::Start => {
                // add the event to the sweep line
                let edge = self.edges.get(event.edge_id);
                self.sweep_line.add(edge, &self.edges);

                // push a corresponding stop event to the event quque
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
            EventType::Stop => {
                // remove the event from the sweep line
                let edge = self.edges.get(event.edge_id);
                let prev = edge.prev(&self.edges);
                let next = edge.next(&self.edges);
                self.sweep_line.remove(edge, &self.edges);

                if let (Some(prev), Some(next)) = (prev, next) {
                    // insert intersection between them
                    self.event_queue.extend(
                        intersection_event(prev, next)
                            .map(|event| Reverse(AbsoluteEq(EventOrder(event)))),
                    );
                }
            }
            EventType::Intersection { other_edge_id, .. } => {
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
        }

        // return the event
        Some(event)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // at least, we have `event_queue` events left
        // at most, each event is a start that will lead to a
        // stop event and an intersect event
        let len = self.event_queue.len();
        (len, len.checked_mul(3))
    }
}

// once the event queue is exhausted, it will never produce another
// event, therefore we are fused
impl<Num: Scalar> FusedIterator for BentleyOttmann<Num> {}

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
    current_edge: EdgeId,
    current_y: Num,
}

impl<Num: Bounded> Default for SweepLine<Num> {
    fn default() -> Self {
        Self {
            head: None,
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
}

/// The segment type used within the Bentley-Ottmann algorithm.
#[derive(Debug, Clone)]
struct BoEdge<Num> {
    segment: Edge<Num>,
    /// The lowest X coordinate for this edge.
    lowest_x: Point2D<Num>,
    /// The highest X coordinate for this edge.
    highest_x: Point2D<Num>,
    id: NonZeroUsize,
    prev: Cell<EdgeId>,
    next: Cell<EdgeId>,
}

impl<Num> BoEdge<Num> {
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
}

impl<Num: Scalar> BoEdge<Num> {
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
        }
    }
}

fn points_of_edge<Num: Scalar>(edge: &Edge<Num>) -> (Point2D<Num>, Point2D<Num>) {
    let p1 = Point2D::new(x_for_y(&edge.line, edge.top), edge.top);
    let p2 = Point2D::new(x_for_y(&edge.line, edge.bottom), edge.bottom);

    (p1, p2)
}

fn x_for_y<Num: Scalar>(line: &Line<Num>, y: Num) -> Num {
    line.equation()
        .solve_x_for_y(y)
        .expect("unexpected horizontal line")
}

type EdgeId = Option<NonZeroUsize>;

const EXPECTED_NOT_NAN: &str = "Expected non-NaN values";
