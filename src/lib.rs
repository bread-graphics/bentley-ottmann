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
//! ## Examples
//!
//! ```rust
//! use bentley_ottmann::bentley_ottmann;
//! use geometry::{Direction, Edge, Line, Point2D, Vector2D};
//!
//! let edges = vec![
//!     Edge {
//!        line: Line {
//!           point: Point2D::new(0.0, 0.0),
//!           vector: Vector2D::new(1.0, 2.0),
//!        },
//!        top: 0.0,
//!        bottom: 2.0,
//!        direction: Direction::Forward,
//!     },
//!     Edge {
//!        line: Line {
//!           point: Point2D::new(0.0, 2.0),
//!           vector: Vector2D::new(1.0, -2.0),
//!        },
//!        top: 0.0,
//!        bottom: 2.0,
//!        direction: Direction::Forward,
//!     },
//! ];
//!
//! let mut intersects = bentley_ottmann(edges);
//! assert_eq!(intersects.next(), Some(Point2D::new(0.5, 1.0)));
//! assert_eq!(intersects.next(), None);
//! ```
//!
//! [Bentley-Ottmann algorithm]: https://en.wikipedia.org/wiki/Bentley%E2%80%93Ottmann_algorithm

#![no_std]
#![forbid(unsafe_code, rust_2018_idioms)]

extern crate alloc;

use core::{iter::FusedIterator, num::NonZeroUsize};
use geometry::{Edge, FillRule, Point2D, Scalar, Trapezoid};
use num_traits::Bounded;

mod algorithm;
mod compare;

/// The whole point.
///
/// This function iterates over the intersections between the given
/// line segments. It returns an iterator over the intersections.
///
/// The iterator does not yield intersections lazily; the entire
/// `segments` iterator is consumed before the iterator is created.
pub fn bentley_ottmann<Num: Scalar + Bounded + Default>(
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
pub fn bentley_ottmann_events<Num: Scalar + Bounded + Default>(
    segments: impl IntoIterator<Item = Edge<Num>>,
) -> BentleyOttmann<Num> {
    BentleyOttmann {
        inner: algorithm::Algorithm::new(segments.into_iter(), {
            // doesn't matter, we're not tesselating
            FillRule::Winding
        }),
    }
}

/// Rasterizes the polygon defined by the edges into trapezoids.
pub fn trapezoids<Num: Scalar + Bounded + Default>(
    segments: impl IntoIterator<Item = Edge<Num>>,
    fill_rule: FillRule,
) -> Trapezoids<Num> {
    Trapezoids {
        inner: algorithm::Algorithm::new(segments.into_iter(), fill_rule),
    }
}

/// An event that may occur in the Bentley-Ottmann algorithm.
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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

pub struct BentleyOttmann<Num> {
    inner: algorithm::Algorithm<Num>,
}

impl<Num: Scalar> Iterator for BentleyOttmann<Num> {
    type Item = Event<Num>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_event::<false>()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let heap_len = self.inner.queue_len();

        (heap_len, Some(heap_len * 3))
    }
}

impl<Num: Scalar> FusedIterator for BentleyOttmann<Num> {}

pub struct Trapezoids<Num> {
    inner: algorithm::Algorithm<Num>,
}

impl<Num: Scalar> Iterator for Trapezoids<Num> {
    type Item = Trapezoid<Num>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_trap()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let traps = self.inner.pending_traps();
        (
            traps,
            Some(traps.saturating_add(self.inner.queue_len().saturating_mul(2))),
        )
    }
}
