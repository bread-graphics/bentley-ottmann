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

use crate::Event;
use alloc::collections::BinaryHeap;
use core::{
    cmp::{Ordering::Equal, Reverse},
    iter::FromIterator,
};
use geometry::Scalar;

/// The priority queue for events used in the algorithm.
///
/// This is implemented as a min-heap that orders elements first
/// by the point's Y coordinate and then the X coordinate.
#[derive(Debug, Default)]
pub(super) struct PriorityQueue<Num: Scalar> {
    // wrapper justifications:
    // - reverse turns it into a min-heap
    // - EventOrder orders by Y and then X
    heap: BinaryHeap<Reverse<EventOrder<Num>>>,
}

/// A wrapper struct around an `Event` that orders it by
/// the point's Y coordinate and then the X coordinate.
#[derive(Debug)]
#[repr(transparent)]
struct EventOrder<Num>(Event<Num>);

impl<Num: Scalar> PriorityQueue<Num> {
    /// Push an event into this priority queue.
    pub(super) fn push(&mut self, event: Event<Num>) {
        self.heap.push(Reverse(EventOrder(event)));
    }

    /// Pop the next event from this priority queue.
    pub(super) fn pop(&mut self) -> Option<Event<Num>> {
        self.heap.pop().map(|Reverse(EventOrder(event))| event)
    }

    /// Get the number of events in this queue.
    pub(super) fn len(&self) -> usize {
        self.heap.len()
    }
}

impl<Num: Scalar> FromIterator<Event<Num>> for PriorityQueue<Num> {
    fn from_iter<T: IntoIterator<Item = Event<Num>>>(iter: T) -> Self {
        // build the heap
        Self {
            heap: iter
                .into_iter()
                .map(|event| Reverse(EventOrder(event)))
                .collect(),
        }
    }
}

impl<Num: Scalar> Extend<Event<Num>> for PriorityQueue<Num> {
    fn extend<T: IntoIterator<Item = Event<Num>>>(&mut self, iter: T) {
        self.heap
            .extend(iter.into_iter().map(|event| Reverse(EventOrder(event))));
    }
}

impl<Num: Scalar> PartialEq for EventOrder<Num> {
    fn eq(&self, other: &Self) -> bool {
        self.0.point == other.0.point
    }
}

// we assert Eq because the algorithm fails fast on NaN anyhow
impl<Num: Scalar> Eq for EventOrder<Num> {}

impl<Num: Scalar> PartialOrd for EventOrder<Num> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        // cmp by point
        self.0
            .point
            .y
            .partial_cmp(&other.0.point.y)
            .and_then(|cmp| {
                // if equal, cmp by point
                if matches!(cmp, Equal) {
                    self.0.point.x.partial_cmp(&other.0.point.x)
                } else {
                    Some(cmp)
                }
            })
    }
}

// we assert Ord for the same reasons as above
impl<Num: Scalar> Ord for EventOrder<Num> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.partial_cmp(other).expect("Unexpected NaN value")
    }
}
