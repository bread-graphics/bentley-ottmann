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

use crate::utils::approx_eq;

use super::{edge::Edges, BoEdge, LinkedList};
use alloc::vec::Vec;
use core::{
    cmp,
    iter::{self, FusedIterator},
    mem,
};
use geometry::{Direction, FillRule, Scalar, Trapezoid};
use tinyvec::ArrayVec;

/// The sweep line, currently traversing the edges.
///
/// It consists of the current Y coordinate as well as
/// a linked list of "active" edges.
#[derive(Debug)]
pub(crate) struct SweepLine<Num> {
    /// The current Y coordinate we are operating at.
    current_y: Num,
    /// The list of active edges.
    ///
    /// Kept in an `Option` so that we can move it out to make insertion
    /// easier.
    active: LinkedList,
    /// The list of edges that are no longer active, but still may
    /// have partial trapezoids.
    leftovers: LinkedList,
}

impl<Num: Scalar> Default for SweepLine<Num> {
    fn default() -> Self {
        Self {
            current_y: Num::min_value(),
            active: LinkedList::default(),
            leftovers: LinkedList::default(),
        }
    }
}

impl<Num: Scalar> SweepLine<Num> {
    /// Get the current Y coordinate.
    pub(super) fn current_y(&self) -> Num {
        self.current_y
    }

    /// Set the current Y coordinate.
    pub(super) fn set_current_y(&mut self, y: Num) {
        self.current_y = y;
    }

    /// Compare two edges along the sweep line.
    pub(super) fn compare_edges(&self, a: &BoEdge<Num>, b: &BoEdge<Num>) -> Option<cmp::Ordering> {
        // compare by their X values at the current Y
        let ax = a.x_at_y(self.current_y());
        let bx = b.x_at_y(self.current_y());

        Partial::from(approx_cmp(ax, bx))
            .or_else(|| {
                // if X and Y is equal, order by the top point's x
                let ax = a.lowest_y().x;
                let bx = b.lowest_y().x;
                approx_cmp(ax, bx)
            })
            .or_else(|| {
                // order by the bottom point's x
                let ax = a.highest_y().x;
                let bx = b.highest_y().x;
                approx_cmp(ax, bx)
            })
            .into()
    }

    /// Add an edge to the active sweep line.
    pub(super) fn add_edge(&mut self, edge: &BoEdge<Num>, all: &Edges<Num>) {
        tracing::trace!("Adding edge {} to active set", edge.id());

        let mut active = mem::take(&mut self.active);
        active.insert(edge, all, |edge, next| {
            let c = self.compare_edges(edge, next);
            matches!(c, Some(cmp::Ordering::Less | cmp::Ordering::Equal))
        });
        self.active = active;
    }

    /// Remove an edge from the active sweep line.
    pub(super) fn remove_edge(&mut self, edge: &BoEdge<Num>, all: &Edges<Num>) {
        tracing::trace!("Removing edge {} from active set", edge.id());

        self.active.remove(edge, all);

        // if the edge has a pending trapezoid, add it to the leftovers
        if edge.pending_trapezoid() {
            self.leftovers.push(edge, all);
        }
    }

    /// Swap an edge with the edge immediately after in the sweep line.
    pub(super) fn swap_edge(&mut self, edge: &BoEdge<Num>, all: &Edges<Num>) {
        self.active.swap(edge, all);
    }

    /// Iterate over the leftover items.
    pub(super) fn leftovers<'all>(
        &mut self,
        all: &'all Edges<Num>,
    ) -> impl FusedIterator<Item = &'all BoEdge<Num>> + 'all {
        self.leftovers.iter(all)
    }

    /// Remove an edge from the leftovers.
    pub(super) fn remove_leftover(&mut self, edge: &BoEdge<Num>, all: &Edges<Num>) {
        self.leftovers.remove(edge, all);
    }

    /// Take out the leftover items and iterate over them.
    pub(super) fn take_leftovers<'all>(
        &mut self,
        all: &'all Edges<Num>,
    ) -> impl FusedIterator<Item = &'all BoEdge<Num>> + 'all {
        mem::take(&mut self.leftovers).iter(all)
    }

    /// Try to complete trapezoids belonging to the active set
    /// of edges.
    pub(super) fn trapezoids<'all>(
        &self,
        fill_rule: FillRule,
        all: &'all Edges<Num>,
    ) -> impl FusedIterator<Item = Trapezoid<Num>> + 'all {
        let current_y = self.current_y;

        if cfg!(debug_assertions) {
            tracing::debug!(
                "Edges in active set: {:?}",
                self.active.iter(all).map(|e| e.id()).collect::<Vec<_>>()
            );
        }

        self.active.pairs(all).filter_map(move |current| {
            let (left, right) = current;
            tracing::debug!(
                "Creating trapezoid between {} and {}",
                left.id(),
                right.id()
            );
            left.start_trapezoid(right, current_y, all)
        })
    }
}

/// Partial comparison monad for the sweep line.
/// 
/// Makes chaining `PartialOrd` implementations easier.
#[derive(Copy, Clone)]
struct Partial {
    inner: Option<cmp::Ordering>,
}

impl From<Option<cmp::Ordering>> for Partial {
    fn from(inner: Option<cmp::Ordering>) -> Self {
        Partial { inner }
    }
}

impl From<Partial> for Option<cmp::Ordering> {
    fn from(partial: Partial) -> Self {
        partial.inner
    }
}

impl Partial {
    fn or_else<F: FnOnce() -> Option<cmp::Ordering>>(self, f: F) -> Self {
        match self.inner {
            Some(cmp::Ordering::Equal) => f().into(),
            o => o.into(),
        }
    }
}

/// Needed to fix certain shapes.
fn approx_cmp<Num: Scalar>(a: Num, b: Num) -> Option<cmp::Ordering> {
    if approx_eq(a, b) {
        Some(cmp::Ordering::Equal)
    } else {
        a.partial_cmp(&b)
    }
}