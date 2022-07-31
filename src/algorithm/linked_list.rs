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

use super::{BoEdge, Edges};
use core::{iter::FusedIterator, num::NonZeroUsize};

/// A linked list, based off of the `BoEdge` structure.
#[derive(Debug, Default)]
pub(super) struct LinkedList {
    /// The root of the linked list, or `None` if the
    /// list is empty.
    root: Option<NonZeroUsize>,
}

/// An iterator over the elements of a `LinkedList`.
pub(super) struct LinkedListIter<'all, Num> {
    /// The current node in the linked list.
    current: Option<NonZeroUsize>,
    /// The list of edges.
    edges: &'all Edges<Num>,
}

/// An iterator over pairs of elements in a `LinkedList`.
pub(super) struct LinkedListPairIter<'all, Num>(LinkedListIter<'all, Num>);

impl LinkedList {
    /// Get an iterator over this list.
    pub(super) fn iter<'all, Num>(&self, edges: &'all Edges<Num>) -> LinkedListIter<'all, Num> {
        LinkedListIter {
            current: self.root,
            edges,
        }
    }

    /// Iterate over this list in pairs.
    pub(super) fn pairs<'all, Num>(
        &self,
        edges: &'all Edges<Num>,
    ) -> LinkedListPairIter<'all, Num> {
        LinkedListPairIter(self.iter(edges))
    }

    /// Push a `BoEdge` to the end of the linked list.
    pub(super) fn push<'all, Num: Copy>(&mut self, edge: &BoEdge<Num>, all: &'all Edges<Num>) {
        match &mut self.root {
            root @ None => {
                *root = Some(edge.id());
                edge.set_prev(None);
            }
            Some(_) => {
                // find the last node and add to it
                let node = self.iter(all).last().unwrap();
                node.set_next(Some(edge.id()));
                edge.set_prev(Some(node.id()));
            }
        }

        // TODO: unnecessary precaution?
        edge.set_next(None);
    }

    /// Insert an edge into this linked list.
    ///
    /// The closure should return `true` if the edge should be inserted
    /// before the given element.
    pub(super) fn insert<'all, Num: Copy>(
        &mut self,
        edge: &BoEdge<Num>,
        all: &'all Edges<Num>,
        mut before: impl FnMut(&BoEdge<Num>, &BoEdge<Num>) -> bool,
    ) {
        // find the node to insert this edge before
        let node = match self.iter(all).find(|n| before(edge, n)) {
            Some(node) => node,
            None => {
                // insert at the end
                self.push(edge, all);
                return;
            }
        };

        // insert into the linked list
        let prev = node.prev();
        if let Some(prev) = prev {
            all.get(prev).set_next(Some(edge.id()));
        } else {
            self.root = Some(edge.id());
        }
        edge.set_prev(prev);
        edge.set_next(Some(node.id()));
        node.set_prev(Some(edge.id()));
    }

    /// Remove an edge from this linked list.
    pub(super) fn remove<'all, Num: Copy>(&mut self, edge: &BoEdge<Num>, all: &'all Edges<Num>) {
        let prev = edge.prev();
        let next = edge.next();

        if let Some(prev) = prev {
            all.get(prev).set_next(next);
        } else {
            self.root = next;
        }

        if let Some(next) = next {
            all.get(next).set_prev(prev);
        }

        edge.set_next(None);
        edge.set_prev(None);
    }

    /// Swap an edge with the next edge in the linked list.
    ///
    /// # Panics
    ///
    /// Panics if the edge is the last element in the linked list.
    pub(super) fn swap<'all, Num: Copy>(&mut self, edge: &BoEdge<Num>, all: &'all Edges<Num>) {
        let next = all.get(match edge.next() {
            Some(next) => next,
            None => {
                tracing::error!("edge should never be the removed from the list");
                return;
            }
        });
        let prev = edge.prev();
        let next_next = next.next();

        if let Some(prev) = prev {
            all.get(prev).set_next(Some(next.id()));
        } else {
            self.root = Some(next.id());
        }

        if let Some(next_next) = next_next {
            all.get(next_next).set_prev(Some(edge.id()));
        }

        edge.set_next(next_next);
        edge.set_prev(Some(next.id()));
        next.set_prev(prev);
        next.set_next(Some(edge.id()));
    }
}

impl<'all, Num: Copy> Iterator for LinkedListIter<'all, Num> {
    type Item = &'all BoEdge<Num>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.map(|current| {
            let edge = self.edges.get(current);
            self.current = edge.next();
            edge
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // we have at least one element if current is Some
        (self.current.is_some() as usize, None)
    }
}

impl<'all, Num: Copy> FusedIterator for LinkedListIter<'all, Num> {}

impl<'all, Num: Copy> Iterator for LinkedListPairIter<'all, Num> {
    type Item = (&'all BoEdge<Num>, &'all BoEdge<Num>);

    fn next(&mut self) -> Option<Self::Item> {
        let e1 = self.0.next()?;
        let e2 = self.0.next()?;
        Some((e1, e2))
    }
}

impl<'all, Num: Copy> FusedIterator for LinkedListPairIter<'all, Num> {}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{vec, vec::Vec};
    use core::num::NonZeroUsize;
    use geometry::Point2D;

    macro_rules! nzu {
        ($x:expr) => {{
            NonZeroUsize::new($x).unwrap()
        }};
    }

    fn testing_edges() -> Vec<BoEdge<f32>> {
        vec![
            BoEdge::from_points(Point2D::new(1.0, 0.0), Point2D::new(1.0, 1.0), nzu!(1)),
            BoEdge::from_points(Point2D::new(2.0, 0.0), Point2D::new(1.0, 1.0), nzu!(2)),
            BoEdge::from_points(Point2D::new(3.0, 1.0), Point2D::new(0.0, 2.0), nzu!(3)),
            BoEdge::from_points(Point2D::new(4.0, 1.0), Point2D::new(0.0, 2.0), nzu!(4)),
        ]
    }

    fn assert_ids_eq(left: Option<&BoEdge<f32>>, right: Option<&BoEdge<f32>>) {
        assert_eq!(left.map(|l| l.id()), right.map(|r| r.id()))
    }

    #[test]
    fn linked_list() {
        let edges: Edges<f32> = testing_edges().into();
        let mut linked_list = LinkedList::default();

        // push to the linked list
        for edge in &edges {
            linked_list.push(edge, &edges);
        }

        let mut iter = linked_list.iter(&edges);
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(1))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(2))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(3))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(4))));
        assert_ids_eq(iter.next(), None);
    }

    #[test]
    fn sorted_linked_list() {
        let edges: Edges<f32> = testing_edges().into();
        let mut linked_list = LinkedList::default();

        // push to the linked list, but sort in reverse by the first X
        // coordinate of the edge's start point
        for edge in &edges {
            linked_list.insert(edge, &edges, |edge, next| {
                edge.lowest_y().x >= next.lowest_y().x
            });
        }

        let mut iter = linked_list.iter(&edges);
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(4))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(3))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(2))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(1))));
        assert_ids_eq(iter.next(), None);

        // remove the element with id 3 from the list
        linked_list.remove(edges.get(nzu!(3)), &edges);

        let mut iter = linked_list.iter(&edges);
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(4))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(2))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(1))));
        assert_ids_eq(iter.next(), None);

        // swap the elements at indices 4 and 2
        linked_list.swap(edges.get(nzu!(4)), &edges);

        let mut iter = linked_list.iter(&edges);
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(2))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(4))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(1))));

        // swap the elements at indices 4 and 1
        linked_list.swap(edges.get(nzu!(4)), &edges);
        let mut iter = linked_list.iter(&edges);
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(2))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(1))));
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(4))));
        assert_ids_eq(iter.next(), None);

        // remove the elements at indices 2 and 4
        linked_list.remove(edges.get(nzu!(2)), &edges);
        linked_list.remove(edges.get(nzu!(4)), &edges);
        let mut iter = linked_list.iter(&edges);
        assert_ids_eq(iter.next(), Some(edges.get(nzu!(1))));
        assert_ids_eq(iter.next(), None);
    }
}
