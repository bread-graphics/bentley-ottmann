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

//! Unit tests for functionality in the main module.

#![cfg(test)]

use super::*;
use alloc::vec;
use geometry::*;

const TEST_LINE: Line<f32> = Line {
    point: Point2D::new(0.0, 0.0),
    vector: Vector2D::new(1.0, 2.0),
};
const TEST_LINE_COLLINEAR: Line<f32> = Line {
    point: Point2D::new(-1.0, -2.0),
    vector: Vector2D::new(3.0, 6.0),
};
const TEST_LINE_NOT_COLLINEAR: Line<f32> = Line {
    point: Point2D::new(-1.0, -1.9),
    vector: Vector2D::new(3.0, 6.0),
};
const TEST_EDGE: Edge<f32> = Edge {
    line: TEST_LINE,
    top: 0.0,
    bottom: 2.0,
    direction: Direction::Forward,
};

fn make_test_bo_edge(edge: Line<f32>, id: NonZeroUsize) -> BoEdge<f32> {
    let swap_edges = edge.point.y > edge.point.y + edge.vector.y;

    let (p1, p2) = if swap_edges {
        (edge.point, edge.point + edge.vector)
    } else {
        (edge.point + edge.vector, edge.point)
    };

    BoEdge::from_edge(
        Edge {
            line: edge,
            top: p1.y,
            bottom: p2.y,
            direction: if swap_edges {
                Direction::Backwards
            } else {
                Direction::Forward
            },
        },
        id,
    )
}

#[test]
fn test_approx_eq() {
    assert!(approx_eq(0.0, 0.0));
    assert!(approx_eq(1.0, 1.0));
    assert!(approx_neq(0.0, 1.0));
}

#[test]
fn test_x_for_y() {
    let line = Line {
        point: Point2D::new(0.0, 0.0),
        vector: Vector2D::new(1.0, 2.0),
    };

    assert_eq!(x_for_y(&line, 0.0), 0.0);
    assert_eq!(x_for_y(&line, 2.0), 1.0);
    assert_eq!(x_for_y(&line, 4.0), 2.0);
    assert_eq!(x_for_y(&line, 0.5), 0.25);
}

#[test]
fn test_points_of_edge() {
    let edge = TEST_EDGE;

    let (p1, p2) = points_of_edge(&edge);
    assert_eq!(p1.x, 0.0);
    assert_eq!(p1.y, 0.0);
    assert_eq!(p2.x, 1.0);
    assert_eq!(p2.y, 2.0);
}

#[test]
fn test_collinear() {
    assert!(colinear(&TEST_LINE, &TEST_LINE_COLLINEAR));
    assert!(!colinear(&TEST_LINE, &TEST_LINE_NOT_COLLINEAR));
}
