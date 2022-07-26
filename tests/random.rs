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

use bentley_ottmann::bentley_ottmann;
use fastrand::Rng;
use geometry::{Edge, Line, Point2D, Vector2D};
use std::iter;

#[test]
fn random_lines() {
    let rng = Rng::new();
    let random_lines = iter::repeat_with(|| make_random_line(&rng))
        .take(500)
        .collect::<Vec<_>>();

    // use the brute force method to generate the list of intersections
    let mut intersections = vec![];
    for (i, line1) in random_lines.iter().enumerate() {
        for (j, line2) in random_lines.iter().enumerate() {
            if i != j {
                let intersection = line1.intersection(line2);
                if let Some(intersection) = intersection {
                    intersections.push(intersection);
                }
            }
        }
    }

    // use the Bentley-Ottmann algorithm to generate the list of intersections
    bentley_ottmann(random_lines).for_each(|intersect| {
        if intersections.contains(&intersect) {
            intersections.retain(|&x| x != intersect);
        } else {
            panic!(
                "Intersection produce by B.O not found in brute force list: {:?}",
                intersect
            );
        }
    });
}

fn make_random_line(rng: &Rng) -> Edge<f32> {
    let x = gen_f32(rng, -10.0, 10.0);
    let y = gen_f32(rng, -10.0, 10.0);
    let dx = gen_f32_non_zero(rng, -10.0, 10.0);
    let dy = gen_f32_non_zero(rng, -10.0, 10.0);

    let line = Line {
        point: Point2D::new(x, y),
        vector: Vector2D::new(dx, dy),
    };

    let (top, bottom) = if dy < 0.0 { (y, y + dy) } else { (y + dy, y) };

    Edge {
        line,
        top,
        bottom,
        direction: geometry::Direction::Forward,
    }
}

fn gen_f32_non_zero(rng: &Rng, min: f32, max: f32) -> f32 {
    let mut value = gen_f32(rng, min, max);
    while value == 0.0 {
        value = gen_f32(rng, min, max);
    }
    value
}

fn gen_f32(rng: &Rng, min: f32, max: f32) -> f32 {
    let rand = rng.f32();
    min + ((max - min) * rand)
}
