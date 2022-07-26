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

use bentley_ottmann::trapezoids;
use fastrand::Rng;
use geometry::{Angle, Edge, Line, Point2D, Trapezoid, Vector2D, Polygon, Size2D, FillRule};
use image::{Rgba, RgbaImage};

fn main() {
    tracing_subscriber::fmt::init();

    // make an image
    let image_size = Size2D::new(640.0f32, 480.0);
    let center: Point2D<f32> = (image_size / 2.0).to_tuple().into();
    let image_size = image_size.to_u32();
    let mut img = RgbaImage::new(image_size.width, image_size.height);

    // generate a shape and then tesselate it
    let rng = Rng::new();
    let shape = generate_shape(center, &rng);
    let traps = trapezoids(shape, FillRule::Winding);

    for trap in traps {
        tracing::debug!("Yielded trapezoid: {:#?}", trap);
        draw_trapezoid(&mut img, Rgba([255, 0, 0, 255]), trap);
    }

    tracing::info!("Finished tesselating shape");

    // display the image in an SDL window
    imageproc::window::display_image("Rasterized Shape", &img, image_size.width, image_size.height);
}

/// Generate a random shape in the rough form of a circle.
fn generate_shape(center: Point2D<f32>, rng: &Rng) -> Polygon {
    //let mut last_point = None;
    let mut polygon = Polygon::default();

    /*for i in 0..60 {
        // generate a random point around cos(x), sin(x)
        let mut x = (i as f32).cos() * (center.x / 2.0);
        let mut y = (i as f32).sin() * (center.y / 2.0);
        x += center.x;
        y += center.y;
        let mut root = Point2D::new(x, y);

        // add random noise
        let noise_x = (center.x / 3.0) * (rng.f32() * 2.0 - 1.0);
        let noise_y = (center.y / 3.0) * (rng.f32() * 2.0 - 1.0);

        root.x += noise_x;
        root.y += noise_y;

        // figure out how we edit the polygon
        match &mut last_point {
            pt @ None => { *pt = Some(root); }
            Some(ref mut pt) => {
                // add the edge consisting of the current and last point,
                // then set the last point to the current point
                polygon.add_edge(*pt, root);
                *pt = root;
            }
        }
    }*/
    polygon.add_edge(Point2D::new(100.0, 100.0), Point2D::new(200.0, 100.0));
    polygon.add_edge(Point2D::new(200.0, 100.0), Point2D::new(200.0, 200.0));
    polygon.add_edge(Point2D::new(200.0, 200.0), Point2D::new(100.0, 200.0));
    polygon.add_edge(Point2D::new(100.0, 200.0), Point2D::new(100.0, 100.0));

    polygon
}

/// Draw a trapezoid to an image.
fn draw_trapezoid(image: &mut RgbaImage, color: Rgba<u8>, trap: Trapezoid<f32>) {
    // tell where we start
    let get_point_at = |i: f32| {
        let current_left = Point2D::new(trap.left.equation().solve_x_for_y(i).unwrap(), i);
        let current_right = Point2D::new(trap.right.equation().solve_x_for_y(i).unwrap(), i);
        (current_left, current_right)
    };

    let top = trap.top as usize;
    let bottom = trap.bottom as usize;

    for i in top..=bottom {
        let (left, right) = get_point_at(i as f32);
        imageproc::drawing::draw_line_segment_mut(
            image,
            (left.x, left.y),
            (right.x, right.y),
            color,
        );
    }
}
