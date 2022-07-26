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
use geometry::{FillRule, Path, PathBuffer, Point2D, Polygon, Size2D, Trapezoid, Vector2D};
use image::{Rgba, RgbaImage};
use std::env;

const COLORS: &[Rgba<u8>] = &[
    Rgba([255, 0, 0, 255]),
    Rgba([0, 255, 0, 255]),
    Rgba([0, 0, 255, 255]),
    Rgba([255, 255, 0, 255]),
    Rgba([255, 0, 255, 255]),
    Rgba([0, 255, 255, 255]),
    Rgba([0, 0, 0, 255]),
];

fn main() {
    tracing_subscriber::fmt::init();

    // make an image
    let image_size = Size2D::new(640.0f32, 480.0);
    let center: Point2D<f32> = (image_size / 2.0).to_tuple().into();
    let image_size = image_size.to_u32();
    let mut img = RgbaImage::new(image_size.width, image_size.height);

    // generate a shape and then tesselate it
    let variation = env::args_os()
        .nth(1)
        .and_then(|a| a.to_str().map(|s| s.to_string()));
    let shape = if variation.as_deref() == Some("rect") {
        generate_rectangle(center)
    } else if variation.as_deref() == Some("triangle") {
        generate_triangle(center)
    } else if variation.as_deref() == Some("t") {
        generate_t()
    } else if variation.as_deref() == Some("x") {
        generate_x()
    } else if variation.as_deref() == Some("o") {
        generate_shape(center, true)
    } else {
        generate_shape(center, false)
    };
    let traps = trapezoids(shape, FillRule::Winding);

    for (i, trap) in traps.enumerate() {
        // select a color
        let color = COLORS[i % COLORS.len()];

        tracing::debug!("Yielded trapezoid #{}: {:#?}", i, trap);
        draw_trapezoid(&mut img, color, trap);
    }

    tracing::info!("Finished tesselating shape");

    // display the image in an SDL window
    imageproc::window::display_image(
        "Rasterized Shape",
        &img,
        image_size.width,
        image_size.height,
    );
}

/// Generate a polygon consisting of a simple rectangle.
fn generate_rectangle(center: Point2D<f32>) -> Polygon {
    let size = Size2D::new(100.0, 100.0);
    let origin = center;
    let p1 = origin + Vector2D::new(size.width, 0.0);
    let p2 = origin + Vector2D::new(0.0, size.height);
    let p3 = origin + Vector2D::new(size.width, size.height);

    let mut polygon = Polygon::default();
    polygon.add_edge(origin, p1);
    polygon.add_edge(p1, p3);
    polygon.add_edge(p3, p2);
    polygon.add_edge(p2, origin);
    polygon
}

/// Generate a polygon consisting of a "T".
fn generate_t() -> Polygon {
    let p1 = Point2D::new(100.0, 100.0);
    let p2 = Point2D::new(300.0, 100.0);
    let p3 = Point2D::new(300.0, 200.0);
    let p4 = Point2D::new(250.0, 200.0);
    let p5 = Point2D::new(250.0, 300.0);
    let p6 = Point2D::new(150.0, 300.0);
    let p7 = Point2D::new(150.0, 200.0);
    let p8 = Point2D::new(100.0, 200.0);

    let mut polygon = Polygon::default();
    polygon.add_edge(p1, p2);
    polygon.add_edge(p2, p3);
    polygon.add_edge(p3, p4);
    polygon.add_edge(p4, p5);
    polygon.add_edge(p5, p6);
    polygon.add_edge(p6, p7);
    polygon.add_edge(p7, p8);
    polygon.add_edge(p8, p1);
    polygon
}

/// Generate a polygon consisting of a simple triangle.
fn generate_triangle(center: Point2D<f32>) -> Polygon {
    let size = Size2D::new(100.0, 100.0);
    let origin = center;
    let p1 = origin + Vector2D::new(size.width, size.height);
    let p2 = origin + Vector2D::new(-size.width, size.height);

    let mut polygon = Polygon::default();
    polygon.add_edge(origin, p1);
    polygon.add_edge(p1, p2);
    polygon.add_edge(p2, origin);
    polygon
}

/// Generate a large red "X".
fn generate_x() -> Polygon {
    let mut builder = Path::builder();
    builder.begin(Point2D::new(100.0, 100.0));
    builder.line_to(Point2D::new(120.0, 80.0));
    builder.line_to(Point2D::new(200.0, 150.0));
    builder.line_to(Point2D::new(280.0, 80.0));
    builder.line_to(Point2D::new(300.0, 100.0));
    builder.line_to(Point2D::new(220.0, 170.0));
    builder.line_to(Point2D::new(300.0, 240.0));
    builder.line_to(Point2D::new(280.0, 260.0));
    builder.line_to(Point2D::new(200.0, 190.0));
    builder.line_to(Point2D::new(120.0, 260.0));
    builder.line_to(Point2D::new(100.0, 240.0));
    builder.line_to(Point2D::new(180.0, 170.0));
    builder.line_to(Point2D::new(100.0, 100.0));
    builder.end(true);
    builder.build().into()
}

/// Generate a circle
fn generate_shape(center: Point2D<f32>, inside: bool) -> Polygon {
    const MAX_SIDES: usize = 60;

    let mut circle = PathBuffer::default();
    let mut add_circle = |radius: f32| {
        let mut builder = circle.builder();

        let mut started = false;

        for i in 0..MAX_SIDES {
            let angle = (i as f32 / MAX_SIDES as f32) * 2.0 * std::f32::consts::PI;

            // generate a random point around cos(x), sin(x)
            let mut x = angle.cos() * (center.x / radius);
            let mut y = angle.sin() * (center.y / radius);
            x += center.x;
            y += center.y;
            let root = Point2D::new(x, y);

            if !started {
                builder.begin(root);
                started = true;
            } else {
                builder.line_to(root);
            }
        }

        builder.end(true);
        builder.build();
    };

    add_circle(2.0);
    if inside {
        add_circle(4.0);
    }
    circle.into()
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
