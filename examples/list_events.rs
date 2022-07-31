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

use bentley_ottmann::bentley_ottmann_events;
use geometry::{Edge, Point2D};

fn main() {
    tracing_subscriber::fmt::init();

    let edges = vec![
        Edge::new(Point2D::new(0.0, 0.0), Point2D::new(1.0, 2.0)),
        Edge::new(Point2D::new(0.0, 2.0), Point2D::new(1.0, 0.0)),
    ];

    let events = bentley_ottmann_events(edges).collect::<Vec<_>>();
    println!("{:#?}", events);
}
