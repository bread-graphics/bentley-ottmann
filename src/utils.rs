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

//! Various utility functions.

use geometry::{Point2D, Scalar};

/// Are two points approximately equal?
pub fn approx_eq_point<Num: Scalar>(a: Point2D<Num>, b: Point2D<Num>) -> bool {
    approx_eq(a.x, b.x) && approx_eq(a.y, b.y)
}

/// Are two values approximately equal to eachother?
pub(crate) fn approx_eq<Num: Scalar>(a: Num, b: Num) -> bool {
    (a - b).abs() < Num::EPSILON
}

/// Are two values not approximately equal to eachother?
pub(crate) fn approx_neq<Num: Scalar>(a: Num, b: Num) -> bool {
    !approx_eq(a, b)
}
