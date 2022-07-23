// BSL 1.0 License

//! Rust makes comparing objects (especially floats) hard
//! sometimes, so this module contains some wrapper structs
//! for use in sorting/comparing objects.

use core::cmp;
use geometry::{Line, Point2D, Scalar, Slope};

/// Wraps an object that implements `PartialOrd` and `PartialEq`,
/// then makes it `Eq` and `Ord`.
///
/// This asserts that none of the involves objects are `NaN` or the like.
#[derive(Debug, Copy, Clone, Default, PartialEq, PartialOrd)]
pub(crate) struct AbsoluteEq<T>(pub(crate) T);

impl<T: PartialEq> Eq for AbsoluteEq<T> {}
#[allow(clippy::derive_ord_xor_partial_ord)]
impl<T: PartialOrd> Ord for AbsoluteEq<T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.0
            .partial_cmp(&other.0)
            .expect("Expected non-NaN values")
    }
}

/// Compare two `Line`s at a given Y coordinate.
pub(crate) fn compare_lines_at_x<Num: Scalar>(
    line1: Line<Num>,
    line2: Line<Num>,
    y: Num,
) -> Option<cmp::Ordering> {
    if line1.point == line2.point && line1.vector == line2.vector {
        return Some(cmp::Ordering::Equal);
    }

    let x1 = line1.equation().solve_x_for_y(y);
    let x2 = line2.equation().solve_x_for_y(y);

    match (x1, x2) {
        (Some(x1), Some(x2)) => match x1.partial_cmp(&x2) {
            Some(cmp::Ordering::Equal) => {}
            x => return x,
        },
        _ => return None,
    }

    // we now should compare slopes
    let sl1 = Slope::from_line(line1);
    let sl2 = Slope::from_line(line2);
    sl1.partial_cmp(&sl2)
}

/// Order a point by X and then Y.
pub(crate) fn order_points<Num: Scalar>(
    p1: Point2D<Num>,
    p2: Point2D<Num>,
) -> (Point2D<Num>, Point2D<Num>) {
    if p1.x < p2.x || (p1.x == p2.x && p1.y < p2.y) {
        (p1, p2)
    } else {
        (p2, p1)
    }
}
