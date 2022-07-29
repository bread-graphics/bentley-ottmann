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

//! Rust makes comparing objects (especially floats) hard
//! sometimes, so this module contains some wrapper structs
//! for use in sorting/comparing objects.

use core::cmp;

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
