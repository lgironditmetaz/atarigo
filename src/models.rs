//! Models used by the __atarigo__ crate.

use derive_new::new;

/// Represent a type of stone on a goban or no stone at all.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Stone {
    NoStone,
    Black,
    White,
}

impl Default for Stone {
    fn default() -> Self {
        Self::NoStone
    }
}

/// Represent a player in an atarigo game.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Player {
    Black,
    White,
}

impl std::fmt::Display for Player {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Player::Black => write!(f, "Black"),
            Player::White => write!(f, "White"),
        }
    }
}

/// A coordinate on the goban.
#[derive(Debug, PartialEq, Eq, Clone, new)]
pub struct Coordinate {
    /// The coordinate column on the goban (between _0_ and _width - 1_).
    pub i: usize,
    /// The coordinate row on the goban (between _0_ and _height - 1_).
    pub j: usize,
}

impl Coordinate {
    /// Checks the coordinate instance is within the limits of a given `size`.
    ///
    /// # Arguments
    ///
    /// * `size` - The size for which the coordinate should be valid.
    ///
    /// # Examples
    /// ```
    /// let c = atarigo::models::Coordinate::new(4, 5);
    /// let s = atarigo::models::Size::new(9, 9);
    ///
    /// assert!(c.is_valid_for_size(&s));
    /// ```
    pub fn is_valid_for_size(&self, size: &Size) -> bool {
        self.i < size.width && self.j < size.height
    }
}

/// Represent the size of a goban.
#[derive(Debug, PartialEq, Eq, Clone, new)]
pub struct Size {
    /// The width of a goban.
    pub width: usize,
    /// The height of a goban.
    pub height: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coordinate_can_check_validity_with_size() {
        assert!(Coordinate::new(0, 0).is_valid_for_size(&Size::new(9, 9)));
        assert!(Coordinate::new(4, 5).is_valid_for_size(&Size::new(9, 9)));
        assert!(Coordinate::new(8, 8).is_valid_for_size(&Size::new(9, 9)));

        assert!(Coordinate::new(9, 0).is_valid_for_size(&Size::new(9, 9)) == false);
        assert!(Coordinate::new(0, 9).is_valid_for_size(&Size::new(9, 9)) == false);
        assert!(Coordinate::new(100, 100).is_valid_for_size(&Size::new(9, 9)) == false);
    }
}
