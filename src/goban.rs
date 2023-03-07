//! Variable size goban implementation that can be used to group stones
//! and compute their liberties.

use std::collections::HashMap;

use crate::{
    array_2d::Array2d,
    models::{Coordinate, Size, Stone},
};

/// Represents a Goban size & content.
#[derive(Debug)]
pub struct Goban {
    stones: Array2d<Stone>,
}

impl Goban {
    /// Returns a `Goban` filled with no stones.
    ///
    /// # Arguments
    ///
    /// * `size` - The size of the `Goban`.
    pub fn new(size: Size) -> Self {
        Self {
            stones: Array2d::new(size),
        }
    }

    /// Returns the size of the `Goban` instance.
    pub fn size(&self) -> &Size {
        self.stones.size()
    }

    /// Returns the stone at a given coordinate.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The stone's coordinate.
    pub fn stone(&self, coordinate: &Coordinate) -> Stone {
        self.stones.value(coordinate)
    }

    /// Sets the stone at a given coordinate.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The stone's coordinate.
    /// * `stone` - The stone to be inserted (can be `Stone::NoStone` to remove the stone).
    pub fn set_stone(&mut self, coordinate: &Coordinate, stone: Stone) {
        self.stones.set_value(coordinate, stone)
    }

    /// Returns a mask of adjacent stones (aka groups).
    ///
    /// For instance the following `Goban`:
    ///
    /// ```text
    /// ● ● . . .
    /// . . ◯ . .
    /// . . ◯ ◯ .
    /// . . ◯ . ●
    /// ● . . . .
    /// ```
    ///
    /// will produce the following `Goban`:
    ///
    /// ```text
    /// 1 1 0 0 0
    /// 0 0 2 0 0
    /// 0 0 2 2 0
    /// 0 0 2 0 3
    /// 4 0 0 0 0
    /// ```
    pub fn group_mask(&self) -> Array2d<i32> {
        self.stones.adjacent_value_mask()
    }

    /// Returns the stone corresponding to a given group mask.
    ///
    /// # Arguments:
    ///
    /// * `group_index` - A valid group mask index.
    ///
    /// # Returns:
    ///
    /// The stone corresponding the the group mask index provided as argument if any, None otherwise.
    ///
    /// # Note:
    ///
    /// This method will always uses the most up to date group mask index, so you should
    /// always provide a group index computed on an up to date group mask index as well.
    pub fn stone_by_group_index(&self, group_index: i32) -> Option<Stone> {
        self.stones.value_by_mask_index(group_index)
    }

    /// Removes a group of stones by group mask index.
    ///
    /// # Arguments:
    ///
    /// * `group_index` - A valid group mask index.
    /// * `group_mask` - An optional group mask that can be provided in order to
    ///                  delete several groups without index changes.
    ///
    /// # Note:
    ///
    /// If the group mask index is invalid, no stone will be removed.
    pub fn remove_group(&mut self, group_index: i32, group_mask: Option<&Array2d<i32>>) {
        let computed_group_mask = self.group_mask();
        let group_mask = match group_mask {
            Some(group_mask) => group_mask,
            None => &computed_group_mask,
        };

        (0..self.size().height).for_each(|j| {
            (0..self.size().width).for_each(|i| {
                let coordinate = Coordinate::new(i, j);
                if group_mask.value(&coordinate) == group_index {
                    self.set_stone(&coordinate, Stone::NoStone);
                }
            })
        });
    }

    /// Computes the remaining liberties for all groups of the `Goban`.
    ///
    /// # Returns:
    ///
    /// An `HashMap<i32, usize>` containing all liberty count indexed by
    /// the group index for the current group mask.
    pub fn group_liberties(&self) -> HashMap<i32, usize> {
        let mut group_liberties = HashMap::new();
        let group_mask = self.group_mask();

        (0..self.size().height).for_each(|j| {
            (0..self.size().width).for_each(|i| {
                if Stone::NoStone == self.stone(&Coordinate::new(i, j)) {
                    // If there is no stone, we can add liberties for all adjacent group but one group should
                    // only receive one liberties from this intersection even with several stones are
                    // adjacent.
                    let (_, left, right, top, bottom) =
                        group_mask.adjacent_values(&Coordinate::new(i, j));

                    let left_group_index = left.unwrap_or_default();
                    let right_group_index = right.unwrap_or_default();
                    let top_group_index = top.unwrap_or_default();
                    let bottom_group_index = bottom.unwrap_or_default();

                    if left_group_index != 0 {
                        *group_liberties.entry(left_group_index).or_insert(0) += 1;
                    }
                    if right_group_index != 0 && left_group_index != right_group_index {
                        *group_liberties.entry(right_group_index).or_insert(0) += 1;
                    }
                    if top_group_index != 0
                        && left_group_index != top_group_index
                        && right_group_index != top_group_index
                    {
                        *group_liberties.entry(top_group_index).or_insert(0) += 1;
                    }
                    if bottom_group_index != 0
                        && left_group_index != bottom_group_index
                        && right_group_index != bottom_group_index
                        && top_group_index != bottom_group_index
                    {
                        *group_liberties.entry(bottom_group_index).or_insert(0) += 1;
                    }
                } else {
                    // We must add to the dictionary all groups that have no liberties… otherwise
                    // dead groups will not appear at all in it.
                    let group_index = group_mask.value(&Coordinate::new(i, j));
                    group_liberties.entry(group_index).or_insert(0);
                }
            });
        });

        group_liberties
    }
}

impl Default for Goban {
    fn default() -> Self {
        Self::new(Size {
            width: 9,
            height: 9,
        })
    }
}

impl std::fmt::Display for Goban {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut desc = format!(
            "Size: width: {} / height: {}\n\r",
            self.size().width,
            self.size().height
        );

        (0..self.size().height).for_each(|j| {
            (0..self.size().width).for_each(|i| match self.stone(&Coordinate::new(i, j)) {
                Stone::NoStone => desc.push_str(". "),
                Stone::Black => desc.push_str("● "),
                Stone::White => desc.push_str("◯ "),
            });
            desc.push_str("\n\r");
        });

        write!(f, "{}", desc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_create_empty_goban_from_the_right_size() {
        let g = Goban::new(Size::new(2, 3));
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 2)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 2)), Stone::NoStone);
    }

    #[test]
    fn default_creates_a_9_by_9_goban() {
        let g = Goban::default();
        assert_eq!(g.size(), &Size::new(9, 9));
    }

    #[test]
    fn stones_can_be_set_and_retrieved() {
        let mut g = Goban::new(Size::new(3, 2));
        g.set_stone(&Coordinate::new(1, 1), Stone::Black);
        g.set_stone(&Coordinate::new(2, 1), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::White);
    }

    #[test]
    fn setting_stones_outside_coordinates_is_ignored() {
        let mut g = Goban::new(Size::new(2, 2));
        g.set_stone(&Coordinate::new(2, 1), Stone::Black);
        g.set_stone(&Coordinate::new(1, 2), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::NoStone);
    }

    #[test]
    fn reading_stones_outside_coordinates_returns_no_stone() {
        let mut g = Goban::new(Size::new(2, 2));
        g.set_stone(&Coordinate::new(0, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 0), Stone::Black);
        g.set_stone(&Coordinate::new(0, 1), Stone::White);
        g.set_stone(&Coordinate::new(1, 1), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 2)), Stone::NoStone);
    }

    #[test]
    fn retrieving_stone_from_mask_index() {
        let mut g = Goban::new(Size::new(3, 3));
        g.set_stone(&Coordinate::new(0, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 1), Stone::Black);
        g.set_stone(&Coordinate::new(2, 0), Stone::White);
        g.set_stone(&Coordinate::new(2, 1), Stone::White);
        g.set_stone(&Coordinate::new(2, 2), Stone::White);

        assert_eq!(g.stone_by_group_index(0), Some(Stone::NoStone));
        assert_eq!(g.stone_by_group_index(1), Some(Stone::Black));
        assert_eq!(g.stone_by_group_index(2), Some(Stone::White));
        assert_eq!(g.stone_by_group_index(99), None);
    }

    #[test]
    fn removing_group_from_mask_index() {
        let mut g = Goban::new(Size::new(3, 3));
        g.set_stone(&Coordinate::new(0, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 1), Stone::Black);
        g.set_stone(&Coordinate::new(2, 0), Stone::White);
        g.set_stone(&Coordinate::new(2, 1), Stone::White);
        g.set_stone(&Coordinate::new(2, 2), Stone::White);

        g.remove_group(2, None); // removing the group '2', aka the white vertical group
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(2, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(2, 2)), Stone::NoStone);
    }

    #[test]
    fn removing_group_from_mask_index_with_precomputed_mask() {
        let mut g = Goban::new(Size::new(3, 3));
        g.set_stone(&Coordinate::new(0, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 1), Stone::Black);
        g.set_stone(&Coordinate::new(2, 0), Stone::White);
        g.set_stone(&Coordinate::new(2, 1), Stone::White);
        g.set_stone(&Coordinate::new(2, 2), Stone::White);

        g.remove_group(2, Some(&g.group_mask())); // removing the group '2', aka the white vertical group
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(2, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(2, 2)), Stone::NoStone);
    }

    #[test]
    fn group_liberties_is_computed_properly_1() {
        // Computing liberties for the following goban:
        // ● ● . ◯
        // . ● . ◯
        // ● . . ◯
        let mut g = Goban::new(Size::new(4, 3));
        g.set_stone(&Coordinate::new(0, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 1), Stone::Black);
        g.set_stone(&Coordinate::new(0, 2), Stone::Black);
        g.set_stone(&Coordinate::new(3, 0), Stone::White);
        g.set_stone(&Coordinate::new(3, 1), Stone::White);
        g.set_stone(&Coordinate::new(3, 2), Stone::White);

        let liberties = g.group_liberties();
        assert_eq!(liberties.get(&1).unwrap(), &4usize);
        assert_eq!(liberties.get(&2).unwrap(), &3usize);
        assert_eq!(liberties.get(&3).unwrap(), &2usize);
    }

    #[test]
    fn group_liberties_is_computed_properly_2() {
        // Computing liberties for the following goban:
        // . . . .
        // . ● ◯ .
        // . ◯ ● .
        // . . . .
        let mut g = Goban::new(Size::new(4, 4));
        g.set_stone(&Coordinate::new(1, 1), Stone::Black);
        g.set_stone(&Coordinate::new(2, 2), Stone::Black);
        g.set_stone(&Coordinate::new(1, 2), Stone::White);
        g.set_stone(&Coordinate::new(2, 1), Stone::White);

        let liberties = g.group_liberties();
        assert_eq!(liberties.get(&1).unwrap(), &2usize);
        assert_eq!(liberties.get(&2).unwrap(), &2usize);
        assert_eq!(liberties.get(&3).unwrap(), &2usize);
        assert_eq!(liberties.get(&4).unwrap(), &2usize);
    }

    #[test]
    fn group_liberties_is_computed_properly_3() {
        // Computing liberties for a more complex goban including some groups without liberties:
        // ◯ ● . .
        // ● ● ◯ .
        // . ◯ ● ◯
        // . . ◯ .
        // This group will yield the following group mask:
        // 1 2 0 0
        // 2 2 4 0
        // 0 5 6 7
        // 0 0 8 0

        // TODO adjacent groups with some groups without liberties
        let mut g = Goban::new(Size::new(4, 4));
        g.set_stone(&Coordinate::new(0, 1), Stone::Black);
        g.set_stone(&Coordinate::new(1, 0), Stone::Black);
        g.set_stone(&Coordinate::new(1, 1), Stone::Black);
        g.set_stone(&Coordinate::new(2, 2), Stone::Black);
        g.set_stone(&Coordinate::new(0, 0), Stone::White);
        g.set_stone(&Coordinate::new(1, 2), Stone::White);
        g.set_stone(&Coordinate::new(2, 1), Stone::White);
        g.set_stone(&Coordinate::new(3, 2), Stone::White);
        g.set_stone(&Coordinate::new(2, 3), Stone::White);

        let liberties = g.group_liberties();
        assert_eq!(liberties.get(&1).unwrap(), &0usize);
        assert_eq!(liberties.get(&2).unwrap(), &2usize);
        assert_eq!(liberties.get(&3), None);
        assert_eq!(liberties.get(&4).unwrap(), &2usize);
        assert_eq!(liberties.get(&5).unwrap(), &2usize);
        assert_eq!(liberties.get(&6).unwrap(), &0usize);
        assert_eq!(liberties.get(&7).unwrap(), &2usize);
        assert_eq!(liberties.get(&8).unwrap(), &2usize);
    }
}
