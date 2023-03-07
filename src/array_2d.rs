//! Variable size 2d generic array that can be used to easily model a _Goban_.

use std::fmt::Display;

use super::models::{Coordinate, Size};

/// Represents the array size & content.
#[derive(Debug)]
pub struct Array2d<T> {
    size: Size,
    array: Vec<Vec<T>>,
}

impl<T: Default + Clone> Array2d<T> {
    /// Returns a new `Array2d` filled with default values.
    ///
    /// # Arguments
    ///
    /// * `size` - The size of the `Array2d`.
    pub fn new(size: Size) -> Self {
        Self {
            array: Array2d::empty_array(&size),
            size,
        }
    }

    /// Returns an `Vec<Vec<T>>` initialized with default values.
    ///
    /// # Arguments
    ///
    /// * `size` - The size of the `Vec<Vec<T>>`.
    fn empty_array(size: &Size) -> Vec<Vec<T>> {
        (0..size.height)
            .map(|_| (0..size.width).map(|_| T::default()).collect())
            .collect()
    }

    /// Returns the size of the `Array2d` instance.
    pub fn size(&self) -> &Size {
        &self.size
    }

    /// Returns the value of a given coordinate.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The coordinate from which to extract the value.
    pub fn value(&self, coordinate: &Coordinate) -> T {
        if coordinate.is_valid_for_size(&self.size) {
            self.array[coordinate.j][coordinate.i].clone()
        } else {
            T::default()
        }
    }

    /// Sets the value from a given coordinate.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The coordinate in which the value will be set.
    /// * `value` - The value to be inserted.
    pub fn set_value(&mut self, coordinate: &Coordinate, value: T) {
        if coordinate.is_valid_for_size(&self.size) {
            self.array[coordinate.j][coordinate.i] = value;
        }
    }

    /// Returns the value from a given coordinate and all the values
    /// directly adjacent to the coordinate.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The coordinate from which to extract the value.
    ///
    /// # Returns
    ///
    /// A tuple that contains:
    ///
    /// * the value for the coordinate provided as arguments,
    /// * the value to the left of the coordinate if any, None otherwise,
    /// * the value to the right of the coordinate if any, None otherwise,
    /// * the value to the top of the coordinate if any, None otherwise,
    /// * the value to the bottom of the coordinate if any, None otherwise,
    pub fn adjacent_values(
        &self,
        coordinate: &Coordinate,
    ) -> (T, Option<T>, Option<T>, Option<T>, Option<T>) {
        let value = self.value(coordinate);
        let left_value = if coordinate.i > 0 {
            Some(self.value(&Coordinate::new(coordinate.i - 1, coordinate.j)))
        } else {
            None
        };
        let right_value = if coordinate.i + 1 < self.size().width {
            Some(self.value(&Coordinate::new(coordinate.i + 1, coordinate.j)))
        } else {
            None
        };
        let top_value = if coordinate.j > 0 {
            Some(self.value(&Coordinate::new(coordinate.i, coordinate.j - 1)))
        } else {
            None
        };
        let bottom_value: Option<T> = if coordinate.j + 1 < self.size().height {
            Some(self.value(&Coordinate::new(coordinate.i, coordinate.j + 1)))
        } else {
            None
        };

        (value, left_value, right_value, top_value, bottom_value)
    }
}

impl<T: Default + Clone + PartialEq> Array2d<T> {
    /// Returns the value corresponding to a given mask index.
    ///
    /// # Arguments:
    ///
    /// * `mask_index` - A valid mask index.
    ///
    /// # Returns:
    ///
    /// The value corresponding the the mask index provided as argument if any, None otherwise.
    ///
    /// # Note:
    ///
    /// This method will always uses the most up to date values mask, so you should
    /// always provide an index computed on an up to date values mask as well.
    pub fn value_by_mask_index(&self, mask_index: i32) -> Option<T> {
        let value_mask = self.adjacent_value_mask();
        let mut value_coordinate: Option<Coordinate> = None;

        (0..self.size().height).for_each(|j| {
            (0..self.size().width).for_each(|i| {
                if value_mask.value(&Coordinate::new(i, j)) == mask_index {
                    value_coordinate = Some(Coordinate::new(i, j));
                }
            });
        });

        value_coordinate.map(|coordinate| self.value(&coordinate))
    }

    /// Returns a mask of adjacent values.
    ///
    /// A value mask is an `Array2d<i32>` which attributes a index for all identical non default
    /// values that are adjacent in the original instance of `Array2d`.
    ///
    /// For instance the following array:
    ///
    /// ```text
    /// a a . . .
    /// . . b . .
    /// . . b b .
    /// . . b . c
    /// c . . . .
    /// ```
    ///
    /// will produce the following mask:
    ///
    /// ```text
    /// 1 1 0 0 0
    /// 0 0 2 0 0
    /// 0 0 2 2 0
    /// 0 0 2 0 3
    /// 4 0 0 0 0
    /// ```
    ///
    /// A value mask can be useful to find groups of `Stones` when the `Array2d` is used to
    /// implement the `Goban` type.
    pub fn adjacent_value_mask(&self) -> Array2d<i32> {
        let mut adjacent_value_mask: Array2d<i32> = Array2d::new(self.size().clone());
        let mut clash_indexes: Vec<(i32, i32)> = Vec::new();
        let mut current_index = 0;

        (0..self.size().height).for_each(|j| {
            (0..self.size().width).for_each(|i| {
                // On each cell…
                let coordinate = Coordinate::new(i, j);
                let (current_value, left_value, _, top_value, _) =
                    self.adjacent_values(&coordinate);

                // Mask value update occurs only if the current value is not default, otherwise
                // the mask value should always be 0!
                if current_value != T::default() {
                    // Retrieving the current mask values of adjacent cells if they exists and
                    // if they have the same value.
                    let left_mask_value = match left_value {
                        Some(v) if v == current_value => adjacent_value_mask
                            .value(&Coordinate::new(coordinate.i - 1, coordinate.j))
                            .to_owned(),
                        _ => 0,
                    };
                    let top_mask_value = match top_value {
                        Some(v) if v == current_value => adjacent_value_mask
                            .value(&Coordinate::new(coordinate.i, coordinate.j - 1))
                            .to_owned(),
                        _ => 0,
                    };

                    // Computing the mask value from the neighbour values orr from the current index…
                    let mask_value = if left_mask_value != 0 {
                        left_mask_value
                    } else if top_mask_value != 0 {
                        top_mask_value
                    } else {
                        current_index += 1;
                        current_index
                    };

                    // If the left mask value and top mask value exists but are different, we have
                    // an index clash: this means that we have incorrectly created a new index for some
                    // adjacent values.
                    // The tuple of incorrect indexes is stored for the moment and the two indexes will
                    // be merged during post processing…
                    if left_mask_value != 0
                        && top_mask_value != 0
                        && left_mask_value != top_mask_value
                    {
                        // The left mask value is always first in the tuple as it is the largest.
                        // Postprocessing will always rewrite indexes from largest to smallest and
                        // will always start from the end of the array…
                        clash_indexes.push((top_mask_value, left_mask_value));
                    }

                    adjacent_value_mask.set_value(&coordinate, mask_value);
                }
            });
        });

        // Postprocessing:
        // Clashed indexes are going to be fixed by being merged together. We want to keep the smallest
        // indexes during the merge, so it will start from the end, by the largest index value.
        while let Some((smallest_index, largest_index)) = clash_indexes.pop() {
            adjacent_value_mask.change_values(largest_index, smallest_index);
        }

        adjacent_value_mask
    }

    /// Changes all the values in the `Array2d` for a new value.
    ///
    /// # Arguments:
    ///
    /// * `old` - The value to be replaced.
    /// * `new` - The new value.
    fn change_values(&mut self, old: T, new: T) {
        (0..self.size().height).for_each(|j| {
            (0..self.size().width).for_each(|i| {
                let coordinate = Coordinate::new(i, j);
                if self.value(&coordinate) == old {
                    self.set_value(&coordinate, new.clone());
                }
            });
        });
    }
}

impl<T: Display> Display for Array2d<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut desc = format!(
            "Size: width: {} / height: {}\n\r",
            self.size.width, self.size.height
        );

        (0..self.size.height).for_each(|j| {
            (0..self.size.width).for_each(|i| {
                let s = format!("{}\t", self.array[j][i]);
                desc.push_str(s.as_str());
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
    fn new_create_array_from_the_right_size_and_content_1() {
        let a: Array2d<bool> = Array2d::new(Size::new(3, 2));
        assert_eq!(a.size(), &Size::new(3, 2));
        assert_eq!(a.value(&Coordinate::new(0, 0)), false);
        assert_eq!(a.value(&Coordinate::new(1, 0)), false);
        assert_eq!(a.value(&Coordinate::new(2, 0)), false);
        assert_eq!(a.value(&Coordinate::new(0, 1)), false);
        assert_eq!(a.value(&Coordinate::new(1, 1)), false);
        assert_eq!(a.value(&Coordinate::new(2, 1)), false);
    }

    #[test]
    fn new_create_array_from_the_right_size_and_content_2() {
        let a: Array2d<i32> = Array2d::new(Size::new(3, 3));
        assert_eq!(a.size(), &Size::new(3, 3));
        assert_eq!(a.value(&Coordinate::new(0, 0)), 0i32);
        assert_eq!(a.value(&Coordinate::new(1, 0)), 0i32);
        assert_eq!(a.value(&Coordinate::new(2, 0)), 0i32);
        assert_eq!(a.value(&Coordinate::new(0, 1)), 0i32);
        assert_eq!(a.value(&Coordinate::new(1, 1)), 0i32);
        assert_eq!(a.value(&Coordinate::new(2, 1)), 0i32);
        assert_eq!(a.value(&Coordinate::new(0, 2)), 0i32);
        assert_eq!(a.value(&Coordinate::new(1, 2)), 0i32);
        assert_eq!(a.value(&Coordinate::new(2, 2)), 0i32);
    }

    #[test]
    fn values_can_be_set_and_retrieved() {
        let mut a: Array2d<String> = Array2d::new(Size::new(3, 2));
        assert_eq!(a.value(&Coordinate::new(1, 1)), "");
        a.set_value(&Coordinate::new(1, 1), "value1".to_string());
        a.set_value(&Coordinate::new(2, 1), "value2".to_string());
        assert_eq!(a.value(&Coordinate::new(1, 1)), "value1");
        assert_eq!(a.value(&Coordinate::new(2, 1)), "value2");
    }

    #[test]
    fn setting_values_outside_coordinates_is_ignored() {
        let mut a: Array2d<f64> = Array2d::new(Size::new(2, 2));
        a.set_value(&Coordinate::new(5, 5), 1.25);
        assert_eq!(a.value(&Coordinate::new(0, 0)), 0.0);
        assert_eq!(a.value(&Coordinate::new(1, 0)), 0.0);
        assert_eq!(a.value(&Coordinate::new(0, 1)), 0.0);
        assert_eq!(a.value(&Coordinate::new(1, 1)), 0.0);
    }

    #[test]
    fn reading_values_outside_coordinates_returns_default() {
        let mut a: Array2d<String> = Array2d::new(Size::new(2, 2));
        a.set_value(&Coordinate::new(0, 0), "0,0".to_string());
        a.set_value(&Coordinate::new(1, 0), "1,0".to_string());
        a.set_value(&Coordinate::new(0, 1), "0,1".to_string());
        a.set_value(&Coordinate::new(1, 1), "1,1".to_string());
        assert_eq!(a.value(&Coordinate::new(2, 0)), "");
        assert_eq!(a.value(&Coordinate::new(0, 2)), "");
    }

    #[test]
    fn adjacent_values_on_center_values() {
        let mut a: Array2d<u8> = Array2d::new(Size::new(3, 3));
        a.set_value(&Coordinate::new(0, 0), 1);
        a.set_value(&Coordinate::new(1, 0), 2);
        a.set_value(&Coordinate::new(2, 0), 3);
        a.set_value(&Coordinate::new(0, 1), 4);
        a.set_value(&Coordinate::new(1, 1), 5);
        a.set_value(&Coordinate::new(2, 1), 6);
        a.set_value(&Coordinate::new(0, 2), 7);
        a.set_value(&Coordinate::new(1, 2), 8);
        a.set_value(&Coordinate::new(2, 2), 9);
        let (value, left, right, top, bottom) = a.adjacent_values(&Coordinate::new(1, 1));
        assert_eq!(value, 5);
        assert_eq!(left, Some(4));
        assert_eq!(right, Some(6));
        assert_eq!(top, Some(2));
        assert_eq!(bottom, Some(8));
    }

    #[test]
    fn adjacent_values_on_left_edge_values() {
        let mut a: Array2d<u8> = Array2d::new(Size::new(3, 3));
        a.set_value(&Coordinate::new(0, 0), 1);
        a.set_value(&Coordinate::new(1, 0), 2);
        a.set_value(&Coordinate::new(2, 0), 3);
        a.set_value(&Coordinate::new(0, 1), 4);
        a.set_value(&Coordinate::new(1, 1), 5);
        a.set_value(&Coordinate::new(2, 1), 6);
        a.set_value(&Coordinate::new(0, 2), 7);
        a.set_value(&Coordinate::new(1, 2), 8);
        a.set_value(&Coordinate::new(2, 2), 9);
        let (value, left, right, top, bottom) = a.adjacent_values(&Coordinate::new(0, 1));
        assert_eq!(value, 4);
        assert_eq!(left, None);
        assert_eq!(right, Some(5));
        assert_eq!(top, Some(1));
        assert_eq!(bottom, Some(7));
    }

    #[test]
    fn adjacent_values_on_right_edge_values() {
        let mut a: Array2d<u8> = Array2d::new(Size::new(3, 3));
        a.set_value(&Coordinate::new(0, 0), 1);
        a.set_value(&Coordinate::new(1, 0), 2);
        a.set_value(&Coordinate::new(2, 0), 3);
        a.set_value(&Coordinate::new(0, 1), 4);
        a.set_value(&Coordinate::new(1, 1), 5);
        a.set_value(&Coordinate::new(2, 1), 6);
        a.set_value(&Coordinate::new(0, 2), 7);
        a.set_value(&Coordinate::new(1, 2), 8);
        a.set_value(&Coordinate::new(2, 2), 9);
        let (value, left, right, top, bottom) = a.adjacent_values(&Coordinate::new(2, 1));
        assert_eq!(value, 6);
        assert_eq!(left, Some(5));
        assert_eq!(right, None);
        assert_eq!(top, Some(3));
        assert_eq!(bottom, Some(9));
    }

    #[test]
    fn adjacent_values_on_top_edge_values() {
        let mut a: Array2d<u8> = Array2d::new(Size::new(3, 3));
        a.set_value(&Coordinate::new(0, 0), 1);
        a.set_value(&Coordinate::new(1, 0), 2);
        a.set_value(&Coordinate::new(2, 0), 3);
        a.set_value(&Coordinate::new(0, 1), 4);
        a.set_value(&Coordinate::new(1, 1), 5);
        a.set_value(&Coordinate::new(2, 1), 6);
        a.set_value(&Coordinate::new(0, 2), 7);
        a.set_value(&Coordinate::new(1, 2), 8);
        a.set_value(&Coordinate::new(2, 2), 9);
        let (value, left, right, top, bottom) = a.adjacent_values(&Coordinate::new(1, 0));
        assert_eq!(value, 2);
        assert_eq!(left, Some(1));
        assert_eq!(right, Some(3));
        assert_eq!(top, None);
        assert_eq!(bottom, Some(5));
    }

    #[test]
    fn adjacent_values_on_bottom_edge_values() {
        let mut a: Array2d<u8> = Array2d::new(Size::new(3, 3));
        a.set_value(&Coordinate::new(0, 0), 1);
        a.set_value(&Coordinate::new(1, 0), 2);
        a.set_value(&Coordinate::new(2, 0), 3);
        a.set_value(&Coordinate::new(0, 1), 4);
        a.set_value(&Coordinate::new(1, 1), 5);
        a.set_value(&Coordinate::new(2, 1), 6);
        a.set_value(&Coordinate::new(0, 2), 7);
        a.set_value(&Coordinate::new(1, 2), 8);
        a.set_value(&Coordinate::new(2, 2), 9);
        let (value, left, right, top, bottom) = a.adjacent_values(&Coordinate::new(1, 2));
        assert_eq!(value, 8);
        assert_eq!(left, Some(7));
        assert_eq!(right, Some(9));
        assert_eq!(top, Some(5));
        assert_eq!(bottom, None);
    }

    #[test]
    fn adjacent_values_mask_is_generated_for_regular_values_1() {
        // Simple test with non adjacent values:
        // ---
        // Trying to get a values mask for the following values:
        // a a . . .
        // . . b . .
        // . . b b .
        // . . b . c
        // c . . . .
        // Expecting the following mask:
        // 1 1 0 0 0
        // 0 0 2 0 0
        // 0 0 2 2 0
        // 0 0 2 0 3
        // 4 0 0 0 0
        let mut a: Array2d<char> = Array2d::new(Size::new(5, 5));
        a.set_value(&Coordinate::new(0, 0), 'a');
        a.set_value(&Coordinate::new(1, 0), 'a');
        a.set_value(&Coordinate::new(2, 1), 'b');
        a.set_value(&Coordinate::new(2, 2), 'b');
        a.set_value(&Coordinate::new(3, 2), 'b');
        a.set_value(&Coordinate::new(2, 3), 'b');
        a.set_value(&Coordinate::new(4, 3), 'c');
        a.set_value(&Coordinate::new(4, 3), 'c');
        a.set_value(&Coordinate::new(0, 4), 'c');

        let m = a.adjacent_value_mask();
        assert_eq!(m.value(&Coordinate::new(0, 0)), 1);
        assert_eq!(m.value(&Coordinate::new(1, 0)), 1);
        assert_eq!(m.value(&Coordinate::new(2, 0)), 0);
        assert_eq!(m.value(&Coordinate::new(3, 0)), 0);
        assert_eq!(m.value(&Coordinate::new(4, 0)), 0);
        assert_eq!(m.value(&Coordinate::new(0, 1)), 0);
        assert_eq!(m.value(&Coordinate::new(1, 1)), 0);
        assert_eq!(m.value(&Coordinate::new(2, 1)), 2);
        assert_eq!(m.value(&Coordinate::new(3, 1)), 0);
        assert_eq!(m.value(&Coordinate::new(4, 1)), 0);
        assert_eq!(m.value(&Coordinate::new(0, 2)), 0);
        assert_eq!(m.value(&Coordinate::new(1, 2)), 0);
        assert_eq!(m.value(&Coordinate::new(2, 2)), 2);
        assert_eq!(m.value(&Coordinate::new(3, 2)), 2);
        assert_eq!(m.value(&Coordinate::new(4, 2)), 0);
        assert_eq!(m.value(&Coordinate::new(0, 3)), 0);
        assert_eq!(m.value(&Coordinate::new(1, 3)), 0);
        assert_eq!(m.value(&Coordinate::new(2, 3)), 2);
        assert_eq!(m.value(&Coordinate::new(3, 3)), 0);
        assert_eq!(m.value(&Coordinate::new(4, 3)), 3);
        assert_eq!(m.value(&Coordinate::new(0, 4)), 4);
        assert_eq!(m.value(&Coordinate::new(1, 4)), 0);
        assert_eq!(m.value(&Coordinate::new(2, 4)), 0);
        assert_eq!(m.value(&Coordinate::new(3, 4)), 0);
        assert_eq!(m.value(&Coordinate::new(4, 4)), 0);
    }

    #[test]
    fn adjacent_values_mask_is_generated_for_regular_values_2() {
        // Simple test with a lot of adjacent values:
        // ---
        // Trying to get a values mask for the following values:
        // a a b
        // a c b
        // c . b
        // Expecting the following mask:
        // 1 1 2
        // 1 3 2
        // 4 0 2
        let mut a: Array2d<char> = Array2d::new(Size::new(3, 3));
        a.set_value(&Coordinate::new(0, 0), 'a');
        a.set_value(&Coordinate::new(1, 0), 'a');
        a.set_value(&Coordinate::new(2, 0), 'b');
        a.set_value(&Coordinate::new(0, 1), 'a');
        a.set_value(&Coordinate::new(1, 1), 'c');
        a.set_value(&Coordinate::new(2, 1), 'b');
        a.set_value(&Coordinate::new(0, 2), 'c');
        a.set_value(&Coordinate::new(2, 2), 'b');

        let m = a.adjacent_value_mask();
        assert_eq!(m.value(&Coordinate::new(0, 0)), 1);
        assert_eq!(m.value(&Coordinate::new(1, 0)), 1);
        assert_eq!(m.value(&Coordinate::new(2, 0)), 2);
        assert_eq!(m.value(&Coordinate::new(0, 1)), 1);
        assert_eq!(m.value(&Coordinate::new(1, 1)), 3);
        assert_eq!(m.value(&Coordinate::new(2, 1)), 2);
        assert_eq!(m.value(&Coordinate::new(0, 2)), 4);
        assert_eq!(m.value(&Coordinate::new(1, 2)), 0);
        assert_eq!(m.value(&Coordinate::new(2, 2)), 2);
    }

    #[test]
    fn adjacent_values_mask_is_generated_for_triangle_edge_case_1() {
        // The edge case in the algorithm can happen when there is a 'triangle'
        // shape oriented toward bottom right, for instance:
        // . . . .
        // . . a .
        // . a a .
        // . . . .
        // In this case, the algorithm will at first see two different groups,
        // then should be able to spot the issue and fix it, outputing:
        // 0 0 0 0
        // 0 0 1 0
        // 0 1 1 0
        // 0 0 0 0
        let mut a: Array2d<char> = Array2d::new(Size::new(4, 4));
        a.set_value(&Coordinate::new(2, 1), 'a');
        a.set_value(&Coordinate::new(1, 2), 'a');
        a.set_value(&Coordinate::new(2, 2), 'a');

        let m = a.adjacent_value_mask();
        assert_eq!(m.value(&Coordinate::new(2, 1)), 1);
        assert_eq!(m.value(&Coordinate::new(1, 2)), 1);
        assert_eq!(m.value(&Coordinate::new(2, 2)), 1);
    }

    #[test]
    fn adjacent_values_mask_is_generated_for_triangle_edge_case_2() {
        // Edge case with a more complex example:
        // . . . . .
        // . . . a a
        // b b a a .
        // a a a b .
        // . . . . .
        // In this case, we expect all the 'a' values to be a single index:
        // . . . . .
        // . . . 1 1
        // 2 2 1 1 .
        // 1 1 1 5 .
        // . . . . .
        // note: the last group index is 5 instead of 3 because indexes
        // 3 and 4 have been first created incorrectly by the algorithm then
        // merged into the index 1 -> this is the expected behavior!
        let mut a: Array2d<char> = Array2d::new(Size::new(5, 5));
        a.set_value(&Coordinate::new(3, 1), 'a');
        a.set_value(&Coordinate::new(4, 1), 'a');
        a.set_value(&Coordinate::new(0, 2), 'b');
        a.set_value(&Coordinate::new(1, 2), 'b');
        a.set_value(&Coordinate::new(2, 2), 'a');
        a.set_value(&Coordinate::new(3, 2), 'a');
        a.set_value(&Coordinate::new(0, 3), 'a');
        a.set_value(&Coordinate::new(1, 3), 'a');
        a.set_value(&Coordinate::new(2, 3), 'a');
        a.set_value(&Coordinate::new(3, 3), 'b');

        let m = a.adjacent_value_mask();
        assert_eq!(m.value(&Coordinate::new(3, 1)), 1);
        assert_eq!(m.value(&Coordinate::new(4, 1)), 1);
        assert_eq!(m.value(&Coordinate::new(0, 2)), 2);
        assert_eq!(m.value(&Coordinate::new(1, 2)), 2);
        assert_eq!(m.value(&Coordinate::new(2, 2)), 1);
        assert_eq!(m.value(&Coordinate::new(3, 2)), 1);
        assert_eq!(m.value(&Coordinate::new(0, 3)), 1);
        assert_eq!(m.value(&Coordinate::new(1, 3)), 1);
        assert_eq!(m.value(&Coordinate::new(2, 3)), 1);
        assert_eq!(m.value(&Coordinate::new(3, 3)), 5);
    }

    #[test]
    fn retrieving_value_from_mask_index() {
        // Trying to find values from index with the following Array2d:
        // a a b
        // a c b
        // c . b
        // Which will have the following mask:
        // 1 1 2
        // 1 3 2
        // 4 0 2
        let mut a: Array2d<char> = Array2d::new(Size::new(3, 3));
        a.set_value(&Coordinate::new(0, 0), 'a');
        a.set_value(&Coordinate::new(1, 0), 'a');
        a.set_value(&Coordinate::new(2, 0), 'b');
        a.set_value(&Coordinate::new(0, 1), 'a');
        a.set_value(&Coordinate::new(1, 1), 'c');
        a.set_value(&Coordinate::new(2, 1), 'b');
        a.set_value(&Coordinate::new(0, 2), 'c');
        a.set_value(&Coordinate::new(2, 2), 'b');

        assert_eq!(a.value_by_mask_index(1), Some('a'));
        assert_eq!(a.value_by_mask_index(2), Some('b'));
        assert_eq!(a.value_by_mask_index(3), Some('c'));
        assert_eq!(a.value_by_mask_index(4), Some('c'));
        assert_eq!(a.value_by_mask_index(99), None);
    }
}
