//! A struct used to represent a game of atari-go;
//!
//! The `Game` structure can be created with an arbitrary size using the
//! `new()` function or with the default size and position using the
//! `default() function (in this case, the size will be 9x9 and four moves
//! will be pre-played on the board).
//!
//! To play a game of atari-go, creates a mutable instance of `Game` then
//! use the `play_move()` function until the `winner()` returns an actual
//! winner:
//!
//! ```
//! use crate::atarigo::models::Coordinate;
//! use crate::atarigo::game::Game;
//!
//! let mut game = Game::default();
//! game.play_move(&Coordinate::new(4, 3));
//!
//! assert!(matches!(game.winner(), None));
//! ```

use crate::{
    goban::Goban,
    models::{Coordinate, Player, Size, Stone},
};

/// Represents a game of atari-go.
#[derive(Debug)]
pub struct Game {
    /// The underlying goban representing the current state of the game.
    goban: Goban,
    /// The next player that will play a move.
    next_player: Player,
    /// The winner if any, None otherwise.
    winner: Option<Player>,
}

impl Game {
    /// Returns a new `Game` with a goban of arbitrary size and no move
    /// on the board.
    ///
    /// # Arguments:
    ///
    /// * `size` - The size of the underlying goban.
    pub fn new(size: Size) -> Self {
        Self {
            goban: Goban::new(size),
            next_player: Player::Black,
            winner: None,
        }
    }

    /// Returns the size of the underlying goban.
    pub fn size(&self) -> &Size {
        self.goban.size()
    }

    /// Returns the winner of this game if any, None otherwise.
    pub fn winner(&self) -> &Option<Player> {
        &self.winner
    }

    /// Returns the stone color for some given coordinates.
    ///
    /// # Arguments:
    ///
    /// * `coordinate` - The coordinates of the stone which should be retrieved.
    pub fn stone(&self, coordinate: &Coordinate) -> Stone {
        self.goban.stone(coordinate)
    }

    /// Plays a move for the next player.
    ///
    /// Calling this function will add a stone for the next player at the given
    /// coordinates. The next player will then be automatically updated and
    /// the winner will be chosen if any.
    ///
    /// Note: this function will ignore any invalid move:
    ///
    /// * moves outside of the goban's size,
    /// * moves when the game already have a winner,
    /// * moves on a non empty coordinate,
    /// * _suicide_ moves.
    ///
    /// # Arguments:
    ///
    /// * `coordinate` - The coordinate of an empty intersection in which the stone of
    ///                  the next player will be played.
    pub fn play_move(&mut self, coordinate: &Coordinate) {
        if self.winner.is_some() {
            // Move ignored because the game is already finished
            return;
        }

        if self.goban.stone(coordinate) != Stone::NoStone {
            // Move ignored because there is already a stone here
            return;
        }

        if !coordinate.is_valid_for_size(self.goban.size()) {
            // Move ignored because it is outside of the goban size
            return;
        }

        let current_player = self.next_player.clone();
        let current_player_stone = if current_player == Player::Black {
            Stone::Black
        } else {
            Stone::White
        };

        // Playing the stone
        self.goban
            .set_stone(coordinate, current_player_stone.clone());

        // Collecting the group liberties to assess if a winner exists
        let group_liberties = self.goban.group_liberties();

        // Searching for dead groups
        let dead_groups: Vec<(i32, Stone)> = group_liberties
            .iter()
            .filter(|&(_, &liberties)| liberties == 0)
            .map(|(&index, _)| {
                (
                    index,
                    self.goban
                        .stone_by_group_index(index)
                        .expect("The index will always correspond to a valid stone"),
                )
            })
            .collect();

        let dead_count = dead_groups.len();

        // If there is only one dead group from the color of the current player, this is a suicide and
        // this not allowed by the rules: we revert the move and exit!
        if let Some((_, stone)) = dead_groups.first() {
            if dead_count == 1 && stone == &current_player_stone {
                // Reverting the move…
                self.goban.set_stone(coordinate, Stone::NoStone);
                return;
            }
        }

        // Handling dead groups & finding the winner
        if dead_count > 0 {
            // Finding the winner
            self.winner = Some(current_player);

            // Removing dead groups
            let group_mask = self.goban.group_mask();
            for (index, stone) in dead_groups {
                // We remove all dead groups except the one from the current player if any
                if stone != current_player_stone {
                    self.goban.remove_group(index, Some(&group_mask));
                }
            }
        }

        // Switching to the next player
        self.next_player = if self.next_player == Player::Black {
            Player::White
        } else {
            Player::Black
        };
    }
}

impl Default for Game {
    /// Returns a new `Game` with a goban of size 9x9 and with the typical _cross-cut_
    /// position used at start of an atari-go game:
    ///
    /// ```text
    /// . . . . . . . . .
    /// . . . . . . . . .
    /// . . . . . . . . .
    /// . . . . . . . . .
    /// . . . . ● ◯ . . .
    /// . . . . ◯ ● . . .
    /// . . . . . . . . .
    /// . . . . . . . . .
    /// . . . . . . . . .
    /// ```
    fn default() -> Self {
        // Creating a new 9x9 Goban
        let mut game = Self::new(Size::new(9, 9));

        // Setting the first 4 stones according to the rules
        game.goban.set_stone(&Coordinate::new(4, 4), Stone::Black);
        game.goban.set_stone(&Coordinate::new(4, 5), Stone::White);
        game.goban.set_stone(&Coordinate::new(5, 5), Stone::Black);
        game.goban.set_stone(&Coordinate::new(5, 4), Stone::White);

        game
    }
}

impl std::fmt::Display for Game {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut desc = self.goban.to_string();
        match &self.winner {
            Some(winner) => desc.push_str(format!("Winner: {}", winner).as_str()),
            None => desc.push_str(format!("Next player: {}", self.next_player).as_str()),
        }
        write!(f, "{}", desc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn game_can_be_created_with_size() {
        let g = Game::new(Size::new(2, 3));
        assert_eq!(g.size(), &Size::new(2, 3));
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 2)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 2)), Stone::NoStone);
    }

    #[test]
    fn default_game_is_9x9_with_4_stone_in_cross_cut() {
        let g = Game::default();
        assert_eq!(g.size(), &Size::new(9, 9));
        assert_eq!(g.stone(&Coordinate::new(4, 4)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(5, 4)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(4, 5)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(5, 5)), Stone::Black);
    }

    #[test]
    fn stones_can_be_played() {
        let mut g = Game::new(Size::new(3, 3));
        assert_eq!(g.next_player, Player::Black);

        g.play_move(&Coordinate::new(0, 0));
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::Black);
        assert_eq!(g.next_player, Player::White);
        assert!(matches!(g.winner, None));

        g.play_move(&Coordinate::new(2, 2));
        assert_eq!(g.stone(&Coordinate::new(2, 2)), Stone::White);
        assert_eq!(g.next_player, Player::Black);
        assert!(matches!(g.winner, None));

        g.play_move(&Coordinate::new(1, 1));
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::Black);
        assert_eq!(g.next_player, Player::White);
        assert!(matches!(g.winner, None));
    }

    #[test]
    fn game_can_be_won_with_simple_capture() {
        let mut g = Game::new(Size::new(3, 3));

        g.play_move(&Coordinate::new(0, 0));
        g.play_move(&Coordinate::new(0, 1));
        g.play_move(&Coordinate::new(1, 0));
        g.play_move(&Coordinate::new(1, 1));
        g.play_move(&Coordinate::new(2, 0));
        assert!(matches!(g.winner, None));

        // Current position:
        // ● ● ●
        // ◯ ◯ x
        // . . .
        // -> white is going to play in the 'x' intersection and win the game
        // by capturing one group of 3 stones

        g.play_move(&Coordinate::new(2, 1));
        assert!(matches!(g.winner(), Some(p) if p == &Player::White));

        // The dead group is removed from the board:
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(2, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 1)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::White); // newly played stone
    }

    #[test]
    fn game_can_be_won_with_double_group_kill() {
        let mut g = Game::new(Size::new(3, 3));

        g.play_move(&Coordinate::new(0, 1));
        g.play_move(&Coordinate::new(0, 0));
        g.play_move(&Coordinate::new(2, 1));
        g.play_move(&Coordinate::new(2, 0));
        assert!(matches!(g.winner, None));

        // Current position:
        // ◯ x ◯
        // ● . ●
        // . . .
        // -> black is going to play in the 'x' intersection and win the game
        // by capturing two groups at once

        g.play_move(&Coordinate::new(1, 0));
        assert!(matches!(g.winner(), Some(p) if p == &Player::Black));

        // The dead groups are removed from the board:
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(2, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 1)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::Black); // newly played stone
    }

    #[test]
    fn game_can_be_won_with_no_liberty_move_killing_some_groups() {
        let mut g = Game::new(Size::new(3, 3));

        g.play_move(&Coordinate::new(0, 0));
        g.play_move(&Coordinate::new(0, 1));
        g.play_move(&Coordinate::new(2, 0));
        g.play_move(&Coordinate::new(2, 1));
        g.play_move(&Coordinate::new(1, 1));
        assert!(matches!(g.winner, None));

        // Current position:
        // ● x ●
        // ◯ ● ◯
        // . . .
        // -> white is going to play in the 'x' intersection and win the game
        // by capturing two groups at once

        g.play_move(&Coordinate::new(1, 0));
        assert!(matches!(g.winner(), Some(p) if p == &Player::White));

        // The dead groups are removed from the board:
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(2, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(0, 1)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::White); // newly played stone
    }

    #[test]
    fn suicide_move_are_not_allowed() {
        let mut g = Game::new(Size::new(3, 3));

        g.play_move(&Coordinate::new(0, 0));
        g.play_move(&Coordinate::new(2, 1));
        g.play_move(&Coordinate::new(1, 0));
        g.play_move(&Coordinate::new(1, 2));
        assert_eq!(g.next_player, Player::Black);
        assert!(matches!(g.winner(), None));

        // Current position:
        // ● ● .
        // . . ◯
        // . ◯ x
        // -> black will attempt to play in the 'x' intersection, but the move will
        // be ignored, no winner will appear and the current player will not change:
        // suicide moves are not allowed

        g.play_move(&Coordinate::new(2, 2));
        assert!(matches!(g.winner(), None));
        assert_eq!(g.next_player, Player::Black);

        assert_eq!(g.stone(&Coordinate::new(2, 2)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(1, 2)), Stone::White);
    }

    #[test]
    fn playing_on_stone_is_not_allowed_1() {
        let mut g = Game::new(Size::new(3, 3));

        g.play_move(&Coordinate::new(0, 0));
        g.play_move(&Coordinate::new(2, 1));
        g.play_move(&Coordinate::new(1, 0));
        assert_eq!(g.next_player, Player::White);
        assert!(matches!(g.winner(), None));

        // Current position:
        // ● ● .
        // . . ◯
        // . . .
        // -> white will attempt to play on a black stone, but the move will be ignored
        // because playing on existing stone is not allowed.

        g.play_move(&Coordinate::new(1, 0));
        assert_eq!(g.next_player, Player::White);
        assert!(matches!(g.winner(), None));

        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::Black);
    }

    #[test]
    fn playing_on_stone_is_not_allowed_2() {
        let mut g = Game::new(Size::new(3, 3));

        g.play_move(&Coordinate::new(0, 0));
        g.play_move(&Coordinate::new(2, 1));
        g.play_move(&Coordinate::new(1, 0));
        g.play_move(&Coordinate::new(2, 2));
        assert_eq!(g.next_player, Player::Black);
        assert!(matches!(g.winner(), None));

        // Current position:
        // ● ● .
        // . . ◯
        // . . ◯
        // -> black will attempt to play on a black stone, but the move will be ignored
        // because playing on existing stone is not allowed.

        g.play_move(&Coordinate::new(0, 0));
        assert_eq!(g.next_player, Player::Black);
        assert!(matches!(g.winner(), None));

        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::Black);
        assert_eq!(g.stone(&Coordinate::new(2, 2)), Stone::White);
    }

    #[test]
    fn playing_when_already_won_is_not_allowed() {
        let mut g = Game::new(Size::new(3, 3));

        g.play_move(&Coordinate::new(0, 0));
        g.play_move(&Coordinate::new(0, 1));
        g.play_move(&Coordinate::new(1, 0));
        g.play_move(&Coordinate::new(1, 1));
        g.play_move(&Coordinate::new(2, 0));
        g.play_move(&Coordinate::new(2, 1));
        assert_eq!(g.next_player, Player::Black);
        assert!(matches!(g.winner(), Some(p) if p == &Player::White));

        // Current position:
        // x x x
        // ◯ ◯ ◯
        // . . .
        // -> white has won by capturing the stones marked 'x', any further
        // attempt to play a move should be ignored

        g.play_move(&Coordinate::new(1, 0));
        assert_eq!(g.next_player, Player::Black);
        assert!(matches!(g.winner(), Some(p) if p == &Player::White));

        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(2, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 1)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::White);
        assert_eq!(g.stone(&Coordinate::new(2, 1)), Stone::White);
    }

    #[test]
    fn playing_outside_goban_is_not_allowed() {
        let mut g = Game::new(Size::new(2, 2));
        assert_eq!(g.next_player, Player::Black);
        assert!(matches!(g.winner(), None));

        g.play_move(&Coordinate::new(2, 0));
        assert_eq!(g.next_player, Player::Black);
        assert!(matches!(g.winner(), None));
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::NoStone);

        g.play_move(&Coordinate::new(0, 2));
        assert_eq!(g.next_player, Player::Black);
        assert!(matches!(g.winner(), None));
        assert_eq!(g.stone(&Coordinate::new(0, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 0)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(0, 1)), Stone::NoStone);
        assert_eq!(g.stone(&Coordinate::new(1, 1)), Stone::NoStone);
    }
}
