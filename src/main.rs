//! AtariGo binary crate.
//!
//! Allow a game of atarigo to be played from command line. If the CLI application
//! is called without argument, the game will be interactive and both players will
//! have to provide coordinates.
//!
//! If the CLI application is started with the 'random' parameter, the computer will
//! play a (completely) random game and exit.

use std::env;

use games::{AtariGo, InteractiveAtariGo, RandomAtariGo};

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.get(1) {
        Some(arg) if arg.to_lowercase() == "random" => {
            let mut random_game = RandomAtariGo::new();
            random_game.run();
        }
        _ => {
            let mut interactive_game = InteractiveAtariGo::new();
            interactive_game.run();
        }
    }
}

mod games {
    use core::time;
    use std::{io, thread};

    use atarigo::{
        game::Game,
        models::{Coordinate, Stone},
    };
    use rand::seq::SliceRandom;

    pub trait AtariGo {
        fn run(&mut self);
    }

    pub struct InteractiveAtariGo {
        game: Game,
    }

    impl InteractiveAtariGo {
        pub fn new() -> Self {
            Self {
                game: Game::default(),
            }
        }
    }

    impl AtariGo for InteractiveAtariGo {
        fn run(&mut self) {
            println!("ATARI GO GAME");
            println!("--------------------");
            println!("{}", self.game);
            loop {
                let mut col_str = String::new();
                println!("Select a COLUMN (from 1 to {}): ", self.game.size().width);
                io::stdin()
                    .read_line(&mut col_str)
                    .expect("Failed to read column");

                let mut row_str = String::new();
                println!("Select a ROW (from 1 to {}): ", self.game.size().height);
                io::stdin()
                    .read_line(&mut row_str)
                    .expect("Failed to read row");

                let col: usize = match col_str.trim().parse() {
                    Ok(value) if value >= 1 && value <= self.game.size().width => value,
                    _ => {
                        println!("Invalid COLUMN!");
                        continue;
                    }
                };

                let row: usize = match row_str.trim().parse() {
                    Ok(value) if value >= 1 && value <= self.game.size().height => value,
                    _ => {
                        println!("Invalid ROW!");
                        continue;
                    }
                };

                // note: the Goban coordinates are starting at 0 internally but we convert them
                // so they start at 1 in the CLI game to avoid confusing players…

                self.game.play_move(&Coordinate::new(col - 1, row - 1));
                println!("{}", self.game);

                if let Some(player) = self.game.winner() {
                    println!("--------------------");
                    println!("{player} wins!");
                    println!("--------------------");
                    break;
                }

                println!("--------------------");
            }
        }
    }

    pub struct RandomAtariGo {
        game: Game,
    }

    impl RandomAtariGo {
        pub fn new() -> Self {
            Self {
                game: Game::default(),
            }
        }

        fn empty_intersection(&self) -> Vec<Coordinate> {
            let mut coordinates: Vec<Coordinate> = Vec::new();
            (0..self.game.size().height).for_each(|j| {
                (0..self.game.size().width).for_each(|i| {
                    let coordinate = Coordinate::new(i, j);
                    if self.game.stone(&coordinate) == Stone::NoStone {
                        coordinates.push(coordinate);
                    }
                });
            });
            coordinates
        }
    }

    impl AtariGo for RandomAtariGo {
        fn run(&mut self) {
            println!("RANDOM ATARI GO GAME");
            println!("--------------------");
            println!("{}", self.game);

            let mut rng = rand::thread_rng();
            let mut round = 1;

            loop {
                let coordinate = self
                    .empty_intersection()
                    .choose(&mut rng)
                    .unwrap()
                    .to_owned();
                self.game.play_move(&coordinate);
                println!("ROUND {round}:");
                println!("{}", self.game);
                println!("--------------------");

                if let Some(player) = self.game.winner() {
                    println!("{player} wins!");
                    println!("--------------------");
                    break;
                }

                thread::sleep(time::Duration::from_millis(500));
                round += 1;
            }
        }
    }
}
