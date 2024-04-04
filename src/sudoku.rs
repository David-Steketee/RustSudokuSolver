use std::str::FromStr;

#[derive(Debug)]
pub struct Sudoku {
    grid: [[u8;9];9]
}


pub struct ParseSudokuStringError;

impl FromStr for Sudoku {
    type Err = ParseSudokuStringError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 45
        {
            return Err(ParseSudokuStringError);
        }
        return Ok(Sudoku{grid: [[0; 9]; 9]});
    }
}