//mod sudoku;
//use crate::sudoku::Sudoku;
//use std::str::FromStr;

///
/// Basic Sudoku solver
///
/// quick rust development project to play around
/// solves using the following simple rules:
///     - each cell can have 9 possible values
///     - for each given digit remove that as a possibility from its row, col and box
///     - if ever only one option remaining add a given digit to queue
///     - check each row to see if any digits only have one possible location, if so add given digit to queue
///     - repeat above for columns and boxes
///     - when a given digit is added to queue add it to the front, and add check rows and cols and boxes to back of queue
///         -- this have a bunch of duplication that should be tidied up in the future
///
/// Unimplemented logic for the future
///     - look for pairs/triples etc in each row,col and box
///     - if only options for a digit in a row are in the same box remove their availabilities from that box
///         - and other combinations of the logic above

use std::collections::{HashSet, VecDeque};

const VERBOSE: bool = false;

#[derive(Clone)]
struct Sudoku {
    grid: [[u8; 9]; 9],
}

impl Sudoku {
    fn default() -> Self {
        Sudoku {
            grid: [[0; 9]; 9],
        }
    }

    fn from_string(grid_str: &str) -> Sudoku {
        let mut s = Sudoku {
            grid: [[0; 9]; 9]
        };

        let split_str: Vec<_> = grid_str.chars().collect(); //included "" at start and end of vector
        assert_eq!(split_str.len(), 81);
        const BASE: u32 = 10;
        for n in 0..81 {
            match split_str[n].to_digit(BASE) {
                Some(x) => {
                    s.grid[n / 9][n % 9] = x as u8;
                }
                None => {}
            }
        }

        s
    }

    fn print(&self) {
        for i in 0..9 {
            for j in 0..9 {
                if self.grid[i][j] != 0 {
                    print!("{} ", self.grid[i][j]);
                } else {
                    print!(". ");
                }
            }
            println!();
        }
    }

    fn known_digits(&self) -> u8 {
        let mut n = 0u8;
        for row in self.grid {
            for entry in row {
                if entry != 0 {
                    n += 1;
                }
            }
        }
        n
    }

    fn validate_rows(&self) -> bool {
        for i in 0..9 {
            let mut s = HashSet::new();
            for j in 0..9 {
                if self.grid[i][j] != 0 && !s.insert(self.grid[i][j]) {
                    eprintln!("error in row {}", i+1);
                    self.print();
                    return false;
                }
            }
        }
        return true;
    }

    fn validate_cols(&self) -> bool {
        for j in 0..9 {
            let mut s = HashSet::new();
            for i in 0..9 {
                if self.grid[i][j] != 0 && !s.insert(self.grid[i][j]) {
                    eprintln!("error in col {}", j+1);
                    self.print();
                    return false;
                }
            }
        }
        return true;
    }

    fn validate_boxes(&self) -> bool {
        for i in 0..3 {
            for j in 0..3 {
                let mut s = HashSet::new();
                for ii in 0..3 {
                    for jj in 0..3 {
                        if self.grid[i*3+ii][j*3+jj] != 0 && !s.insert(self.grid[i*3+ii][j*3+jj]) {
                            eprintln!("error in box {}", j*3+i+1);
                            self.print();
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }

    fn is_full(&self) -> bool {
        for i in 0..9 {
            for j in 0..9 {
                if self.grid[i][j] == 0 {
                    return false;
                }
            }
        }
        return true;
    }
}

fn start_within_final(base: &Sudoku, new: &Sudoku) -> bool {
    for i in 0..9 {
        for j in 0..9 {
            if base.grid[i][j] != 0  && base.grid[i][j] != new.grid[i][j] {
                return false;
            }
        }
    }
    return true;
}

struct SudokuPossibleValues {
    grid: [[[bool; 9]; 9]; 9],
    num_cell_options: [[u8; 9]; 9],
    knowns: [[Option<u8>; 9]; 9],
}

impl Default for SudokuPossibleValues {
    fn default() -> Self {
        SudokuPossibleValues {
            grid: [[[true; 9]; 9]; 9],
            num_cell_options: [[9; 9]; 9],
            knowns: [[None; 9]; 9],
        }
    }
}

#[derive(PartialEq, Copy, Clone)]
struct Pos {
    x: usize,
    y: usize,
}
struct GivenDigit {
    val: u8,
    pos: Pos
}

impl GivenDigit {
    fn print(&self) {
        println!("{} at ({}, {})", self.val, self.pos.x + 1, self.pos.y + 1);
    }
}

enum Actions {
    AddGivenDigit(GivenDigit),
    CheckRows(),
    CheckColumns(),
    CheckBoxes(),
}

fn get_other_cells_in_row(pos: &Pos) -> Vec<Pos>{
    let mut v = Vec::new();
    for i in 0..9 {
        let p = Pos{x: pos.x, y: i};
        if p != *pos {
            v.push(p)
        }
    }
    v
}

fn get_other_cells_in_col(pos: &Pos) -> Vec<Pos>{
    let mut v = Vec::new();
    for i in 0..9 {
        let p = Pos{x: i, y: pos.y};
        if p != *pos {
            v.push(p)
        }
    }
    v
}

fn get_other_cells_in_box(pos: &Pos) -> Vec<Pos>{
    let mut v = Vec::new();
    let x_0 = pos.x/3;
    let y_0 = pos.y/3;
    for i in 0..3 {
        for j in 0..3 {
            let p = Pos { x: x_0*3 + i, y: y_0*3 + j };
            if p != *pos {
                v.push(p)
            }
        }
    }
    v
}

impl SudokuPossibleValues {
    fn actions_from_sudoku(s: &Sudoku) -> VecDeque<Actions> {
        let mut init_actions = VecDeque::new();
        for i in 0..9 {
            for j in 0..9{
                if s.grid[i][j] != 0 {
                    init_actions.push_back(Actions::AddGivenDigit(GivenDigit{ val: s.grid[i][j], pos: Pos{x: i, y: j}}));
                }
            }
        }
        init_actions.push_back(Actions::CheckRows());
        init_actions.push_back(Actions::CheckColumns());
        init_actions.push_back(Actions::CheckBoxes());
        return init_actions
    }

    //fn no_possible_value(s: &SudokuPossibleValues, x: u8, y: u8) {
    //    println!("Bobbins! we've broken the puzzle");
    //    s.print_knowns();
    //    println!("No digit possible at ({}, {})", x, y);
    //}

    fn remove_option_from_cell(&mut self, pos: Pos, val: u8) -> Result<Vec<Actions>, Box<dyn FnOnce() -> ()>> {
        let mut new_actions = Vec::new();

        if self.knowns[pos.x][pos.y].is_none() && self.grid[pos.x][pos.y][val as usize - 1] == true {
            self.grid[pos.x][pos.y][val as usize - 1] = false;
            self.num_cell_options[pos.x][pos.y] -= 1;

            if self.num_cell_options[pos.x][pos.y] == 0 {
                return Err(Box::new(move || {
                    println!("Bobbins! we've broken the puzzle");
                    println!("No digit possible at ({}, {})", pos.x + 1, pos.y + 1);
                }));
            }

            if self.num_cell_options[pos.x][pos.y] == 1 {
                let opts = SudokuPossibleValues::get_remaining_options(&self.grid[pos.x][pos.y]);
                assert_eq!(opts.len(), 1);
                let g = GivenDigit{val: opts[0], pos: pos.clone()};
                if VERBOSE {
                    println!("got another digit!");
                    g.print();
                }
                new_actions.push(Actions::AddGivenDigit(g));
            }
        }

        return Ok(new_actions);
    }

    fn add_given_digit(sudoku_pv: &mut SudokuPossibleValues, giv: GivenDigit) -> Result<Vec<Actions>, Box<dyn FnOnce() -> ()>> {
        //update given cell to have one value
        for i in 0..9 {
            let n = i as u8 + 1;
            sudoku_pv.grid[giv.pos.x][giv.pos.y][i] = (giv.val == n);
        }

        let mut new_actions = Vec::new();

        if let Some(val) = sudoku_pv.knowns[giv.pos.x][giv.pos.y] {
            if val == giv.val {
                //already got this digit
                return Ok(new_actions);
            } else {
                assert!(false);
            }
        }

        sudoku_pv.num_cell_options[giv.pos.x][giv.pos.y] = 1;
        assert_eq!(sudoku_pv.knowns[giv.pos.x][giv.pos.y].is_some(), false);
        sudoku_pv.knowns[giv.pos.x][giv.pos.y] = Some(giv.val);

        for cell in get_other_cells_in_row(&giv.pos) {
            match sudoku_pv.remove_option_from_cell(cell, giv.val) {
                Ok(act) => new_actions.extend(act),
                err => return err,
            }
        }

        for cell in get_other_cells_in_col(&giv.pos) {
            match sudoku_pv.remove_option_from_cell(cell, giv.val) {
                Ok(act) => new_actions.extend(act),
                err => return err,
            }
        }

        for cell in get_other_cells_in_box(&giv.pos) {
            match sudoku_pv.remove_option_from_cell(cell, giv.val) {
                Ok(act) => new_actions.extend(act),
                err => return err,
            }
        }

        if new_actions.len() != 0 {
            new_actions.push(Actions::CheckRows());
            new_actions.push(Actions::CheckColumns());
            new_actions.push(Actions::CheckBoxes());
        }

        return Ok(new_actions);
    }

    fn check_9set_for_single_availabilities(sudoku_pv: &SudokuPossibleValues, set: Vec<Pos>) -> Result<Vec<Actions>, Box<dyn FnOnce() -> ()>> {
        assert_eq!(set.len(), 9);

        let mut new_actions = Vec::new();

        let mut missing_vals: HashSet<u8> = HashSet::from([1, 2, 3, 4, 5, 6, 7, 8, 9]);
        let mut empty_cells = Vec::new();
        for pos in set {
            if let Some(val) = sudoku_pv.knowns[pos.x][pos.y] {
                missing_vals.remove(&val);
            } else {
                empty_cells.push(pos);
            }
        }
        for val in missing_vals {
            let mut avail_cells = Vec::new();
            for pos in empty_cells.clone() {
                if SudokuPossibleValues::can_have_value(&sudoku_pv.grid[pos.x][pos.y], val) {
                    avail_cells.push(pos);
                }
            }
            if avail_cells.len() == 1 {
                let g = GivenDigit { val: val, pos: avail_cells[0].clone() };
                if VERBOSE {
                    println!("only one spot in set for {}!", val);
                    g.print();
                }
                new_actions.push(Actions::AddGivenDigit(g));
            } else if avail_cells.len() == 0 {
                return Err(Box::new(move || {
                    println!("Bobbins! we've broken the puzzle");
                    println!("No position available for {} in set", val);
                }));
            }
        }
        return Ok(new_actions);
    }

    fn check_rows_for_singles(sudoku_pv: &SudokuPossibleValues) -> Result<Vec<Actions>, Box<dyn FnOnce() -> ()>> {
        let mut new_actions = Vec::new();

        for i in 0..9 {
            let mut row = Vec::new();
            for j in 0..9 {
                row.push(Pos { x: i, y: j });
            }

            match SudokuPossibleValues::check_9set_for_single_availabilities(sudoku_pv, row) {
                Ok(acts) => new_actions.extend(acts),
                err => return err,
            }
        }

        if new_actions.len() != 0 {
            new_actions.push(Actions::CheckRows());
            new_actions.push(Actions::CheckColumns());
            new_actions.push(Actions::CheckBoxes());
        }

        Ok(new_actions)
    }

    fn check_cols_for_singles(sudoku_pv: &SudokuPossibleValues) -> Result<Vec<Actions>, Box<dyn FnOnce() -> ()>> {
        let mut new_actions = Vec::new();

        for j in 0..9 {
            let mut col = Vec::new();
            for i in 0..9 {
                col.push(Pos { x: i, y: j });
            }

            match SudokuPossibleValues::check_9set_for_single_availabilities(sudoku_pv, col) {
                Ok(acts) => new_actions.extend(acts),
                err => return err,
            }
        }

        if new_actions.len() != 0 {
            new_actions.push(Actions::CheckRows());
            new_actions.push(Actions::CheckColumns());
            new_actions.push(Actions::CheckBoxes());
        }

        Ok(new_actions)
    }

    fn check_boxes_for_singles(sudoku_pv: &SudokuPossibleValues) -> Result<Vec<Actions>, Box<dyn FnOnce() -> ()>> {
        let mut new_actions = Vec::new();

        for i in 0..3 {
            for j in 0..3 {
                let mut sbox = Vec::new();
                for ii in 0..3 {
                    for jj in 0..3 {
                        sbox.push(Pos { x: i * 3 + ii, y: j*3+jj });
                    }
                }

                match SudokuPossibleValues::check_9set_for_single_availabilities(sudoku_pv, sbox) {
                    Ok(acts) => new_actions.extend(acts),
                    err => return err,
                }
            }
        }

        if new_actions.len() != 0 {
            new_actions.push(Actions::CheckRows());
            new_actions.push(Actions::CheckColumns());
            new_actions.push(Actions::CheckBoxes());
        }

        Ok(new_actions)
    }

    fn get_remaining_options(opts: &[bool; 9]) -> Vec<u8> {
        let mut v = Vec::new();
        for i in 0..9 {
            if opts[i] {
                v.push(i as u8 +1);
            }
        }
        v
    }

    fn can_have_value(opts: &[bool; 9], val: u8) -> bool {
        return opts[val as usize - 1]
    }

    fn to_sudoku(&self) -> Sudoku {
        let mut s = Sudoku::default();

        for i in 0..9 {
            for j in 0..9 {
                if let Some(val) = self.knowns[i][j] {
                    s.grid[i][j] = val;
                }
            }
        }
        s
    }

    fn print_knowns(&self) {
        self.to_sudoku().print();
    }
}

fn process_step(sudoku_pv: &mut SudokuPossibleValues, act: Actions) -> Result<Vec<Actions>, Box<dyn FnOnce() -> ()>>{
    match act {
        Actions::AddGivenDigit(dig) => SudokuPossibleValues::add_given_digit(sudoku_pv, dig),
        Actions::CheckRows() => SudokuPossibleValues::check_rows_for_singles(sudoku_pv),
        Actions::CheckColumns() => SudokuPossibleValues::check_cols_for_singles(sudoku_pv),
        Actions::CheckBoxes() => SudokuPossibleValues::check_boxes_for_singles(sudoku_pv)
    }
}

fn attempt_solve(s: Sudoku) -> SudokuPossibleValues {
    if VERBOSE {
        println!("Initial grid:");
        s.print();
    }

    let mut possible_vals = SudokuPossibleValues::default();
    let mut next_steps = SudokuPossibleValues::actions_from_sudoku(&s);

    while !next_steps.is_empty() {
        let res = process_step(&mut possible_vals, next_steps.pop_front().unwrap());
        match res {
            Err(f) => {
                f();
                return possible_vals
            },
            Ok(new_actions) => {
                for act in new_actions {
                    match act {
                        Actions::AddGivenDigit(g) => next_steps.push_front(Actions::AddGivenDigit(g)),
                        Actions::CheckRows() => next_steps.push_back(Actions::CheckRows()),
                        Actions::CheckColumns() => next_steps.push_back(Actions::CheckColumns()),
                        Actions::CheckBoxes() => next_steps.push_back(Actions::CheckBoxes()),
                    }
                }
            }
        }
    }

    if VERBOSE {
        println!("done?");
        possible_vals.print_knowns();
    }

    return possible_vals
}

fn main() {

    let _s1 = Sudoku::from_string("123456789123456789123456789123456789123456789123456789123456789123456789123456789");
    let _s2 = Sudoku::from_string("12345678X________________________________________________________________________");
    let _s3 = Sudoku::from_string("1____________1____________X___1______1______________1___1___________1_________1__");
    let _s4 = Sudoku::from_string("1____________1____________X___X______1______________1___X___________1_________1__");
    let _s5 = Sudoku::from_string("___64___7___971_321__2_35__51__6_798___5_9___964_3__25__18_6__435_194___6___57___"); //very easy
    let _s6 = Sudoku::from_string("5_72___9___6_3_7_14______6_1__49___7___5_8___8___27__5_7______92_9_8_6___4___93_8"); //medium
    let _s7 = Sudoku::from_string("_26_3___89__6__1______19_4___73_2_____4_7_8_____8_67___5_72______9__5__44___6_21_");
    let _s8 = Sudoku::from_string("__65____8_95____2_7__9__3______4_27____873____79_5______2__8__9_5____81_3____54__"); //hard

    //attempt_solve(_s1);
    //attempt_solve(_s2);
    //attempt_solve(_s3);
    //attempt_solve(-s4);
    //attempt_solve(_s5);
    //attempt_solve(_s6);
    //attempt_solve(_s7);
    //attempt_solve(_s8);
}



#[cfg(test)]
mod sudoku_tests {
    use crate::{attempt_solve, start_within_final, Sudoku};

    #[test]
    fn test_basic_input() {
        let _s1 = Sudoku::from_string("123456789123456789123456789123456789123456789123456789123456789123456789123456789");
        let _s2 = Sudoku::from_string("123456789________________________________________________________________________");
    }

    #[test]
    fn test_basic_parsing() {
        let s1 = Sudoku::from_string("123456789123456789123456789123456789123456789123456789123456789123456789123456789");
        assert_eq!(s1.known_digits(), 81u8);
        let s2 = Sudoku::from_string("123456789________________________________________________________________________");
        assert_eq!(s2.known_digits(), 9u8);
    }

    #[test]
    fn test_validity_checks() {
        let s1 = Sudoku::from_string("123456789123456789123456789123456789123456789123456789123456789123456789123456789");
        assert_eq!(s1.validate_rows(), true);
        assert_eq!(s1.validate_cols(), false);
        assert_eq!(s1.validate_boxes(), false);
        let s2 = Sudoku::from_string("123456789________________________________________________________________________");
        assert_eq!(s2.validate_rows(), true);
        assert_eq!(s2.validate_cols(), true);
        assert_eq!(s2.validate_boxes(), true);
    }

    #[test]
    fn test_base_contained_within_solved() {
        let s = Sudoku::from_string("___64___7___971_321__2_35__51__6_798___5_9___964_3__25__18_6__435_194___6___57___"); //very easy
        let spv = attempt_solve(s.clone());
        let solved = spv.to_sudoku();
        assert_eq!(start_within_final(&s, &solved), true);

        let s = Sudoku::from_string("5_72___9___6_3_7_14______6_1__49___7___5_8___8___27__5_7______92_9_8_6___4___93_8"); //medium
        let spv = attempt_solve(s.clone());
        let solved = spv.to_sudoku();
        assert_eq!(start_within_final(&s, &solved), true);

        let s = Sudoku::from_string("__65____8_95____2_7__9__3______4_27____873____79_5______2__8__9_5____81_3____54__"); //hard
        let spv = attempt_solve(s.clone());
        let solved = spv.to_sudoku();
        assert_eq!(start_within_final(&s, &solved), true);
    }

    #[test]
    fn test_solves() {
        let s = Sudoku::from_string("___64___7___971_321__2_35__51__6_798___5_9___964_3__25__18_6__435_194___6___57___"); //very easy
        assert!(!s.is_full());
        let solved = attempt_solve(s).to_sudoku();
        assert!(solved.is_full());
        assert!(solved.validate_rows());
        assert!(solved.validate_cols());
        assert!(solved.validate_boxes());

        let s = Sudoku::from_string("5_72___9___6_3_7_14______6_1__49___7___5_8___8___27__5_7______92_9_8_6___4___93_8"); //medium
        assert!(!s.is_full());
        let solved = attempt_solve(s).to_sudoku();
        assert!(solved.is_full());
        assert!(solved.validate_rows());
        assert!(solved.validate_cols());
        assert!(solved.validate_boxes());

        let s = Sudoku::from_string("__65____8_95____2_7__9__3______4_27____873____79_5______2__8__9_5____81_3____54__"); //hard
        assert!(!s.is_full());
        let solved = attempt_solve(s).to_sudoku();
        assert!(solved.is_full());
        assert!(solved.validate_rows());
        assert!(solved.validate_cols());
        assert!(solved.validate_boxes());
    }
}
