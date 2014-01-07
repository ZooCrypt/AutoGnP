(** Simple linear algebra (equation solving) over F_2. *)

open Format

type col = int
 
type row = int

type solved = Pivot of row * col | Solved of bool list option

val cols : 'a array array -> int

val rows : 'a array -> int

val sol_col : 'a array array -> int

val col_to_list : 'a array array -> int -> 'a list

val pp_row_vec : (formatter -> 'a -> unit) -> formatter -> 'a array -> unit

val pp_matrix :  (formatter -> 'a -> unit) -> formatter -> 'a array array -> unit

val iter_rows : 'a array -> (int -> 'b) -> unit

val iter_cols : 'a array array -> (int -> 'b) -> unit

val iter_cols_with_sol : 'a array array -> (int -> 'b) -> unit

val classify_cols : bool array array -> bool array * bool array * int option array

val is_solved : bool array array -> solved

val add_row_to : bool array array -> int -> int -> unit

val reduce_pivot : bool array array -> int -> int -> unit

val solve : bool array list -> bool array -> bool list option
