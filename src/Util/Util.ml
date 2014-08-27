module type Tagged = sig
  type t
  val tag : t -> int
end

module type OrderedHash =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHash (X : Tagged) : OrderedHash with type t = X.t = struct
  type t = X.t
  let hash t = X.tag t
  let equal t1 t2 = X.tag t1 = X.tag t2 (* FIXME: is there really a speedup using == on int *)
  let compare t1 t2 = Pervasives.compare (X.tag t1) (X.tag t2)
end

module StructMake (X:Tagged) =
  struct
    module T = OrderedHash(X)
    module M = Map.Make(T)
    module S = Set.Make(T)
    module H = Hashtbl.Make(T)
end

module Ints = StructMake (struct
  type t = int
  let tag x = x
end)

module L = List
module F = Format

module Mint = Ints.M
module Sint = Ints.S
module Hint = Ints.H

module Mstring = Map.Make(String)
module Sstring = Set.Make(String)

let unique_int () = Oo.id (object end)

(* ----------------------------------------------------------------------- *)

let list_eq_for_all2 f l1 l2 =
  try List.for_all2 f l1 l2 with _ -> false

let smart_map f l =
  let rec aux r l' = 
    match l' with
    | [] -> l
    | hd::tl -> 
        let hd' = f hd in
        if hd == hd' then aux (hd::r) tl
        else List.rev_append r (hd' :: List.map f tl) in
  aux [] l

let rec drop i l =
  match l with
  | _::xs when i > 0 -> drop (i - 1) xs
  | _ -> l

let rec take i l =
  match l with
  | x::xs when i > 0 -> x::(take (i - 1) xs)
  | _ -> []

let split_n i l = 
  assert (i >= 0);
  let rec aux i r l = 
    match l with 
    | [] -> assert false
    | x::xs ->
      if i = 0 then r,x,xs
      else aux (i-1) (x::r) xs in
  aux i [] l

let cut_n i l = 
  let rec aux i r l = 
    match  l with
    | _ when i <= 0 -> r, l
    | [] -> assert false 
    | a::l -> aux (i-1) (a::r) l in
  aux i [] l

let rec filter_map f l = 
  match l with
  | [] -> []
  | x :: l ->
    match f x with
    | None -> filter_map f l
    | Some z -> z::filter_map f l

      
let list_from_to i j = (* [i,j), i.e., excluding j *)
  let rec go aux i = if i >= j then aux else go (i::aux) (i+1)
  in List.rev (go [] i)

(* let (|>) x f = f x *)

let format_to_string f = 
  ignore (Format.flush_str_formatter ());
  f Format.str_formatter;
  Format.flush_str_formatter ()

(* let fsprintf fm = Format.fprintf Format.str_formatter fm *)

(* let fsget _ = Format.flush_str_formatter () *)

let compare_on f x y = compare (f x) (f y)

let exc_to_opt f = try Some (f ()) with _ -> None

let map_opt f m = match m with
  | Some x -> Some (f x)
  | None -> None

(* let rec group xs0 =
  let rec go acc xs = match (acc,xs) with
        | ([],[])  -> []
        | (acc,[]) -> [acc]
        | ([],y::ys) -> go [y] ys
        | (b::bs, y::ys) -> if b = y then go (b::y::bs) ys else (b::bs)::(go [y] ys)
  in go [] xs0
*)

(* let nub_sort xs = map hd (group (sort compare xs)) *)

let rec replicate_r acc i x =
  if i <= 0 then acc 
  else replicate_r (x::acc) (i-1) x
  
let replicate i x = replicate_r [] i x

let massoc v l = try Some (List.assoc v l) with Not_found -> None

let swap (x,y) = (y,x)

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> Format.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let pp_list_c pe = (pp_list "," pe)
let pp_list_s = pp_list_c (fun fmt -> Format.fprintf fmt "%s")

let pp_string fmt s = Format.fprintf fmt "%s" s

let input_file file_name =
  let in_channel = open_in file_name in
  let rec go lines =
    try
      let l = input_line in_channel in
      go (l :: lines)
    with
      End_of_file -> lines
  in
  let lines = go [] in
  let _ = close_in_noerr in_channel in
  String.concat "\n" (List.rev lines)

let output_file file_name content =
  let out_channel = open_out file_name in
  output_string out_channel content;
  close_out_noerr out_channel

let assert_msg b m =
  if not b then failwith m

type ('a,'b) either = Left of 'a | Right of 'b

let lefts l =
  let rec go acc xs = match xs with
    | Left(x)::xs  -> go (x::acc) xs
    | Right(_)::xs -> go acc      xs
    | [] -> List.rev acc
  in go [] l

let rights l =
  let rec go acc xs = match xs with
    | Left(_)::xs  -> go acc      xs
    | Right(x)::xs -> go (x::acc) xs
    | [] -> List.rev acc
  in go [] l

let lefts_rights l =
  let rec go lacc racc xs = match xs with
    | Left(x)::xs  -> go (x::lacc) racc      xs
    | Right(x)::xs -> go lacc      (x::racc) xs
    | [] -> (List.rev lacc, List.rev racc)
  in go [] [] l

type direction = LeftToRight | RightToLeft

let id x = x

let cat_Some l =
  let rec go acc xs = match xs with
    | Some(x)::xs  -> go (x::acc) xs
    | None::xs     -> go acc      xs
    | [] -> List.rev acc
  in go [] l

let splitn s sep =
  if s = "" then []
  else
    let rec go acc ofs =
      if ofs >= 0 then (
        try
          let idx = String.rindex_from s ofs sep in
          if idx = ofs
          then go (""::acc) (idx - 1)
          else
            let token = String.sub s (idx + 1) (ofs - idx) in
            go (token::acc) (idx - 1)
        with Not_found ->
          (String.sub s 0 (ofs + 1))::acc
      ) else ""::acc
    in
    go [] (String.length s - 1)

let splitn_by s f =
  let rec go acc i len =
    if i + len < String.length s then (
      if f s (i+len)
        then go ((String.sub s i len)::acc) (i+len+1) 0
        else go acc i (len + 1)
    ) else (
      (String.sub s i len)::acc
    )
  in
  List.rev (go [] 0 0)

let string_find_from s t from =
  let len_s = String.length s in
  let len_t = String.length t in
  let rec go i =
    if i < len_s && len_s - i >= len_t then (
      if String.sub s i len_t = t
        then Some i
        else go (i+1)
    ) else (
      None
    )
  in go from

let string_rfind_from s t from =
  let len_s = String.length s in
  let len_t = String.length t in
  let rec go i =
    if i >= 0 then (
      if len_s - i >= len_t && String.sub s i len_t = t
        then Some i
        else go (i-1)
    ) else (
      None
    )
  in go from

let split s sep =
  match (try Some (String.index s sep) with Not_found -> None) with
  | Some i ->
      let a = String.sub s 0 i in
      let b = if String.length s > i + 1
              then String.sub s (i + 1) (String.length s - i - 1)
              else ""
      in
      Some (a, b)
  | None   -> None

(** Exception *)
exception Invalid_rule of string 

let tacerror fmt =
  let buf  = Buffer.create 127 in
  let fbuf = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush fbuf ();
      raise (Invalid_rule (Buffer.contents buf)))
    fbuf fmt

let fsprintf fmt =
  let buf  = Buffer.create 127 in
  let fbuf = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush fbuf ();
      (Buffer.contents buf))
    fbuf fmt
