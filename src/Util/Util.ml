(*s This module defines types tagged with [int]s, some convenience functor
    applications for maps, sets, hashtables, and some convenience functions
    for lists and pretty printing. *)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Convenience Functors} *)

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
  let equal t1 t2 = X.tag t1 = X.tag t2
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


(*i ----------------------------------------------------------------------- i*)
(* \subsection{Misc functions} *)

let unique_int () = Oo.id (object end)

let exc_to_opt f = try Some (f ()) with _ -> None

let map_opt f m = match m with
  | Some x -> Some (f x)
  | None -> None

let from_opt x o = match o with
  | Some y -> y
  | None   -> x

let opt f x o = match o with
  | Some y -> f y
  | None   -> x


let swap (x,y) = (y,x)

let compare_on f x y = compare (f x) (f y)

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

let assert_msg b m = if not b then failwith m

type ('a,'b) either = Left of 'a | Right of 'b

type direction = LeftToRight | RightToLeft

let string_of_dir = function
  | LeftToRight -> "->"
  | RightToLeft -> "<-"

let id x = x

(*i ----------------------------------------------------------------------- i*)
(* \subsection{List functions} *)

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
      else aux (i-1) (x::r) xs
  in
  aux i [] l

let cut_n i l = 
  let rec aux i r l = 
    match  l with
    | _ when i <= 0 -> r, l
    | [] -> assert false 
    | a::l -> aux (i-1) (a::r) l
  in
  aux i [] l

let rec filter_map f l = 
  match l with
  | [] -> []
  | x :: l ->
    match f x with
    | None -> filter_map f l
    | Some z -> z::filter_map f l

(** For interval $[i,j)$, i.e., excluding $j$. *)
let list_from_to i j =
  let rec go aux i = if i >= j then aux else go (i::aux) (i+1)
  in List.rev (go [] i)

let rec replicate_r acc i x =
  if i <= 0 then acc 
  else replicate_r (x::acc) (i-1) x
  
let replicate i x = replicate_r [] i x

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

let cat_Some l =
  let rec go acc xs = match xs with
    | Some(x)::xs  -> go (x::acc) xs
    | None::xs     -> go acc      xs
    | [] -> List.rev acc
  in go [] l

let conc_map f xs =
  L.concat (L.map f xs)

let map_accum f init xs =
  let rec go acc xs res =
    match xs with
    | []    -> (acc,L.rev res)
    | x::xs ->
      let (acc,y) = f acc x in
      go acc xs (y::res)
  in
  go init xs []

(*i ----------------------------------------------------------------------- i*)
(* \subsection{String functions} *)

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

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Pretty printing} *)

let rec pp_list sep pp_elt f l =
  match l with
  | [] -> ()
  | [e] -> pp_elt f e
  | e::l -> F.fprintf f "%a%(%)%a" pp_elt e sep (pp_list sep pp_elt) l

let pp_list_c pe = (pp_list "," pe)
let pp_list_s = pp_list_c (fun fmt -> F.fprintf fmt "%s")

let pp_string fmt s = F.fprintf fmt "%s" s

let pp_int fmt i = F.fprintf fmt "%i" i

let pp_if c pp1 pp2 fmt x =
  if c then pp1 fmt x else pp2 fmt x

let pp_pair pp1 pp2 fmt (a,b) =
  F.fprintf fmt "(%a,%a)" pp1 a pp2 b

let fsprintf fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      (Buffer.contents buf))
    fbuf fmt

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Debug printing} *)

let debug_fmt = ref F.err_formatter

let eprintf fs = F.fprintf !debug_fmt fs

let set_debug_buffer () =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  debug_fmt := fbuf;
  buf

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Exception required by Logic modules} *)

exception Invalid_rule of string 

let tacerror fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      eprintf "%s\n" s;
      raise (Invalid_rule s))
    fbuf fmt

