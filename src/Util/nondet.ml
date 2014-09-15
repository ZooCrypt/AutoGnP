open Lazy
open Util
(* open Syms *)
(* open Expr *)


(* Nondeterminism Monad *)

type 'a stream =
    Nil  of string option
  | Cons of 'a * ('a stream) lazy_t

type 'a nondet = 'a stream lazy_t

let mempty = lazy (Nil None)

let mfail s = lazy (Nil (Some s))

let ret a = lazy (Cons (a, mempty))

let guard pred =
  if pred then ret () else mempty

let sforce x =
  try
    force x
  with
  | Failure s ->
    failwith s
  (*
  | Wf.Wf_div_zero es ->
    eprintf "Wf: Cannot prove that %a nonzero\n%!" (pp_list "," pp_exp) es; Nil None
  | Wf.Wf_var_undef(v,e) ->
    eprintf  "Wf: Var %a undefined in %a\n%!" Vsym.pp v pp_exp e; Nil None
  *)
  | e ->
    eprintf "sforce: exception %s\n%!" (Printexc.to_string e); Nil None

(* Combine results returned by [a] with results
   returned by [b]. Results from [a] and [b] are
   interleaved. *)
let rec mplus a b = from_fun (fun () ->
  match sforce a with
  | Cons (a1, a2) -> Cons (a1, mplus a2 b)
  | Nil _         -> sforce b)

let rec bind m f = from_fun (fun () ->
  match sforce m with
  | Nil s       -> Nil s
  | Cons (a, b) -> sforce (mplus (f a) (bind b f)))

let fmap f m = bind m (fun x -> ret (f x))

(* Execute and get first [n] results as list,
   use [n = -1] to get all values. *)
let run n m =
  let rec go n m acc =
    if n = 0 then List.rev acc
    else
      match sforce m with
      | Nil _       -> List.rev acc
      | Cons (a, b) -> go (pred n) b (a::acc)
  in go n m []

let pull m =
  match sforce m with
  | Nil e       -> Left e
  | Cons (a, b) -> Right (a,b)

let first m =
  match sforce m with
  | Nil _       -> failwith "first: empty sequence"
  | Cons (a, _) -> a

let is_nil m =
  match sforce m with
  | Nil _       -> true
  | Cons (_, _) -> false

(* Apply function [f] to the first n values,
   use [n = -1] to apply [f] to all values. *)
let iter n m f =
  let rec go n m =
    if n = 0 then ()
    else
      match sforce m with
      | Nil _       -> ()
      | Cons (a, b) -> f a; go (pred n) b
  in go n m

(* helper functions *)
let sequence ms =
  let go m1 m2 =
    bind m1 (fun x ->
    bind m2 (fun xs ->
    ret (x::xs)))
  in
  List.fold_right go ms (ret [])


let mapM f ms = sequence (List.map f ms)
let foreachM ms f = mapM f ms

let rec msum ms =
  match ms with
  | m::ms -> mplus m (msum ms)
  | []    -> mempty

let rec mconcat ms =
  match ms with
  | m::ms -> mplus (ret m) (mconcat ms)
  | []    -> mempty

let (>>=) = bind

(* \ic{Return all subsets $S$ of $m$ such that $|S| \leq k$.} *)
let pick_set k m0 =
  let rec go m k acc =
    guard (k <> 0) >>= fun _ ->
    match sforce m with
    | Nil _ -> ret acc
    | Cons(a,m') ->
      msum [ ret (a::acc)
           ; go m' (k-1) (a::acc)
           ; go m' k     acc ]
  in
  mplus (ret []) (go m0 k [])

(* \ic{Return all subsets $S$ of $m$ such that $|S| = k$.} *)
let pick_set_exact k m0 =
  let rec go m k acc =
    if k = 0
    then ret acc
    else
      match sforce m with
      | Nil _ -> mempty
      | Cons(a,m') ->
        mplus
          (go m' (k-1) (a::acc))
          (go m' k     acc)
  in
  go m0 k []

let rec insertions left z right =
  mplus
    (ret (L.rev_append left (z::right)))
    (match right with
    | []    -> mempty
    | x::xs -> insertions (x::left) z xs)

let rec permutations xs =
  match xs with
  | []    -> ret []
  | x::xs ->
    permutations xs >>= fun xs ->
    insertions [] x xs

(* \ic{Return the cartesian product of $m1$ and $m2$.} *)
let cart m1 m2 =
  m1 >>= fun x1 ->
  m2 >>= fun x2 ->
  ret (x1,x2)

(* \ic{Return the cartesian product of $m$.} *)
let prod m = cart m m

(* \ic{Return the $n$-fold cartesian product of $ms$.} *)
let rec ncart ms =
  match ms with
  | []    -> ret []
  | m::ms ->
    m >>= fun x ->
    ncart ms >>= fun xs ->
    ret (x::xs)

(* \ic{Return the $n$-fold cartesian product of $m$.} *)
let nprod m n =
  let rec go n acc =
    if n <= 0 then ret acc
    else m >>= fun x -> go (n-1) (x::acc)
  in
  go n []
