module L = List
module F = Format
module BL = Bolt.Logger

(* let undef _ = failwith "undefined" *)

let hcomb = Hashcons.combine
let hcomb_l = Hashcons.combine_list
let hcomb_h = Hashcons.combine_hashes
