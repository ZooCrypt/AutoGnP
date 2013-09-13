let main =
  let _e = Parse.scheme_descr
    "start_proof (k1) (G : k3 -> k1 + k2; H : k1 + k2 -> k3) \
     (f : k1 + k2 + k3) (r : k3) (f(H(r)) + f^-1(G(r)) | ([r | r]{k1+k2,k1+k2}) + r | (m_b + *) | 0^{k1})"
  in ()
  (* match e with *)
  (* | Descr(msg_decl, h_decls, p_decls, rv_decls, scheme) -> *)
      (* let (te,s) = declare_scheme msg_decl h_decls p_decls rv_decls scheme in *)
      (* Format.printf "@[scheme: %a@]@." pp_expr s *)
