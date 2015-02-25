open Asm

let rec mk_igraph mps igs = function  (* 干渉グラフ *)
  | [] -> igs
  | e::es ->
     let igs =
       match get_inst e with
       | If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else) ->
	  mk_igraph mps (mk_igraph mps igs e_then) e_else
       | _ -> igs in
     let liveouts = tuple2_map (Liveness.get_liveout e) mps in
     let isets =
       match get_inst e with
       | Mr(_) | FMr(_) -> tuple2_map2 S.diff liveouts (Liveness.use_set e)
       | _  -> liveouts in
     let dsets = Liveness.def_set e in
     let igs = tuple2_map3 UG.add_prod_edges dsets isets igs in
     mk_igraph mps igs es

let rec mk_mgraph mps mgs = function (* 転送命令グラフ *)
  | [] -> mgs
  | e::es ->
     let mgs =
       match get_inst e with
       | If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else) ->
	  mk_mgraph mps (mk_mgraph mps mgs e_then) e_else
       | _ -> mgs in
     let mgs =
       match get_inst e with
       | Mr(_) | FMr(_) -> 
	  let usets = Liveness.use_set e in
	  let dsets = Liveness.def_set e in
	  tuple2_map3 UG.add_prod_edges dsets usets mgs
       | _  -> mgs in
     mk_mgraph mps mgs es

let rec simplify k ig stk =
  let non_regs = S.filter (fun x -> not (is_reg x)) (UG.nodes ig) in
  if S.is_empty non_regs then
    (ig, stk)
  else
    let low_degs = S.filter (fun x -> UG.deg x ig < k) non_regs in
    if S.is_empty low_degs then
      (* let xc = let x = S.min_elt non_regs in (x, M.find x cst) in *)
      (* let (x, _) =  *)
      (* 	S.fold (fun y (x, c) ->  *)
      (* 		let d = M.find y cst in *)
      (* 		if d < c then (y, d) else (x, c)) *)
      (* 	       non_regs xc in *)
      let x = S.min_elt non_regs in
      let adj_x = UG.adj x ig in
      (UG.rm_node x ig, (x, adj_x)::stk)
    else
      let (ig, stk) = 
	S.fold (fun x (ig, stk) -> 
		let adj_x = UG.adj x ig in
		(UG.rm_node x ig, (x, adj_x)::stk)) 
	       low_degs (ig, stk) in
      simplify k ig stk

let h ({ name = Id.L(x); args = yts; body = e; ret = t } as fdef) =
  let mps = Liveness.h fdef in
  let igs = mk_igraph mps (UG.new_graph (), UG.new_graph ()) e in
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  UG.pp_graph (fst igs);
  UG.pp_graph (snd igs);
  ()

let f (Prog(fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  List.iter h fundefs;
  let s = Liveness.g e in
  Prog(fundefs, e)
