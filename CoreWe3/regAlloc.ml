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

exception Spill of Id.t

let regmem x regenv = is_reg x || M.mem x regenv
let regfind x regenv = if is_reg x then x else M.find x regenv

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

let rec select mg rset regenv = function
  | (ig, []) -> regenv
  | (ig, (x, adj_x)::stk) -> 
     let adj_regs = 
       S.fold (fun y s -> S.add (regfind y regenv) s) adj_x S.empty in
     let non_adj_regs = S.diff rset adj_regs in
     if S.is_empty non_adj_regs then
       raise (Spill x)
     else
       let move_regs = 
	 S.fold (fun y s -> 
		 if regmem y regenv then S.add (regfind y regenv) s
	         else s) (UG.adj x mg) S.empty in
       let u = S.union non_adj_regs move_regs in
       let r = S.max_elt (if S.is_empty u then non_adj_regs else u) in
       let ig = UG.add_adj x adj_x ig in
       select mg rset (M.add x r regenv) (ig, stk)

(* let rec allocate regenv = function  *)
(*   | [] -> [] *)
(*   | e::es -> (allocate' regenv e)::(allocate regenv es) *)
(* and allocate' regenv (i, e, b) = *)
(*   let e' = *)
(*     match e with *)
(*     | Nop -> Nop *)
(*     | Ld((x, t), y, i) -> Ld((),) *)
(*     | St(_) -> "St" *)
(*     | FLd(_) -> "FLd" *)
(*     | FSt(_) -> "FSt" *)
(*     | IToF(_) -> "IToF" *)
(*     | FToI(_) -> "FToI" *)
(*     | Neg(_) -> "Neg" *)
(*     | Add(_) -> "Add" *)
(*     | Sub(_) -> "Sub" *)
(*     | And(_) -> "And" *)
(*     | Or(_) -> "Or" *)
(*     | Li(_) -> "Li" *)
(*     | Shl(_) -> "Shl" *)
(*     | Shr(_) -> "Shr" *)
(*     | FAdd(_) -> "FAdd" *)
(*     | FSub(_) -> "FSub" *)
(*     | FMul(_) -> "FMul" *)
(*     | FInv(_) -> "FInv" *)
(*     | FAbs(_) -> "FAbs" *)
(*     | Sqrt(_) -> "Sqrt" *)
(*     | FLi(_) -> "FLi" *)
(*     | If(_) -> "If" *)
(*     | IfF(_) -> "IfF" *)
(*     | Call(_) -> "Call" *)
(*     | LoadLabel(_) -> "LoadLabel" *)
(*     | Mr(_) -> "Mr" *)
(*     | FMr(_) -> "FMr" *)
(*     | Save(_) -> "Save" *)
(*     | Restore(_) -> "Restore" *)
(*     | FSave(_) -> "FSave" *)
(*     | FRestore(_) -> "FRestore" *)
(*   in *)
(*   (i, e', b) *)

let h ({ name = Id.L(x); args = yts; body = e; ret = t } as fdef) =
  let mps = Liveness.h fdef in
  let igs = mk_igraph mps (UG.new_graph (), UG.new_graph ()) e in
  Format.eprintf "igraph ==================@.";
  UG.pp_graph (fst igs);
  let mgs = mk_mgraph mps (UG.new_graph (), UG.new_graph ()) e in
  let igstks = tuple2_map3 simplify (Array.length regs, Array.length fregs) igs ([], []) in
  let (regenvi, regenvf) = tuple2_map4 select mgs (regset, fregset) (M.empty, M.empty) igstks in
  let regenv = M.fold (fun x r env -> M.add x r env) regenvi regenvf in
  Format.eprintf "regenv ==================@.";
  M.iter (fun x r -> Format.eprintf "%s -> %s@." x r) regenv;
  ()

let f (Prog(fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  List.iter h fundefs;
  let s = Liveness.g e in
  Prog(fundefs, e)
