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

let rec add_move_edges yts rs frs (mgi, mgf) =
  match yts with
  | [] -> (mgi, mgf)
  | (y, t)::yts ->
     match t with
     | Type.Unit -> add_move_edges yts rs frs (mgi, mgf)
     | Type.Float -> 
	add_move_edges yts rs (List.tl frs) (mgi, UG.add_edge (y, List.hd frs) mgf)
     | _ -> 
	add_move_edges yts (List.tl rs) frs (UG.add_edge (y, List.hd rs) mgi, mgf)

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
       | Call(xt, _, yts) ->
	  let mgs = add_move_edges yts reglist freglist mgs in
	  add_move_edges [xt] reglist freglist mgs
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

let rec init_regenv regenv = function
  | [] -> regenv
  | e::es ->
     let regenv =
       match get_inst e with
       | If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else) ->
	  init_regenv (init_regenv regenv e_then) e_else
       | _ -> regenv in
     let unit_dests = List.filter (fun (x, t) -> t = Type.Unit) (get_dests e) in
     let regenv = M.add_list (List.map (fun (x, t) -> (x, reg_zero)) unit_dests) regenv in
     init_regenv regenv es

let rec select mg rset regenv = function
  | (ig, []) -> regenv
  | (ig, (x, adj_x)::stk) -> 
     let regenv = 
       if M.mem x regenv then
	 regenv
       else
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
	   let u = S.inter non_adj_regs move_regs in
	   let r = S.max_elt (if S.is_empty u then non_adj_regs else u) in
	   M.add x r regenv in
     let ig = UG.add_adj x adj_x ig in
     select mg rset regenv (ig, stk)

(* let rec spill_for_call  *)

let rec allocate regenv = function
  | [] -> []
  | e::es -> (allocate' regenv e)::(allocate regenv es)
and allocate' regenv (i, e, b) =
  let e' =
    match e with
    | Nop -> Nop
    | Ld((x, t), y, i) -> Ld((regfind x regenv, t), regfind y regenv, i)
    | St(x, y, i) -> St(regfind x regenv, regfind y regenv, i)
    | FLd((x, t), y, i) -> FLd((regfind x regenv, t), regfind y regenv, i)
    | FSt(x, y, i) -> FSt(regfind x regenv, regfind y regenv, i)
    | IToF((x, t), y) -> IToF((regfind x regenv, t), regfind y regenv)
    | FToI((x, t), y) -> FToI((regfind x regenv, t), regfind y regenv)
    | Neg((x, t), y) -> Neg((regfind x regenv, t), regfind y regenv)
    | Add((x, t), y, V(z)) -> Add((regfind x regenv, t), regfind y regenv, V(regfind z regenv))
    | Add((x, t), y, C(i)) -> Add((regfind x regenv, t), regfind y regenv,C(i))
    | Sub((x, t), y, z) -> Sub((regfind x regenv, t), regfind y regenv, regfind z regenv)
    | And((x, t), y, z) -> And((regfind x regenv, t), regfind y regenv, regfind z regenv)
    | Or((x, t), y, z) -> Or((regfind x regenv, t), regfind y regenv, regfind z regenv)
    | Li((x, t), i) -> Li((regfind x regenv, t), i)
    | Shl((x, t), y, V(z)) -> Shl((regfind x regenv, t), regfind y regenv, V(regfind z regenv))
    | Shl((x, t), y, C(i)) -> Shl((regfind x regenv, t), regfind y regenv, C(i))
    | Shr((x, t), y, V(z)) -> Shr((regfind x regenv, t), regfind y regenv, V(regfind z regenv))
    | Shr((x, t), y, C(i)) -> Shr((regfind x regenv, t), regfind y regenv, C(i))
    | FAdd((x, t), y, z) -> FAdd((regfind x regenv, t), regfind y regenv, regfind z regenv)
    | FSub((x, t), y, z) -> FSub((regfind x regenv, t), regfind y regenv, regfind z regenv)
    | FMul((x, t), y, z) -> FMul((regfind x regenv, t), regfind y regenv, regfind z regenv)
    | FInv((x, t), y) -> FInv((regfind x regenv, t), regfind y regenv)
    | FAbs((x, t), y) -> FAbs((regfind x regenv, t), regfind y regenv)
    | Sqrt((x, t), y) -> Sqrt((regfind x regenv, t), regfind y regenv)
    | FLi((x, t), f) -> FLi((regfind x regenv, t), f)
    | If((x, t), cond, (y, V(z)), e_then, e_else) -> If((regfind x regenv, t), cond, (regfind y regenv, V(regfind z regenv)), allocate regenv e_then, allocate regenv e_else)
    | If((x, t), cond, (y, C(i)), e_then, e_else) -> If((regfind x regenv, t), cond, (regfind y regenv, C(i)), allocate regenv e_then, allocate regenv e_else)
    | IfF((x, t), cond, (y, z), e_then, e_else) -> IfF((regfind x regenv, t), cond, (regfind y regenv, regfind z regenv), allocate regenv e_then, allocate regenv e_else)
    | Call((x, t), f, yts) -> Call((regfind x regenv, t), f, List.map (fun (y, t) -> (regfind y regenv, t)) yts)
    | LoadLabel((x, t), l) -> LoadLabel((regfind x regenv, t), l)
    | Mr((x, t), y) -> Mr((regfind x regenv, t), regfind y regenv)
    | FMr((x, t), y) -> FMr((regfind x regenv, t), regfind y regenv)
    | Save(x, s) -> Save(regfind x regenv, s)
    | Restore((x, t), s) -> Restore((regfind x regenv, t), s)
    | FSave(x, s) -> Save(regfind x regenv, s)
    | FRestore((x, t), s) -> Restore((regfind x regenv, t), s)
  in
  (i, e', b)

let rec g tl e = 
  let mps = Liveness.calc_live_main tl e in
  let igs = mk_igraph mps (UG.new_graph (), UG.new_graph ()) e in
  let mgs = mk_mgraph mps (UG.new_graph (), UG.new_graph ()) e in
  let igstks = tuple2_map3 simplify (Array.length regs, Array.length fregs) igs ([], []) in
  let (regenvi, regenvf) = tuple2_map4 select mgs (regset, fregset) (init_regenv M.empty e, M.empty) igstks in
  let regenv = M.fold (fun x r env -> M.add x r env) regenvi regenvf in
  let e = allocate regenv e in
  Format.eprintf "igraph ==================@.";
  UG.pp_graph (fst igs);
  UG.pp_graph (snd igs);
  Format.eprintf "mgraph ==================@.";
  UG.pp_graph (fst mgs);
  UG.pp_graph (snd mgs);
  Format.eprintf "regenv ==================@.";
  M.iter (fun x r -> Format.eprintf "%s -> %s@." x r) regenv;
  e

let h ({ name = Id.L(x); args = yts; body = e; ret = t }) =
  Format.eprintf "allocating register in %s@." x;
  let e' = g (Liveness.Tail (ret_reg t, t)) e in
  { name = Id.L(x); args = yts; body = e'; ret = t }

let f (Prog(fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  let fundefs' = List.map h fundefs in
  Format.eprintf "allocating register in main pocedure@.";
  let e' = g (Liveness.NonTail []) e in
  Prog(fundefs', e')
