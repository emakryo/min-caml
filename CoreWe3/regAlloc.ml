open Asm

let rec get_args rs frs = function
  | [] -> []
  | (y, t)::yts ->
     match t with
     | Type.Unit -> get_args rs frs yts
     | Type.Float -> 
	(new_t (move_reg (y, t) (List.hd frs)))::(get_args rs (List.tl frs) yts)
     | _ -> 
	(new_t (move_reg (y, t) (List.hd rs)))::(get_args (List.tl rs) frs yts)

let rec set_args rs frs = function
  | [] -> []
  | (y, t)::yts ->
     match t with
     | Type.Unit -> set_args rs frs yts
     | Type.Float -> 
	(new_t (move_reg (List.hd frs, t) y))::(set_args rs (List.tl frs) yts)
     | _ -> 
	(new_t (move_reg (List.hd rs, t) y))::(set_args (List.tl rs) frs yts)

let rec map_args rs = function
  | [] -> []
  | (y, t)::yts ->
     match t with
     | Type.Unit -> map_args rs yts
     | _ -> (List.hd rs, t)::(map_args (List.tl rs) yts)

let prepare_for_call mps env es = (* 関数呼び出しをまたぐ変数について、save/restoreを挿入する*)
  let senv = ref M.empty in
  let insert_save e = 
    let liveouts = tuple2_map (Liveness.get_liveout e) mps in
    let dsets = Liveness.def_set e in
    let (livethroughi, livethroughf) = tuple2_map2 S.diff liveouts dsets in
    let non_livethroughs = (S.of_list ((List.map snd !constregs) @ special_regs), S.of_list (List.map snd !constfregs)) in
    let livethroughs = tuple2_map2 S.diff (livethroughi , livethroughf) non_livethroughs in
    let folder f x acc = (* すでにsaveしたことのあるものはsaveせずに、フラグだけ立てる。saveしたことのないものはsaveする。*)
      if M.mem x !senv then 
	(let (svar, _) = M.find x !senv in 
	 senv := M.add x (svar, true) !senv; acc)
      else 
	(let svar = Id.genid "stk" in
	 senv := M.add x (svar, true) !senv;
	 (new_t (f x svar))::acc) in
    let fs = ((fun x svar -> Save(x, svar)), (fun x svar -> FSave(x, svar))) in
    tuple2_map3 (fun f -> S.fold (folder f)) fs livethroughs ([], []) in
  let rec prepare_for_call_aux mps env = function
    | [] -> []
    | (i, e, b)::es ->
       let usets = Liveness.use_set (i, e, b) in
       let folder f x acc = (* すでにsaveされている && 最後の関数呼び出しからrestoreされたことがない ならflagをfalseにしてrestoreする。*)
	 if M.mem x !senv then 
	   let (svar, flag) = M.find x !senv in
	   if flag then 
	     (senv := M.add x (svar, false) !senv; 
	      (new_t (f x svar))::acc)
	   else acc 
	 else acc in
       let fs = ((fun x svar -> Restore((x, M.find x env), svar)),
		 (fun x svar -> FRestore((x, M.find x env), svar))) in
       let (rstri, rstrf) = tuple2_map3 (fun f -> S.fold (folder f)) fs usets ([], []) in
       let (savei, savef) =
	 match e with
	 | Call(_) | If(_) | IfF(_) ->
	    insert_save (i, e, b)
	 | e -> ([], []) in
       let elist =
	 match e with
	 | If(xt, cond, cmp, e_then, e_else) ->
	    let (e_then, e_else) = prepare_for_call_if mps env (e_else, e_then) in
	    [i, If(xt, cond, cmp, e_then, e_else), b]
	 | IfF(xt, cond, cmp, e_then, e_else) ->
	    let (e_then, e_else) = prepare_for_call_if mps env (e_else, e_then) in
	    [i, IfF(xt, cond, cmp, e_then, e_else), b]
	 | Call((x, t), f, yts, zts) ->
	    let sargs = set_args (reglist()) (freglist()) (yts @ zts) in
	    let gargs = get_args (reglist()) (freglist()) [x, t] in
	    let (rts, frts) = tuple2_map2 map_args (reglist(), freglist()) (yts, zts) in
	    sargs @ [i, Call((ret_reg t, t), f, rts, frts), b] @ gargs
	 | e -> [i, e, b] in
       let env = ext_env env (i, e, b) in
       savei @ savef @ rstri @ rstrf @ elist @ (prepare_for_call_aux mps env es)
  and prepare_for_call_if mps env (e_else, e_then) =
    let senv_back = !senv in
    let e_then = prepare_for_call_aux mps env e_then in
    let senv_then = !senv in
    senv := senv_back;
    let e_else = prepare_for_call_aux mps env e_else in
    let senv_else = !senv in
    senv := M.fold (fun x (sv, flag1) se -> 
		    if M.mem x senv_then then
		      let (sv, flag2) = M.find x senv_then in
		      M.add x (sv, flag1 || flag2) se
		    else se) senv_else M.empty;
    (e_then, e_else) in
  prepare_for_call_aux mps env es

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
     let igs = tuple2_map2 (S.fold (fun x ig -> UG.add_node x ig)) dsets igs in
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

let rec simplify spl k ig stk =
  let non_regs = S.filter (fun x -> not (is_reg x)) (UG.nodes ig) in
  if S.is_empty non_regs then
    (ig, stk)
  else
    let (ig, stk) = 
      let low_degs = S.filter (fun x -> UG.deg x ig < k) non_regs in
      if S.is_empty low_degs then
	(* let xc = let x = S.min_elt non_regs in (x, M.find x cst) in *)
	(* let (x, _) =  *)
	(* 	S.fold (fun y (x, c) ->  *)
	(* 		let d = M.find y cst in *)
	(* 		if d < c then (y, d) else (x, c)) *)
	(* 	       non_regs xc in *)
	let x = S.min_elt (S.diff non_regs spl) in
	let adj_x = UG.adj x ig in
	(UG.rm_node x ig, (x, adj_x)::stk)
      else
	S.fold (fun x (ig, stk) -> 
		let adj_x = UG.adj x ig in
		(UG.rm_node x ig, (x, adj_x)::stk)) 
	       low_degs (ig, stk) in
      simplify spl k ig stk

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

let mk_rstr x t sv =
  match t with 
  | Type.Unit -> Nop
  | Type.Float -> FRestore((x, t), sv)
  | _ -> Restore((x, t), sv)

let mk_save x t sv =
  match t with 
  | Type.Unit -> Nop
  | Type.Float -> FSave(x, sv)
  | _ -> Save(x, sv)

let rec insert_spill x sinfo = function 
  | [] -> []
  | (i, e, b)::es -> 
     let rstr = (*save命令以外でxが使用されていたら、直前にresroteを挿入*)
       let (usei, usef) = Liveness.use_set (i, e, b) in
       if S.mem x (S.union usei usef) then
	 match e, sinfo with 
	 | (Save(_) | FSave(_)), _ -> []
	 | _, None -> failwith (x^" is used before definiton?")
	 | _, Some(sv, t) -> [new_t (mk_rstr x t sv)]
       else [] in
     let (save, sinfo) = (* xが定義されていて、save済みでない時のみsaveする *)
       match get_dests (i, e, b), sinfo with
       | (y, t)::_ , None when x = y -> 
	  let sv = Id.genid "stk" in
	  ([new_t (mk_save x t sv)], Some(sv, t))
       | _, _ -> ([], sinfo) in
     let el = 
       match e with
       | Save(y, _) | FSave(y, _) | Restore((y, _), _) | FRestore((y, _), _) when x = y -> 
          []
       | If(xt, cond, cmp, e_then, e_else) ->
	  [i, If(xt, cond, cmp, insert_spill x sinfo e_then, insert_spill x sinfo e_else), b]
       | IfF(xt, cond, cmp, e_then, e_else) ->
	  [i, IfF(xt, cond, cmp, insert_spill x sinfo e_then, insert_spill x sinfo e_else), b]
       | e -> [i, e, b] in
     rstr @ el @ save @ (insert_spill x sinfo es)

let rec allocate regenv = function (* 変数名をレジスタで置き換える *)
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
    | Call((x, t), f, yts, zts) -> Call((regfind x regenv, t), f, List.map (fun (y, t) -> (regfind y regenv, t)) yts, List.map (fun (z, t) -> (regfind z regenv, t)) zts)
    | LoadLabel((x, t), l) -> LoadLabel((regfind x regenv, t), l)
    | Mr((x, t), y) -> Mr((regfind x regenv, t), regfind y regenv)
    | FMr((x, t), y) -> FMr((regfind x regenv, t), regfind y regenv)
    | Save(x, s) -> Save(regfind x regenv, s)
    | Restore((x, t), s) -> Restore((regfind x regenv, t), s)
    | FSave(x, s) -> FSave(regfind x regenv, s)
    | FRestore((x, t), s) -> FRestore((regfind x regenv, t), s)
  in
  (i, e', b)

let rec g env tl e = 
  let env = List.fold_left (fun env r -> M.add r Type.Int env) env special_regs in
  let env = List.fold_left (fun env (_, r) -> M.add r Type.Int env) env !constregs in
  let env = List.fold_left (fun env (_, r) -> M.add r Type.Float env) env !constfregs in
  let mps = Liveness.calc_live_main tl e in
  let e = prepare_for_call mps env e in
  let (regenv, e) = g' tl e S.empty in
  (regenv, e)
and g' tl e spl = 
  try
    let mps = Liveness.calc_live_main tl e in
    let igs = mk_igraph mps (UG.new_graph (), UG.new_graph ()) e in
    let mgs = mk_mgraph mps (UG.new_graph (), UG.new_graph ()) e in
    let igstks = tuple2_map3 (simplify spl) (Array.length (regs()), Array.length (fregs())) igs ([], []) in
    let (regenvi, regenvf) = tuple2_map4 select mgs (regset(), fregset()) (init_regenv M.empty e, M.empty) igstks in
    let regenv = M.fold (fun x r env -> M.add x r env) regenvi regenvf in
    let e = allocate regenv e in
    (* Format.eprintf "igraph ==================@."; *)
    (* UG.pp_graph (fst igs); *)
    (* UG.pp_graph (snd igs); *)
    (* Format.eprintf "mgraph ==================@."; *)
    (* UG.pp_graph (fst mgs); *)
    (* UG.pp_graph (snd mgs); *)
    (* Format.eprintf "regenv ==================@."; *)
    (* M.iter (fun x r -> Format.eprintf "%s -> %s@." x r) regenv; *)
    (regenv, e)
  with Spill(x) ->
    Format.eprintf "spill %s@." x;
    let e = insert_spill x None e in
    g' tl e (S.add x spl)

let h ({ name = Id.L(x); args = yts; fargs = zts; body = e; ret = t }) =
  Format.eprintf "allocating register in %s@." x;
  let env = M.add_list zts (M.add_list yts M.empty) in
  let e = (get_args (reglist()) (freglist()) (yts @ zts)) @ e in
  let (regenv, e) = g env (Liveness.Tail (ret_reg t, t)) e in
  let yts = List.map (fun (y, t) -> (M.find y regenv, t)) yts in
  let zts = List.map (fun (z, t) -> (M.find z regenv, t)) zts in
  { name = Id.L(x); args = yts; fargs = zts; body = e; ret = t }

let f (Prog(fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  let fundefs = List.map h fundefs in
  Format.eprintf "allocating register in main pocedure@.";
  let (_, e) = g M.empty (Liveness.NonTail []) e in
  Prog(fundefs, e)
