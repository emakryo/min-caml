open Asm

let tuple2_map f (x, y) = (f x, f y)
let tuple2_map2 f (x1, y1) (x2, y2) = (f x1 x2, f y1 y2)

let partition_by_type env s = 
  S.partition (fun x -> Type.isn't_float (M.find x env))  s  

let use_set env e = (*各命令で使用される変数*)
  let s = 
    match get_inst e with
    | Nop | Li(_) | FLi(_) | LoadLabel(_) | Restore(_) | FRestore(_)->
       S.empty
    | Ld(_, x, _) | IToF(_, x) | Neg(_, x)  | Mr(_, x) | Save(x, _) | FLd(_, x, _) | FToI(_, x) | FInv(_, x) | FAbs(_, x) | Sqrt(_, x) | FMr(_, x) | FSave(_, x) ->
       S.singleton x
    | St(x, y, _) | Sub(_, x, y) | And(_, x, y) | Or(_, x, y) | FSt(x, y, _) | FAdd(_, x, y) | FSub(_, x, y) | FMul(_, x, y) | IfF(_, _, (x, y), _, _) ->
       S.of_list [x; y]
    | Add(_, x, y') | Shl(_, x, y')| Shr(_, x, y') | If(_, _, (x, y'), _, _) ->
       S.of_list (x::fv_id_or_imm y')
    | Call (_, _, xts) ->
       S.of_list (List.map fst xts) in
  partition_by_type env s  

let def_set env e = (*各命令で定義される変数*)
  let s = 
    match get_inst e with
    | Nop | St(_) | FSt(_) | If(_) | IfF(_) | Save(_) | FSave(_) ->
       S.empty
    | Ld(xt, _, _) | FLd(xt, _, _) | IToF(xt, _) | FToI(xt, _) | Neg(xt, _) | Add(xt, _, _) | Sub(xt, _, _) | And(xt, _, _) | Or(xt, _, _) | Li(xt, _) | Shl(xt, _, _) | Shr(xt, _, _) | FAdd(xt, _, _) | FSub(xt, _, _) | FMul(xt, _, _) | FInv(xt, _) | FAbs(xt, _) | Sqrt(xt, _) | FLi(xt, _) | Call(xt, _, _) | LoadLabel(xt, _) | Mr(xt, _) | FMr(xt, _) | Restore(xt, _) | FRestore(xt, _) ->
       S.singleton (fst xt) in
  partition_by_type env s

type liveset = S.t * S.t (*入口生存 * 出口生存*)
let get_livein e mp = if AM.mem e mp then fst (AM.find e mp) else S.empty
let get_liveout e mp = if AM.mem e mp then snd (AM.find e mp) else S.empty

type tail = Tail of Id.t | NonTail of t list

let rec take n = function
  | [] -> []
  | x::xs when n > 0 -> x::(take (n-1) xs)
  | _ -> []

let livein_of_ts mps es =
  List.fold_left (fun sets e ->
		  let liveins = tuple2_map (get_livein e) mps in
		  tuple2_map2 S.union sets liveins)
		 (S.empty, S.empty) (take 1 es)
let livein_of_tail mps env = function
  | Tail x ->  partition_by_type env (S.singleton x)
  | NonTail es -> livein_of_ts mps es

let rec calc_live mps env tl = function (*深さ優先で帰りがけ順に写像を更新*)
  | [] -> mps
  | [e] -> calc_live' mps env tl e
  | e::es ->
     let env' = ext_env env e in
     let mps = calc_live mps env' tl es in
     calc_live' mps env (NonTail es) e
and calc_live' mps env tl e =
  let mps =
    match get_inst e with
    | If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else)->
       let mps = calc_live mps env tl e_then in
       calc_live mps env tl e_else
    | _ -> mps in
  let env = ext_env env e in
  let liveouts  =
    match (tl, get_inst e) with
    | (_, (If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else))) ->
       liveout_if mps env tl e_then e_else
    | (tl, _) -> livein_of_tail mps env tl in
  let liveins =
    let use_sets = use_set env e in
    let def_sets = def_set env e in
    tuple2_map2 S.union use_sets (tuple2_map2 S.diff liveouts def_sets) in
  let livesets = tuple2_map2 (fun x y -> (x, y)) liveins liveouts in
  tuple2_map2 (AM.add e) livesets mps
and liveout_if mps env tl e_then e_else =
  match (e_then, e_else) with
  | ([], e) | (e, []) ->
     tuple2_map2 S.union (livein_of_tail mps env tl) (livein_of_ts mps e)
  | _ -> tuple2_map2 S.union (livein_of_ts mps e_then) (livein_of_ts mps e_else)

let rec emit_livemap mps = function
  | [] -> ()
  | (i, e, b)::es ->
     emit_livemap mps es;
     (match e with
      | If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else) ->
         emit_livemap mps e_then; emit_livemap mps e_else
      | _ -> ());
     let (mpi, mpf) = mps in
     let ini_s = String.concat "; " (S.to_list (get_livein (i, e, b) mpi)) in
     let outi_s = String.concat "; " (S.to_list (get_liveout (i, e, b) mpi)) in
     let inf_s = String.concat "; " (S.to_list (get_livein (i, e, b) mpf)) in
     let outf_s = String.concat "; " (S.to_list (get_liveout (i, e, b) mpf)) in
     Format.eprintf "in[%d]  = {int: {in: [%s], out: [%s]}, float: {in: [%s], out: [%s]}}@." i ini_s outi_s inf_s outf_s

let rec calc_live_iter mps env tl e n =
  Format.eprintf "iteration %d...@." n;
  let mps' = calc_live mps env tl e in
  emit_livemap mps' e;
  if mps = mps' then
    mps
  else
    calc_live_iter mps' env tl e (n + 1)

let h { name = Id.L(x); args = yts; body = e; ret = t } =
  Format.eprintf "Analysing liveness in %s...@." x;
  let env = M.add_list yts M.empty in
  calc_live_iter (AM.empty, AM.empty) env (Tail (ret_reg t)) e 1

let g e =
  Format.eprintf "Analysing liveness in toplevel...@.";
  calc_live_iter (AM.empty, AM.empty) M.empty (NonTail []) e 1

