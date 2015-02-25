open Asm

let use_set e = (*各命令で使用される変数*)
  match get_inst e with
  | Nop | Li(_) | FLi(_) | LoadLabel(_) | Restore(_) | FRestore(_)->
     (S.empty, S.empty)
  | Ld(_, x, _) | IToF(_, x) | Neg(_, x)  | Mr(_, x) | Save(x, _) | FLd(_, x, _) ->
     (S.singleton x, S.empty)
  | FToI(_, x) | FInv(_, x) | FAbs(_, x) | Sqrt(_, x) | FMr(_, x) | FSave(x, _) ->
     (S.empty, S.singleton x)
  | St(x, y, _) | Sub(_, x, y) | And(_, x, y) | Or(_, x, y) ->
     (S.of_list [x; y], S.empty)
  | FAdd(_, x, y) | FSub(_, x, y) | FMul(_, x, y) | IfF(_, _, (x, y), _, _) ->
     (S.empty, S.of_list [x; y])
  | FSt(x, y, _) ->
     (S.singleton y, S.singleton x)
  | Add(_, x, y') | Shl(_, x, y')| Shr(_, x, y') | If(_, _, (x, y'), _, _) ->
     (S.of_list (x::fv_id_or_imm y'), S.empty)
  | Call (_, _, xts) ->
     let xtss = List.partition (fun (x, t) -> Type.isn't_float t) xts in
     let xss = tuple2_map (List.map fst) xtss in
     tuple2_map S.of_list xss

let def_set e = (*各命令で定義される変数*)
  match get_inst e with
  | Nop | St(_) | FSt(_) | If(_) | IfF(_) | Save(_) | FSave(_) ->
     (S.empty, S.empty)
  | Ld(xt, _, _) | FLd(xt, _, _) | IToF(xt, _) | FToI(xt, _) | Neg(xt, _) | Add(xt, _, _) | Sub(xt, _, _) | And(xt, _, _) | Or(xt, _, _) | Li(xt, _) | Shl(xt, _, _) | Shr(xt, _, _) | FAdd(xt, _, _) | FSub(xt, _, _) | FMul(xt, _, _) | FInv(xt, _) | FAbs(xt, _) | Sqrt(xt, _) | FLi(xt, _) | Call(xt, _, _) | LoadLabel(xt, _) | Mr(xt, _) | FMr(xt, _) | Restore(xt, _) | FRestore(xt, _) ->
     if Type.isn't_float (snd xt) then
       (S.singleton (fst xt), S.empty)
     else
       (S.empty, S.singleton (fst xt))
	   
type liveset = S.t * S.t (*入口生存 * 出口生存*)
let get_livein e mp = if AM.mem e mp then fst (AM.find e mp) else S.empty
let get_liveout e mp = if AM.mem e mp then snd (AM.find e mp) else S.empty

type tail = Tail of (Id.t * Type.t) | NonTail of t list

let rec take n = function
  | [] -> []
  | x::xs when n > 0 -> x::(take (n-1) xs)
  | _ -> []

let livein_of_ts mps es =
  List.fold_left (fun sets e ->
		  let liveins = tuple2_map (get_livein e) mps in
		  tuple2_map2 S.union sets liveins)
		 (S.empty, S.empty) (take 1 es)
let livein_of_tail mps = function
  | Tail xt -> 
     if Type.isn't_float (snd xt) then
       (S.singleton (fst xt), S.empty)
     else
       (S.empty, S.singleton (fst xt))
  | NonTail es -> livein_of_ts mps es

let rec calc_live mps tl = function (*深さ優先で帰りがけ順に写像を更新*)
  | [] -> mps
  | [e] -> calc_live' mps tl e
  | e::es ->
     let mps = calc_live mps tl es in
     calc_live' mps (NonTail es) e
and calc_live' mps tl e =
  let mps =
    match get_inst e with
    | If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else)->
       let mps = calc_live mps tl e_then in
       calc_live mps tl e_else
    | _ -> mps in
  let liveouts  =
    match (tl, get_inst e) with
    | (_, (If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else))) ->
       liveout_if mps tl e_then e_else
    | (tl, _) -> livein_of_tail mps tl in
  let liveins =
    let use_sets = use_set e in
    let def_sets = def_set e in
    tuple2_map2 S.union use_sets (tuple2_map2 S.diff liveouts def_sets) in
  let livesets = tuple2_map2 (fun x y -> (x, y)) liveins liveouts in
  tuple2_map2 (AM.add e) livesets mps
and liveout_if mps tl e_then e_else =
  match (e_then, e_else) with
  | ([], e) | (e, []) ->
     tuple2_map2 S.union (livein_of_tail mps tl) (livein_of_ts mps e)
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

let rec calc_live_iter mps tl e n =
  Format.eprintf "iteration %d...@." n;
  let mps' = calc_live mps tl e in
  emit_livemap mps' e;
  if mps = mps' then
    mps
  else
    calc_live_iter mps' tl e (n + 1)

let h { name = Id.L(x); args = yts; body = e; ret = t } =
  Format.eprintf "Analysing liveness in %s...@." x;
  calc_live_iter (AM.empty, AM.empty) (Tail (ret_reg t, t)) e 1

let g e =
  Format.eprintf "Analysing liveness in toplevel...@.";
  calc_live_iter (AM.empty, AM.empty) (NonTail []) e 1

