open Asm

let use_set e = (*各命令で使用される変数*)
  match get_inst e with
  | Nop | Li(_) | FLi(_) | LoadLabel(_) | Restore(_) -> 
     S.empty
  | Ld(_, x, _) | FLd(_, x, _) | IToF(_, x) | FToI(_, x) (* | IAsF(_, x) | FAsI(_, x) *) | Neg(_, x)  | FInv(_, x) | FAbs(_, x) | Sqrt(_, x) | Mr(_, x) | Save(x, _) | FMr(_, x) -> 
     S.singleton x
  | St(x, y, _) | FSt(x, y, _) | Sub(_, x, y) | And(_, x, y) | Or(_, x, y) | FAdd(_, x, y) | FSub(_, x, y) | FMul(_, x, y) | IfF(_, (x, y), _, _) -> 
     S.of_list [x; y]
  | Add(_, x, y') | Shl(_, x, y')| Shr(_, x, y') | If(_, (x, y'), _, _) -> 
     S.of_list (x::fv_id_or_imm y')
  | Call (_, _, xs) -> 
     S.of_list xs
let def_set e = (*各命令で定義される変数*)
  match get_inst e with
  | Nop | St(_) | FSt(_) | If(_) | IfF(_) | Save(_) ->
     S.empty
  | Ld(xt, _, _) | FLd(xt, _, _) | IToF(xt, _) | FToI(xt, _) | Neg(xt, _) | Add(xt, _, _) | Sub(xt, _, _) | And(xt, _, _) | Or(xt, _, _) | Li(xt, _) | Shl(xt, _, _) | Shr(xt, _, _) | FAdd(xt, _, _) | FSub(xt, _, _) | FMul(xt, _, _) | FInv(xt, _) | FAbs(xt, _) | Sqrt(xt, _) | FLi(xt, _) | Call(xt, _, _) | LoadLabel(xt, _) | Mr(xt, _) | FMr(xt, _) | Restore(xt, _) (* | IAsF(xt, _) | FAsI(xt, _) *) ->
     S.singleton (fst xt)

type liveset = S.t * S.t (*入口生存 * 出口生存*)
let get_livein e mp = if AM.mem e mp then fst (AM.find e mp) else S.empty
let get_liveout e mp = if AM.mem e mp then snd (AM.find e mp) else S.empty

type tail = Tail of Id.t | NonTail of t list

let rec take n = function
  | [] -> []
  | x::xs when n > 0 -> x::(take (n-1) xs)
  | _ -> []

let livein_of_ts mp es = 
  List.fold_left (fun s e -> S.union s (get_livein e mp)) S.empty (take 1 es)
let livein_of_tail mp = function 
  | Tail x -> S.singleton x
  | NonTail es -> livein_of_ts mp es     

let rec calc_live mp tl = function (*深さ優先で帰りがけ順に写像を更新*)
  | [] -> mp
  | [e] -> calc_live' mp tl e
  | e::es ->
     let mp = calc_live mp tl es in
     calc_live' mp (NonTail es) e
and calc_live' mp tl e = 
  let mp = 
    match get_inst e with
    | If(_, _, e_then, e_else) | IfF(_, _, e_then, e_else)->
       let mp = calc_live mp tl e_then in
       calc_live mp tl e_else
    | _ -> mp in
  let liveout = 
    match (tl, get_inst e) with
    | (_, (If(_, _, e_then, e_else) | IfF(_, _, e_then, e_else))) ->
       liveout_if mp tl e_then e_else
    | (tl, _) -> livein_of_tail mp tl in
  let livein = S.union (use_set e) (S.diff liveout (def_set e)) in (* use U (out \ def) *)  
  AM.add e (livein, liveout) mp
and liveout_if mp tl e_then e_else =
  match (e_then, e_else) with
  | ([], e) | (e, []) -> 
     S.union (livein_of_tail mp tl) (livein_of_ts mp e)
  | _ -> S.union (livein_of_ts mp e_then) (livein_of_ts mp e_else)

let rec emit_livemap mp = function
  | [] -> ()
  | (i, e, b)::es ->
     emit_livemap mp es;
     (match e with
      | If(_, _, e_then, e_else) | IfF(_, _, e_then, e_else) ->
         emit_livemap mp e_then; emit_livemap mp e_else
      | _ -> ());
     Format.eprintf "%d(in)  =%s@." i (S.fold (fun x acc -> acc^" "^x) (get_livein (i, e, b) mp) "");
     Format.eprintf "%d(out) =%s@." i (S.fold (fun x acc -> acc^" "^x) (get_liveout (i, e, b) mp) "")

let rec calc_live_iter mp tl e n =
  Format.eprintf "iteration %d...@." n;
  let mp' = calc_live mp tl e in
  emit_livemap mp' e;
  if mp = mp' then
    mp
  else
    calc_live_iter mp' tl e (n + 1)

let h { name = Id.L(x); args = _; body = e; ret = t } =
  Format.eprintf "Analysing liveness in %s...@." x;
  calc_live_iter AM.empty (Tail (ret_reg t)) e 1 

let g e =
  Format.eprintf "Analysing liveness in toplevel...@.";
  calc_live_iter AM.empty (NonTail []) e 1

