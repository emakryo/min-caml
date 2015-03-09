open Asm

let rec g tl e =
  let mps = Liveness.calc_live_main tl e in
  g' mps e
and g' mps = function
  | [] -> []
  | (i, e, b)::es ->
     let elist = 
       match e with
       | Nop -> []
       | St(_) | FSt(_) | Save(_) | FSave(_) | Call(_) as e -> [i, e, b]
       | Mr((x, _), y) | FMr((x, _), y) when x == y  -> []
       | Ld(xt, _, _) | FLd(xt, _, _) | IToF(xt, _) | FToI(xt, _) | Neg(xt, _) | Add(xt, _, _) | Sub(xt, _, _) | And(xt, _, _) | Or(xt, _, _) | Li(xt, _) | Shl(xt, _, _) | Shr(xt, _, _) | FAdd(xt, _, _) | FSub(xt, _, _) | FMul(xt, _, _) | FInv(xt, _) | FAbs(xt, _) | Sqrt(xt, _) | FLi(xt, _) | LoadLabel(xt, _) | Mr(xt, _) | FMr(xt, _) | Restore(xt, _) | FRestore(xt, _) as e ->
          let liveouts = tuple2_map (Liveness.get_liveout (i, e, b)) mps in
	  let (livei, livef) = tuple2_map (S.mem (fst xt)) liveouts in
	  if livei || livef then [i, e, b] else []
       | If(dest, cnd, cmp, e_then, e_else) -> 
	  [(i, If(dest, cnd, cmp, g' mps e_then, g' mps e_else), b)]
       | IfF(dest, cnd, cmp, e_then, e_else) -> 
	  [(i, IfF(dest, cnd, cmp, g' mps e_then, g' mps e_else), b)] in
     elist @ (g' mps es)

(* トップレベル関数の 14 bit 即値最適化 *)
let h { name = l; args = yts; fargs = zts; body = e; ret = t } =
  { name = l; args = yts; fargs = zts; body = g (Liveness.Tail (ret_reg t, t)) e; ret = t }

(* プログラム全体の 14 bit 即値最適化 *)
let f (Prog(fundefs, e)) = 
  (Prog(fundefs, e))
  (* Prog(List.map h fundefs, g (Liveness.NonTail []) e) *)
