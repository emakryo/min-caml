open Asm

let rec g env = function (* 命令列の 14 bit 即値最適化 *)
  | Ans(exp) -> Ans(g' env exp)
  | Let((x, t), Li(i), e) when (t = Type.Bool || t = Type.Int)  && (imm_min <= i) && (i < imm_max) ->
     let e' = g (M.add x (Int32.to_int i) env) e in
     if List.mem x (fv e') then Let((x, t), Li(i), e') else e'
  | Let(xt, exp, e) -> Let(xt, g' env exp, g env e)
and g' env = function (* 各命令の 14 bit 即値最適化 *)
  | Add(x, V(y)) when M.mem y env ->
     Add(x, C(M.find y env))
  | Add(x, V(y)) when M.mem x env ->
     Add(y, C(M.find x env))
  | Sub(x, y) when M.mem y env ->
     Add(x, C(-(M.find y env)))
  | Slw(x, V(y)) when M.mem y env ->
     Slw(x, C(M.find y env))
  | Srw(x, V(y)) when M.mem y env ->
     Srw(x, C(M.find y env))
  | IfEq(x, y, e1, e2) when M.mem y env && M.find y env = 0 -> 
     IfEq(x, reg_zero, g env e1, g env e2)
  | IfEq(x, y, e1, e2) when M.mem x env && M.find x env = 0 -> 
     IfEq(reg_zero, y, g env e1, g env e2)
  | IfEq(x, y, e1, e2) -> 
     IfEq(x, y, g env e1, g env e2)
  | IfLE(x, y, e1, e2) when M.mem y env && M.find y env = 0 -> 
     IfLE(x, reg_zero, g env e1, g env e2)
  | IfLE(x, y, e1, e2) when M.mem x env && M.find x env = 0 -> 
     IfLE(reg_zero, y, g env e1, g env e2)
  | IfLE(x, y, e1, e2) -> 
     IfLE(x, y, g env e1, g env e2)
  | IfFLE(x, y, e1, e2) when M.mem y env && M.find y env = 0 -> 
     IfFLE(x, reg_zero, g env e1, g env e2)
  | IfFLE(x, y, e1, e2) when M.mem x env && M.find x env = 0 -> 
     IfFLE(reg_zero, y, g env e1, g env e2)
  | IfFLE(x, y, e1, e2) -> 
     IfFLE(x, y, g env e1, g env e2)
  | e -> e

(* トップレベル関数の 14 bit 即値最適化 *)
let h { name = l; args = xs; body = e; ret = t } = 
  { name = l; args = xs; body = g M.empty e; ret = t }

(* プログラム全体の 14 bit 即値最適化 *)
let f (Prog(data, fundefs, e)) = 
  (* Prog(data, fundefs, e) *)
  Prog(data, List.map h fundefs, g M.empty e)
