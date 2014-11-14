open Asm

let rec g env = function (* ̿����� 16 bit ¨�ͺ�Ŭ�� *)
  | Ans(exp) -> Ans(g' env exp)
  | Let((x, t), Li(i), e) when ((t = Type. Int) || (t = Type.Bool)) && (imm_min <= i) && (i < imm_max) -> 
     let e' = g (M.add x (Int32.to_int i) env) e in
     if List.mem x (fv e') then Let((x, t), Li(i), e') else e'
  | Let(xt, exp, e) -> Let(xt, g' env exp, g env e)
and g' env = function (* ��̿��� 16 bit ¨�ͺ�Ŭ�� *)
  | Add(x, V(y)) when M.mem y env -> Add(x, C(M.find y env))
  | Add(x, V(y)) when M.mem x env -> Add(y, C(M.find x env))
  | Sub(x, y) when M.mem y env -> Add(x, C(-(M.find y env)))
  | Slw(x, V(y)) when M.mem y env -> Slw(x, C(M.find y env))
  | Srw(x, V(y)) when M.mem y env -> Slw(x, C(M.find y env))
  | IfEq(x, y', e1, e2) -> IfEq(x, y', g env e1, g env e2)
  | IfLE(x, y', e1, e2) -> IfLE(x, y', g env e1, g env e2)
  | IfFLE(x, y', e1, e2) -> IfFLE(x, y', g env e1, g env e2)
  | e -> e

(* �ȥåץ�٥�ؿ��� 16 bit ¨�ͺ�Ŭ�� *)
let h { name = l; args = xs; body = e; ret = t } = 
  { name = l; args = xs; body = g M.empty e; ret = t }

(* �ץ�������Τ� 16 bit ¨�ͺ�Ŭ�� *)
let f (Prog(data, fundefs, e)) = 
  Prog(data, List.map h fundefs, g M.empty e)
