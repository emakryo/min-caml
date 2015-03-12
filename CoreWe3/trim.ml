open Asm

let rec g = function
  | [] -> []
  | (i, e, b)::es ->
     let elist = 
       match e with
       | Nop -> []
       | Mr((x, _), y) | FMr((x, _), y) when x == y  -> []
       | If(dest, cnd, cmp, e_then, e_else) -> 
	  [(i, If(dest, cnd, cmp, g e_then, g e_else), b)]
       | IfF(dest, cnd, cmp, e_then, e_else) -> 
	  [(i, IfF(dest, cnd, cmp, g e_then, g e_else), b)] 
       | _ -> [i, e, b] in
     elist @ (g es)

(* トップレベル関数の 14 bit 即値最適化 *)
let h { name = l; args = yts; fargs = zts; body = e; ret = t } =
  { name = l; args = yts; fargs = zts; body = g e; ret = t }

(* プログラム全体の 14 bit 即値最適化 *)
let f (Prog(fundefs, e)) = 
  (* Prog(fundefs, e) *)
  Prog(List.map h fundefs, g e)
