open Asm

let use_set (_, e, _) = 
  match e with
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

let def_set (_, e, _) =
  match e with
  | Nop | St(_) | FSt(_) | If(_) | IfF(_) | Save(_) ->
     S.empty
  | Ld(xt, _, _) | FLd(xt, _, _) | IToF(xt, _) | FToI(xt, _) | Neg(xt, _) | Add(xt, _, _) | Sub(xt, _, _) | And(xt, _, _) | Or(xt, _, _) | Li(xt, _) | Shl(xt, _, _) | Shr(xt, _, _) | FAdd(xt, _, _) | FSub(xt, _, _) | FMul(xt, _, _) | FInv(xt, _) | FAbs(xt, _) | Sqrt(xt, _) | FLi(xt, _) | Call(xt, _, _) | LoadLabel(xt, _) | Mr(xt, _) | FMr(xt, _) | Restore(xt, _) (* | IAsF(xt, _) | FAsI(xt, _) *) ->
     S.singleton (fst xt)

let f (Prog(fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  Prog(fundefs, e)
