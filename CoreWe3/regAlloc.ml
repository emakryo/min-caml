open Asm

let h ({ name = Id.L(x); args = _; body = e; ret = t } as fdef) =
  let s = Liveness.h fdef in
  ()

let f (Prog(fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  List.iter h fundefs;  
  let s = Liveness.g e in  
  Prog(fundefs, e)
