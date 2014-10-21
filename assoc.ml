(* flatten let-bindings (just for prettier printing) *)

open KNormal

let rec f (r, e) = (* ネストしたletの簡約 (caml2html: assoc_f) *)
  let e' = match e with
    | IfEq(x, y, e1, e2) -> IfEq(x, y, f e1, f e2)
    | IfLE(x, y, e1, e2) -> IfLE(x, y, f e1, f e2)
    | Let(xt, e1, e2) -> (* letの場合 (caml2html: assoc_let) *)
       let rec insert (r'', e'') =
	 match e'' with
	 | Let(yt, e3, e4) -> (r'', Let(yt, e3, insert e4))
	 | LetRec(fundefs, e) -> (r'', LetRec(fundefs, insert e))
	 | LetTuple(yts, z, e) -> (r'', LetTuple(yts, z, insert e))
	 | e -> (r'', Let(xt, (r'', e), f e2)) in
       snd (insert (f e1))
    | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
       LetRec({ name = xt; args = yts; body = f e1 }, f e2)
    | LetTuple(xts, y, e) -> LetTuple(xts, y, f e)
    | e -> e
  in 
  (r, e')
