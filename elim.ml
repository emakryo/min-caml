open KNormal
 
let rec effect (r, e) = (* 副作用の有無 (caml2html: elim_effect) *)
  match e with
  | Let(_, e1, e2) | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> effect e1 || effect e2
  | LetRec(_, e) | LetTuple(_, _, e) -> effect e
  | App _ | Put _ | ExtFunApp _ -> true
  | _ -> false

let rec elim_let (r, e) =  (* 不要定義削除ルーチン本体 (caml2html: elim_f) *)
  let e' = match e with
    | IfEq(x, y, e1, e2) -> IfEq(x, y, elim_let e1, elim_let e2)
    | IfLE(x, y, e1, e2) -> IfLE(x, y, elim_let e1, elim_let e2)
    | Let((x, t), e1, e2) -> (* letの場合 (caml2html: elim_let) *)
       let e1' = elim_let e1 in
       let e2' = elim_let e2 in
       if effect e1' || S.mem x (fv e2') then Let((x, t), e1', e2') else
	 (Format.eprintf "eliminating variable %s@." x;
	  snd e2')
    | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let recの場合 (caml2html: elim_letrec) *)
       let e2' = elim_let e2 in
       if S.mem x (fv e2') then
	 LetRec({ name = (x, t); args = yts; body = elim_let e1 }, e2')
       else
	 (Format.eprintf "eliminating function %s@." x;
	  snd e2')
    | LetTuple(xts, y, e) ->
       let xs = List.map fst xts in
       let e' = elim_let e in
       let live = fv e' in
       if List.exists (fun x -> S.mem x live) xs then LetTuple(xts, y, e') else
	 (Format.eprintf "eliminating variables %s@." (Id.pp_list xs);
	  snd e')
    | e -> e
  in
  (r, e')

let f t = 
  let t' = elim_let t in
  t'
