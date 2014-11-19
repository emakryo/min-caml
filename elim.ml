open KNormal
 
module Em =
  Map.Make
    (struct
      type t = KNormal.t
      let compare = compare
    end)
include Em

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

let rec sanitize (r, e) = (*kNormal.astのみを比較できるように、rangeを無効化*)
  let e' = match e with
    | Unit | Int(_) | Float(_) | Neg(_) | Add(_) | Sub(_) | Lsl(_) | Lsr(_) | FNeg(_) | FAdd(_) | FSub(_) | FMul(_) | FDiv(_) | Var(_) | App(_) | Tuple(_) | Get(_) | Put(_) | ExtArray(_) | ExtTuple(_) | ExtFunApp(_) -> e
    | IfEq (n1, n2, t1, t2) -> IfEq (n1, n2, sanitize t1, sanitize t2)
    | IfLE (n1, n2, t1, t2) -> IfLE (n1, n2, sanitize t1, sanitize t2)
    | Let ((n, ty), t1, t2) -> Let ((n, ty), sanitize t1, sanitize t2)
    | LetRec ({name = (n, ty); args = ags; body = b}, t) -> LetRec ({name = (n, ty); args = ags; body = sanitize b}, sanitize t)
    | LetTuple (xs, n, t) -> LetTuple (xs, n, sanitize t)
  in
  (((0,0),(0,0)), e')

let rec isnt_eliminatable (r, e) = 
  match e with
  | Let(_, e1, e2) | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> isnt_eliminatable e1 || isnt_eliminatable e2
  | LetRec(_, e) | LetTuple(_, _, e) -> isnt_eliminatable e
  | App _ | Get _ | Put _ | ExtFunApp _ -> true
  | _ -> false

let is_simple_exp (r, e) = 
  match e with
  | Unit | Int(_) | Float(_) -> true
  | Var(_) | ExtArray(_) | ExtTuple(_) -> true
  | _ -> false

let rec elim_exp env (r, e) = (*共通部分式除去*)
  let e' = 
    try 
      let n = Em.find (sanitize (r, e)) env in
      Format.eprintf "replacing follewing expression at %s with variable \"%s\".\n%s" (Id.pp_range r) (Id.pp_t n) (pp_t (r, e));
      Var(n)
    with 
      Not_found -> 
      match e with
      | Unit | Int(_) | Float(_) | Neg(_) | Add(_) | Sub(_) | Lsl(_) | Lsr(_) | FNeg(_) | FAdd(_) | FSub(_) | FMul(_) | FDiv(_) | Var(_) | App(_) | Tuple(_) | Get(_) | Put(_) | ExtArray(_) | ExtTuple(_) | ExtFunApp(_) -> e
      | IfEq (n1, n2, t1, t2) -> IfEq (n1, n2, elim_exp env t1, elim_exp env t2)
      | IfLE (n1, n2, t1, t2) -> IfLE (n1, n2, elim_exp env t1, elim_exp env t2)
      | Let ((n, t), t1, t2) -> 
	 let t1' = elim_exp env t1 in
	 if isnt_eliminatable t1' || is_simple_exp t1' then 
	   Let ((n, t), t1', elim_exp env t2)
	 else
	   let env' = Em.add (sanitize t1') n env in
	   Let ((n, t), t1', elim_exp env' t2)
      | LetRec ({name = (n, ty); args = ags; body = b}, t) -> 
	 LetRec ({name = (n, ty); args = ags; body = elim_exp (Em.empty) b}, elim_exp env t)
      | LetTuple (xs, n, t) -> LetTuple (xs, n, elim_exp env t)
  in
  (r, e')

let f t = 
  let t' = elim_let t in
  let t' = elim_exp (Em.empty) t' in
  t'
