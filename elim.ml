open KNormal

let rec compare_t (r1, e1) (r2, e2) = 
  if e1 = e2 then
    0
  else
    match e1, e2 with 
    | _, Unit -> 1
    | Unit, _ -> -1
    | Int x1, Int x2 -> compare x1 x2
    | _, Int _ -> 1
    | Int _, _ -> -1
    | Float x1, Float x2 -> compare x1 x2
    | _, Float _ -> 1
    | Float _, _ -> -1
    | Neg x1, Neg x2 -> compare x1 x2
    | _, Neg _ -> 1
    | Neg _, _ -> -1
    | Add (x1, y1), Add (x2, y2) -> if x1 <> x2 then compare x1 x2 else compare y1 y2
    | _, Add _ -> 1
    | Add _, _ -> -1
    | Sub (x1, y1), Sub (x2, y2) -> if x1 <> x2 then compare x1 x2 else compare y1 y2
    | _, Sub _ -> 1
    | Sub _, _ -> -1
    | Lsl (x1, y1), Lsl (x2, y2) -> if x1 <> x2 then compare x1 x2 else compare y1 y2
    | _, Lsl _ -> 1
    | Lsl _, _ -> -1
    | Lsr (x1, y1), Lsr (x2, y2) -> if x1 <> x2 then compare x1 x2 else compare y1 y2
    | _, Lsr _ -> 1
    | Lsr _, _ -> -1
    | FNeg x1, FNeg x2 -> compare x1 x2
    | _, FNeg _ -> 1
    | FNeg _, _ -> -1
    | FAdd (x1, y1), FAdd (x2, y2) -> if x1 <> x2 then compare x1 x2 else compare y1 y2
    | _, FAdd _ -> 1
    | FAdd _, _ -> -1
    | FSub (x1, y1), FSub (x2, y2) -> if x1 <> x2 then compare x1 x2 else compare y1 y2
    | _, FSub _ -> 1
    | FSub _, _ -> -1
    | FMul (x1, y1), FMul (x2, y2) -> if x1 <> x2 then compare x1 x2 else compare y1 y2
    | _, FMul _ -> 1
    | FMul _, _ -> -1
    | FDiv (x1, y1), FDiv (x2, y2) -> if x1 <> x2 then compare x1 x2 else compare y1 y2
    | _, FDiv _ -> 1
    | FDiv _, _ -> -1
    | IfEq (x1, y1, z1, w1), IfEq (x2, y2, z2, w2) -> if x1 <> x2 then compare x1 x2 else if y1 <> y2 then compare y1 y2 else let c = compare_t z1 z2 in if c <> 0 then c else compare_t w1 w2
    | _, IfEq _ -> 1
    | IfEq _, _ -> -1
    | IfLE (x1, y1, z1, w1), IfLE (x2, y2, z2, w2) -> if x1 <> x2 then compare x1 x2 else if y1 <> y2 then compare y1 y2 else let c = compare_t z1 z2 in if c <> 0 then c else compare_t w1 w2
    | _, IfLE _ -> 1
    | IfLE _, _ -> -1
    | Let ((x1, y1), z1, w1), Let ((x2, y2), z2, w2) -> if x1 <> x2 then compare x1 x2 else compare y1 y2
    | _, Let _ -> 1
    | Let _, _ -> -1
  (* | Let of (Id.t * Type.t) * t * t *)
  (* | Var of Id.t *)
  (* | LetRec of fundef * t *)
  (* | App of Id.t * Id.t list *)
  (* | Tuple of Id.t list *)
  (* | LetTuple of (Id.t * Type.t) list * Id.t * t *)
  (* | Get of Id.t * Id.t *)
  (* | Put of Id.t * Id.t * Id.t *)
  (* | ExtArray of Id.t *)
  (* | ExtFunApp of Id.t * Id.t list *)

module Em =
  Map.Make
    (struct
      type t = KNormal.t
      let compare = compare_t
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


let f t = elim_let t
