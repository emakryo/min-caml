(* give names to intermediate values (K-normalization) *)

type t = Id.range * ast(* K正規化後の式 (caml2html: knormal_t) *)
and ast =
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | Lsl of Id.t * Id.t
  | Lsr of Id.t * Id.t
  | Lor of Id.t * Id.t
  | Land of Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | FInv of Id.t
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.t
  | ExtTuple of Id.t
  | ExtFunApp of Id.t * Id.t list
  | Read 
  | Write of Id.t
  | Fasi of Id.t
  | Iasf of Id.t
  | Ftoi of Id.t
  | Itof of Id.t
  | Fabs of Id.t
  | Sqrt of Id.t
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let rec pp_t t =
  let indent d = String.make (2 * d) ' ' in
  let rec pp_t' d (r, t) =
    let sps = indent d in
    match t with
    | Unit -> Format.sprintf "()"
    | Int i -> Format.sprintf "%d" i
    | Float f -> Format.sprintf "%f" f
    | Neg n -> Format.sprintf "- %s" (Id.pp_t n)
    | Add (n1, n2) -> Format.sprintf "%s + %s" (Id.pp_t n1) (Id.pp_t n2)
    | Sub (n1, n2) -> Format.sprintf "%s - %s" (Id.pp_t n1) (Id.pp_t n2)
    | Lsl (n1, n2) -> Format.sprintf "%s lsl %s" (Id.pp_t n1) (Id.pp_t n2)
    | Lsr (n1, n2) -> Format.sprintf "%s lsr %s" (Id.pp_t n1) (Id.pp_t n2)
    | Lor (n1, n2) -> Format.sprintf "%s lor %s" (Id.pp_t n1) (Id.pp_t n2)
    | Land (n1, n2) -> Format.sprintf "%s land %s" (Id.pp_t n1) (Id.pp_t n2)
    | FNeg n -> Format.sprintf "-. %s" (Id.pp_t n)
    | FAdd (n1, n2) -> Format.sprintf "%s +. %s" (Id.pp_t n1) (Id.pp_t n2)
    | FSub (n1, n2) -> Format.sprintf "%s -. %s" (Id.pp_t n1) (Id.pp_t n2)
    | FMul (n1, n2) -> Format.sprintf "%s *. %s" (Id.pp_t n1) (Id.pp_t n2)
    | FDiv (n1, n2) -> Format.sprintf "%s /. %s" (Id.pp_t n1) (Id.pp_t n2)
    | FInv n -> Format.sprintf "1.0 /. %s" (Id.pp_t n)
    | IfEq (n1, n2, t1, t2) ->
       let s1 = (pp_t' (d + 1) t1) in
       let s1 = if String.contains s1 '\n' then s1 else (indent (d + 1)) ^ s1 in
       let s2 = (pp_t' (d + 1) t2) in
       let s2 = if String.contains s2 '\n' then s2 else (indent (d + 1)) ^ s2 in
       Format.sprintf "%sif %s = %s then\n%s\n%selse\n%s" sps (Id.pp_t n1) (Id.pp_t n2) s1 sps s2
    | IfLE (n1, n2, t1, t2) ->
       let s1 = (pp_t' (d + 1) t1) in
       let s1 = if String.contains s1 '\n' then s1 else (indent (d + 1)) ^ s1 in
       let s2 = (pp_t' (d + 1) t2) in
       let s2 = if String.contains s2 '\n' then s2 else (indent (d + 1)) ^ s2 in
       Format.sprintf "%sif %s <= %s then\n%s\n%selse\n%s" sps (Id.pp_t n1) (Id.pp_t n2) s1 sps s2
    | Let ((name, ty), t1, t2) ->
       let s1 = (pp_t' (d + 1) t1) in
       let s2 = (pp_t' d t2) in
       let s2 = if String.contains s2 '\n' then s2 else (indent d) ^ s2 in
       if String.contains s1 '\n' then
	 Format.sprintf "%slet %s (*%s*) = \n%s in\n%s" sps (Id.pp_t name) (Type.pp_t ty) s1 s2
       else
	 Format.sprintf "%slet %s (*%s*) = %s in\n%s" sps (Id.pp_t name) (Type.pp_t ty) s1 s2
    | Var n -> Format.sprintf "%s" (Id.pp_t n)
    | LetRec (fdef, t) ->
       let (fname, ty) = fdef.name in
       let args = String.concat " " (List.map (fun (name, _) -> Id.pp_t name) fdef.args) in
       let s1 = (pp_t' (d + 1) fdef.body) in
       let s2 = (pp_t' d t) in
       let s2 = if String.contains s2 '\n' then s2 else (indent d) ^ s2 in
       if String.contains s1 '\n' then
	 Format.sprintf "%slet rec %s (*%s*) %s =\n%s in\n%s" sps (Id.pp_t fname) (Type.pp_t ty) args s1 s2
       else
	 Format.sprintf "%slet rec %s (*%s*) %s = %s in\n%s" sps (Id.pp_t fname) (Type.pp_t ty) args s1 s2
    | App (n, ns) -> Format.sprintf "%s %s" (Id.pp_t n) (String.concat " " (List.map (fun m -> Id.pp_t m) ns))
    | Tuple ns -> Format.sprintf "%s" (String.concat ", " (List.map (fun m -> Id.pp_t m) ns))
    | LetTuple (xs, n, t) ->
       let names = String.concat ", " (List.map (fun (name, ty) -> Id.pp_t name) xs) in
       let ty = Type.Tuple (List.map (fun (name, ty) -> ty) xs) in
       let s2 = (pp_t' d t) in
       let s2 = if String.contains s2 '\n' then s2 else (indent d) ^ s2 in
       Format.sprintf "%slet (%s) (*%s*) = %s in\n%s" sps names (Type.pp_t ty) (Id.pp_t n) s2
    | Get (n1, n2) -> Format.sprintf "%s.(%s)" (Id.pp_t n1) (Id.pp_t n2)
    | Put (n1, n2, n3) -> Format.sprintf "%s.(%s) <- %s" (Id.pp_t n1) (Id.pp_t n2) (Id.pp_t n3)
    | ExtArray n -> Format.sprintf "%s" (Id.pp_t n)
    | ExtTuple n -> Format.sprintf "%s" (Id.pp_t n)
    | ExtFunApp (n, ns) -> Format.sprintf "%s %s" (Id.pp_t n) (String.concat " " (List.map (fun m -> Id.pp_t m) ns))
    | Read -> Format.sprintf "read_char ()"
    | Write n -> Format.sprintf "print_char %s" (Id.pp_t n)
    | Fasi n -> Format.sprintf "fasi %s" (Id.pp_t n)
    | Iasf n -> Format.sprintf "iasf %s" (Id.pp_t n)
    | Ftoi n -> Format.sprintf "ftoi %s" (Id.pp_t n)
    | Itof n -> Format.sprintf "itof %s" (Id.pp_t n)
    | Fabs n -> Format.sprintf "fabs %s" (Id.pp_t n)
    | Sqrt n -> Format.sprintf "sqrt %s" (Id.pp_t n)
  in
  Format.sprintf "%s\n" (pp_t' 0 t)

(* let rec pp_t t = *)
(*   let indent d = String.make (2 * d) ' ' in *)
(*   let rec pp_t' d (r, t) = *)
(*     let sps = indent d in *)
(*     let rng = Id.pp_range r in *)
(*     match t with *)
(*     | Unit -> *)
(*        Format.sprintf "%sUnit ()\t#%s\n" sps rng *)
(*     | Int i -> *)
(*        Format.sprintf "%sInt %d\t#%s\n" sps i rng *)
(*     | Float f -> *)
(*        Format.sprintf "%sFloat %f\t#%s\n" sps f rng *)
(*     | Neg n -> *)
(*        Format.sprintf "%sNeg %s\t#%s\n" sps (Id.pp_t n) rng *)
(*     | Add (n1, n2) -> *)
(*        Format.sprintf "%sAdd %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) rng *)
(*     | Sub (n1, n2) -> *)
(*        Format.sprintf "%sSub %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) rng *)
(*     | Lsl (n1, n2) -> *)
(*        Format.sprintf "%sLsl %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) rng *)
(*     | Lsr (n1, n2) -> *)
(*        Format.sprintf "%sLsr %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) rng *)
(*     | FNeg n -> *)
(*        Format.sprintf "%sFNeg %s\t#%s\n" sps (Id.pp_t n) rng *)
(*     | FAdd (n1, n2) -> *)
(*        Format.sprintf "%sFAdd %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) rng *)
(*     | FSub (n1, n2) -> *)
(*        Format.sprintf "%sFSub %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) rng *)
(*     | FMul (n1, n2) -> *)
(*        Format.sprintf "%sFMul %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) rng *)
(*     | FDiv (n1, n2) -> *)
(*        Format.sprintf "%sFDiv %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) rng *)
(*     | IfEq (n1, n2, t1, t2) -> *)
(*        Format.sprintf "%sIfEq %s %s\t#%s\n%s%sElse\n%s" sps (Id.pp_t n1) (Id.pp_t n2) rng (pp_t' (d + 1) t1) sps (pp_t' (d + 1) t2) *)
(*     | IfLE (n1, n2, t1, t2) -> *)
(*        Format.sprintf "%sIfLE %s %s\t#%s\n%s%sElse\n%s" sps (Id.pp_t n1) (Id.pp_t n2) rng (pp_t' (d + 1) t1) sps (pp_t' (d + 1) t2) *)
(*     | Let ((name, _), t1, t2) -> *)
(*        Format.sprintf "%sLet\t#%s\n%s%s\n%s%sIN\n%s" sps rng (indent (d + 1)) (Id.pp_t name) (pp_t' (d + 1) t1) sps (pp_t' d t2) *)
(*     | Var n -> *)
(*        Format.sprintf "%sVar %s\t#%s\n" sps (Id.pp_t n) rng *)
(*     | LetRec (fdef, t) -> *)
(*        Format.sprintf "%sLetRec\t#%s\n%s%sIN\n%s" sps rng (pp_fundef (d + 1) fdef) sps (pp_t' d t) *)
(*     | App (n, ns) -> *)
(*        Format.sprintf "%sApp %s (%s)\t#%s\n" sps (Id.pp_t n) (String.concat ", " (List.map (fun m -> Id.pp_t m) ns)) rng *)
(*     | Tuple ns -> *)
(*        Format.sprintf "%sTuple(%s)\t#%s\n" sps (String.concat ", " (List.map (fun m -> Id.pp_t m) ns)) rng *)
(*     | LetTuple (xs, n, t) -> *)
(*        let names = String.concat ", " (List.map (fun (name, _) -> Id.pp_t name) xs) in *)
(*        Format.sprintf "%sLetTuple (%s) %s\t#%s\n%sIN\n%s" sps names (Id.pp_t n) rng sps (pp_t' d t) *)
(*     | Get (n1, n2) -> *)
(*        Format.sprintf "%sGet %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) rng *)
(*     | Put (n1, n2, n3) -> *)
(*        Format.sprintf "%sGet %s %s %s\t#%s\n" sps (Id.pp_t n1) (Id.pp_t n2) (Id.pp_t n3) rng *)
(*     | ExtArray n -> *)
(*        Format.sprintf "%sExtArray %s\t#%s\n" sps (Id.pp_t n) rng *)
(*     | ExtFunApp (n, ns) -> *)
(*        Format.sprintf "%sExtFunApp %s (%s)\t#%s\n" sps (Id.pp_t n) (String.concat ", " (List.map (fun m -> Id.pp_t m) ns)) rng *)
(*   and pp_fundef d fdef = *)
(*     let sps = indent d in *)
(*     let args = String.concat ", " (List.map (fun (name, _) -> Id.pp_t name) fdef.args) in *)
(*     let (fname, _) = fdef.name in *)
(*     Format.sprintf "%s%s (%s)\n%s" sps (Id.pp_t fname) args (pp_t' d fdef.body) *)
(*   in *)
(*   pp_t' 0 t *)

let rec fv (r, t) =  (* 式に出現する（自由な）変数 (caml2html: knormal_fv) *)
  match t with
  | Unit | Int(_) | Float(_) | ExtArray(_) | ExtTuple(_) | Read -> S.empty
  | Neg(x) | FNeg(x) | FInv(x) | Write(x) | Fasi(x) | Iasf(x) | Ftoi(x) | Itof(x) | Fabs(x) | Sqrt(x) -> S.singleton x
  | Add(x, y) | Sub(x, y) | Lsl(x, y) | Lsr(x, y) | Lor(x, y) | Land(x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2) | IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
      let zs = S.diff (fv e1) (S.of_list (List.map fst yts)) in
      S.diff (S.union zs (fv e2)) (S.singleton x)
  | App(x, ys) -> S.of_list (x :: ys)
  | Tuple(xs) | ExtFunApp(_, xs) -> S.of_list xs
  | Put(x, y, z) -> S.of_list [x; y; z]
  | LetTuple(xs, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xs)))

let insert_let ((r, e), t) k = (* letを挿入する補助関数 (caml2html: knormal_insert) *)
  match e with
  | Var(x) -> k x
  | _ ->
     let x = Id.gentmp t in
     let e', t' = k x in
     (r, Let((x, t), (r, e), e')), t'
				     
let rec g env (r, e) = (* K正規化ルーチン本体 (caml2html: knormal_g) *)
  match e with
  | Syntax.Unit -> (r, Unit), Type.Unit
  | Syntax.Bool(b) -> (r, Int(if b then 1 else 0)), Type.Int (* 論理値true, falseを整数1, 0に変換 (caml2html: knormal_bool) *)
  | Syntax.Int(i) -> (r, Int(i)), Type.Int
  | Syntax.Float(d) -> (r, Float(d)), Type.Float
  | Syntax.Not(e) -> 
     g env (r, Syntax.If(e, (r, Syntax.Bool(false)), (r, Syntax.Bool(true))))
  | Syntax.Neg(e) ->
     insert_let (g env e)
		(fun x -> (r, Neg(x)), Type.Int)
  | Syntax.Add(e1, e2) -> (* 足し算のK正規化 (caml2html: knormal_add) *)
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, Add(x, y)), Type.Int))
  | Syntax.Sub(e1, e2) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, Sub(x, y)), Type.Int))
  | Syntax.Lsl(e1, e2) -> 
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, Lsl(x, y)), Type.Int))
  | Syntax.Lsr(e1, e2) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, Lsr(x, y)), Type.Int))
  | Syntax.Lor(e1, e2) -> 
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, Lor(x, y)), Type.Int))
  | Syntax.Land(e1, e2) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, Land(x, y)), Type.Int))
  | Syntax.FNeg(e) ->
     insert_let (g env e)
		(fun x -> (r, FNeg(x)), Type.Float)
  | Syntax.FAdd(e1, e2) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, FAdd(x, y)), Type.Float))
  | Syntax.FSub(e1, e2) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, FSub(x, y)), Type.Float))
  | Syntax.FMul(e1, e2) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, FMul(x, y)), Type.Float))
  | Syntax.FDiv(e1, e2) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> (r, FDiv(x, y)), Type.Float))
  | Syntax.Eq _ | Syntax.LE _ as cmp ->
		   g env (r, Syntax.If((r, cmp), (r, Syntax.Bool(true)), (r, Syntax.Bool(false))))
  | Syntax.If((r1, Syntax.Not(e1)), e2, e3) -> 
     g env (r, Syntax.If(e1, e3, e2)) (* notによる分岐を変換 (caml2html: knormal_not) *)
  | Syntax.If((r1, Syntax.Eq(e1, e2)), e3, e4) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y ->
				      let e3', t3 = g env e3 in
				      let e4', t4 = g env e4 in
				      (r, IfEq(x, y, e3', e4')), t3))
  | Syntax.If((r1, Syntax.LE(e1, e2)), e3, e4) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y ->
				      let e3', t3 = g env e3 in
				      let e4', t4 = g env e4 in
				      (r, IfLE(x, y, e3', e4')), t3))
  | Syntax.If(e1, e2, e3) -> 
     let r1 = Syntax.get_range e1 in
     g env (r, Syntax.If((r1, Syntax.Eq(e1, (r1, Syntax.Bool(false)))), e3, e2)) (* 比較のない分岐を変換 (caml2html: knormal_if) *)
  | Syntax.Let((x, t), e1, e2) ->
     let e1', t1 = g env e1 in
     let e2', t2 = g (M.add x t env) e2 in
     (r, Let((x, t), e1', e2')), t2
  | Syntax.Var(x) when M.mem x env -> (r, Var(x)), M.find x env
  | Syntax.Var(x) -> (* 外部配列の参照 (caml2html: knormal_extarray) *)
     (match M.find x !Typing.extenv with
      | Type.Array(_) as t -> (r, ExtArray x), t
      | Type.Tuple(_) as t -> (r, ExtTuple x), t
      | _ -> failwith (Printf.sprintf "external variable %s at %s does not have an array or tuple type" x (Id.pp_range r)))
  | Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2) ->
     let env' = M.add x t env in
     let e2', t2 = g env' e2 in
     let e1', t1 = g (M.add_list yts env') e1 in
     (r, LetRec({ name = (x, t); args = yts; body = e1' }, e2')), t2
  | Syntax.App((r1, Syntax.Var(f)), e2s) when not (M.mem f env) -> (* 外部関数の呼び出し (caml2html: knormal_extfunapp) *)
     (match M.find f !Typing.extenv with
      | Type.Fun(_, t) ->
	 let rec bind xs = function (* "xs" are identifiers for the arguments *)
	   | [] -> (r, ExtFunApp(f, xs)), t
	   | e2 :: e2s ->
	      insert_let (g env e2)
			 (fun x -> bind (xs @ [x]) e2s) in
	 bind [] e2s (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.App(e1, e2s) ->
     (match g env e1 with
      | _, Type.Fun(_, t) as g_e1 ->
	 insert_let g_e1
		    (fun f ->
		     let rec bind xs = function (* "xs" are identifiers for the arguments *)
		       | [] -> (r, App(f, xs)), t
		       | e2 :: e2s ->
			  insert_let (g env e2)
				     (fun x -> bind (xs @ [x]) e2s) in
		     bind [] e2s) (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.Tuple(es) ->
     let rec bind xs ts = function (* "xs" and "ts" are identifiers and types for the elements *)
       | [] -> (r, Tuple(xs)), Type.Tuple(ts)
       | e :: es ->
	  let _, t as g_e = g env e in
	  insert_let g_e
		     (fun x -> bind (xs @ [x]) (ts @ [t]) es) in
     bind [] [] es
  | Syntax.LetTuple(xts, e1, e2) ->
     insert_let (g env e1)
		(fun y ->
		 let e2', t2 = g (M.add_list xts env) e2 in
		 (r, LetTuple(xts, y, e2')), t2)
  | Syntax.Array(e1, e2) ->
     insert_let (g env e1)
		(fun x ->
		 let _, t2 as g_e2 = g env e2 in
		 insert_let g_e2
			    (fun y ->
			     let l =
			       match t2 with
			       | Type.Float -> "create_float_array"
			       | _ -> "create_array" in
			     (r, ExtFunApp(l, [x; y])), Type.Array(t2)))
  | Syntax.Get(e1, e2) ->
     (match g env e1 with
      |	_, Type.Array(t) as g_e1 ->
	 insert_let g_e1
		    (fun x -> insert_let (g env e2)
					 (fun y -> (r, Get(x, y)), t))
      | _ -> assert false)
  | Syntax.Put(e1, e2, e3) ->
     insert_let (g env e1)
		(fun x -> insert_let (g env e2)
				     (fun y -> insert_let (g env e3)
							  (fun z -> (r, Put(x, y, z)), Type.Unit)))
  | Syntax.Read (e) -> 
     insert_let (g env e)
		(fun x -> (r, Read), Type.Int)
  | Syntax.Write (e) -> 
     insert_let (g env e)
		(fun x -> (r, Write (x)), Type.Unit)
  | Syntax.Fasi (e) -> 
     insert_let (g env e)
		(fun x -> (r, Fasi (x)), Type.Int)
  | Syntax.Iasf (e) -> 
     insert_let (g env e)
		(fun x -> (r, Iasf (x)), Type.Float)
  | Syntax.Ftoi (e) -> 
     insert_let (g env e)
		(fun x -> (r, Ftoi (x)), Type.Int)
  | Syntax.Itof (e) -> 
     insert_let (g env e)
		(fun x -> (r, Itof (x)), Type.Float)
  | Syntax.Fabs (e) -> 
     insert_let (g env e)
		(fun x -> (r, Fasi (x)), Type.Float)
  | Syntax.Sqrt (e) -> 
     insert_let (g env e)
		(fun x -> (r, Iasf (x)), Type.Float)

let f e = 
  let s = fst (g M.empty e) in
  print_string "(* =====kNormalized===== *)\n";
  print_string (pp_t s);
  s

