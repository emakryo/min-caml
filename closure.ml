type closure = { entry : Id.l; actual_fv : Id.t list }
type t = Id.range * ast
and ast = (* ���������Ѵ���μ� (caml2html: closure_t) *)
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
  | FInv of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | MakeCls of (Id.t * Type.t) * closure * t
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.l
  | ExtTuple of Id.l
  | Read
  | Write of Id.t
  | Fasi of Id.t
  | Iasf of Id.t
  | Ftoi of Id.t
  | Itof of Id.t
  | Fabs of Id.t
  | Sqrt of Id.t
type fundef = { name : Id.l * Type.t;
		args : (Id.t * Type.t) list;
		formal_fv : (Id.t * Type.t) list;
		body : t }
type prog = Prog of fundef list * t

let rec pp_t t d =
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
    | FInv n -> Format.sprintf "1.0 /. %s" (Id.pp_t n)
    | FAdd (n1, n2) -> Format.sprintf "%s +. %s" (Id.pp_t n1) (Id.pp_t n2)
    | FSub (n1, n2) -> Format.sprintf "%s -. %s" (Id.pp_t n1) (Id.pp_t n2)
    | FMul (n1, n2) -> Format.sprintf "%s *. %s" (Id.pp_t n1) (Id.pp_t n2)
    | FDiv (n1, n2) -> Format.sprintf "%s /. %s" (Id.pp_t n1) (Id.pp_t n2)
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
    | MakeCls((x, t), { entry = Id.L(l); actual_fv = zs }, e2') ->
       let fvs = String.concat " "  zs in
       let s2 = (pp_t' d e2') in
       let s2 = if String.contains s2 '\n' then s2 else (indent d) ^ s2 in
       Format.sprintf "%slet %s (*%s*) = <closure_%s{%s}> in\n%s" sps (Id.pp_t x) (Type.pp_t t) l fvs s2
    | AppCls (n, args) -> Format.sprintf "closure_%s %s" (Id.pp_t n) (String.concat " " (List.map (fun m -> Id.pp_t m) args))
    | AppDir (Id.L l, args) ->Format.sprintf "%s %s" (Id.pp_t l) (String.concat " " (List.map (fun m -> Id.pp_t m) args))
    | Tuple ns -> Format.sprintf "(%s)" (String.concat ", " (List.map (fun m -> Id.pp_t m) ns))
    | LetTuple (xs, n, t) ->
       let names = String.concat ", " (List.map (fun (name, ty) -> Id.pp_t name) xs) in
       let ty = Type.Tuple (List.map (fun (name, ty) -> ty) xs) in
       let s2 = (pp_t' d t) in
       let s2 = if String.contains s2 '\n' then s2 else (indent d) ^ s2 in
       Format.sprintf "%slet (%s) (*%s*) = %s in\n%s" sps names (Type.pp_t ty) (Id.pp_t n) s2
    | Get (n1, n2) -> Format.sprintf "%s.(%s)" (Id.pp_t n1) (Id.pp_t n2)
    | Put (n1, n2, n3) -> Format.sprintf "%s.(%s) <- %s" (Id.pp_t n1) (Id.pp_t n2) (Id.pp_t n3)
    | ExtArray n -> Format.sprintf "ext_array_%s" (Id.pp_l n)
    | ExtTuple n -> Format.sprintf "ext_tuple_%s" (Id.pp_l n)
    | Read -> Format.sprintf "read_char ()"
    | Write n -> Format.sprintf "print_char %s" (Id.pp_t n)
    | Fasi n -> Format.sprintf "fasi %s" (Id.pp_t n)
    | Iasf n -> Format.sprintf "iasf %s" (Id.pp_t n)
    | Ftoi n -> Format.sprintf "ftoi %s" (Id.pp_t n)
    | Itof n -> Format.sprintf "itof %s" (Id.pp_t n)
    | Fabs n -> Format.sprintf "fabs %s" (Id.pp_t n)
    | Sqrt n -> Format.sprintf "sqrt %s" (Id.pp_t n)
  in
  Format.sprintf "%s\n" (pp_t' d t)

let rec pp_fundef { name = (Id.L(x), t); args = yts; formal_fv = zts; body = b } =
  let indent d = String.make (2 * d) ' ' in
  let args = String.concat " " (List.map (fun (name, _) -> Id.pp_t name) yts) in
  let fvs = String.concat " " (List.map (fun (name, _) -> Id.pp_t name) zts) in
  let s = (pp_t b 1) in
  let s = if String.contains s '\n' then s else (indent 1) ^ s in
  Format.sprintf "let rec %s %s {%s} (*%s*) = \n%s\n" x args fvs (Type.pp_t t) s

let rec fv (r, e) =
  match e with
  | Unit | Int(_) | Float(_) | ExtArray(_) | ExtTuple(_) | Read -> S.empty
  | Neg(x) | FNeg(x) | FInv(x) | Write(x) | Fasi(x) | Iasf(x) | Ftoi(x) | Itof(x) | Fabs(x) | Sqrt(x) -> S.singleton x
  | Add(x, y) | Sub(x, y) | Lsl(x, y) | Lsr(x, y) | Lor(x, y) | Land(x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2)| IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | MakeCls((x, t), { entry = l; actual_fv = ys }, e) -> S.remove x (S.union (S.of_list ys) (fv e))
  | AppCls(x, ys) -> S.of_list (x :: ys)
  | AppDir(_, xs) | Tuple(xs) -> S.of_list xs
  | LetTuple(xts, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xts)))
  | Put(x, y, z) -> S.of_list [x; y; z]

let toplevel : fundef list ref = ref []

let floatop2app op args = KNormal.ExtFunApp(op, args)

let rec g env known (r, e) = (* ���������Ѵ��롼�������� (caml2html: closure_g) *)
  let e' = match e with
    | KNormal.Unit -> Unit
    | KNormal.Int(i) -> Int(i)
    | KNormal.Float(d) -> Float(d)
    | KNormal.Neg(x) -> Neg(x)
    | KNormal.Add(x, y) -> Add(x, y)
    | KNormal.Sub(x, y) -> Sub(x, y)
    | KNormal.Lsl(x, y) -> Lsl(x, y)
    | KNormal.Lsr(x, y) -> Lsr(x, y)
    | KNormal.Lor(x, y) -> Lor(x, y)
    | KNormal.Land(x, y) -> Land(x, y)
    | KNormal.FNeg(x) -> FNeg(x)
    | KNormal.FAdd(x, y) -> FAdd(x, y)
    | KNormal.FSub(x, y) -> FSub(x, y)
    | KNormal.FMul(x, y) -> FMul(x, y)
    | KNormal.FDiv(x, y) -> FDiv(x, y)
    | KNormal.FInv(x) -> FInv(x)
    | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g env known e1, g env known e2)
    | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g env known e1, g env known e2)
    | KNormal.Let((x, t), e1, e2) -> Let((x, t), g env known e1, g (M.add x t env) known e2)
    | KNormal.Var(x) -> Var(x)
    | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) -> (* �ؿ�����ξ�� (caml2html: closure_letrec) *)
       (* �ؿ����let rec x y1 ... yn = e1 in e2�ξ��ϡ�
	 x�˼�ͳ�ѿ����ʤ�(closure��𤵤�direct�˸ƤӽФ���)
	 �Ȳ��ꤷ��known���ɲä���e1�򥯥������Ѵ����Ƥߤ� *)
       let toplevel_backup = !toplevel in
       let env' = M.add x t env in
       let known' = S.add x known in
       let e1' = g (M.add_list yts env') known' e1 in
       (* �����˼�ͳ�ѿ����ʤ��ä������Ѵ����e1'���ǧ���� *)
       (* ���: e1'��x���Ȥ��ѿ��Ȥ��ƽи��������closure��ɬ��!
         (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml����) *)
       let zs = S.diff (fv e1') (S.of_list (List.map fst yts)) in
       let known', e1' =
	 if S.is_empty zs then known', e1' else
	   (* ���ܤ��ä������(toplevel����)���ᤷ�ơ����������Ѵ�����ľ�� *)
	   (Format.eprintf "free variable(s) %s found in function %s@." (Id.pp_list (S.elements zs)) x;
	    Format.eprintf "function %s cannot be directly applied in fact@." x;
	    toplevel := toplevel_backup;
	    let e1' = g (M.add_list yts env') known e1 in
	    known, e1') in
       let zs = S.elements (S.diff (fv e1') (S.add x (S.of_list (List.map fst yts)))) in (* ��ͳ�ѿ��Υꥹ�� *)
       let zts = List.map (fun z -> (z, M.find z env')) zs in (* �����Ǽ�ͳ�ѿ�z�η����������˰���env��ɬ�� *)
       toplevel := { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e1' } :: !toplevel; (* �ȥåץ�٥�ؿ����ɲ� *)
       let e2' = g env' known' e2 in
       if S.mem x (fv e2') then (* x���ѿ��Ȥ���e2'�˽и����뤫 *)
	 MakeCls((x, t), { entry = Id.L(x); actual_fv = zs }, e2') (* �и����Ƥ����������ʤ� *)
       else
	 (Format.eprintf "eliminating closure(s) %s@." x;
	  snd e2') (* �и����ʤ����MakeCls���� *)
    | KNormal.App(x, ys) when S.mem x known -> (* �ؿ�Ŭ�Ѥξ�� (caml2html: closure_app) *)
       Format.eprintf "directly applying %s@." x;
       AppDir(Id.L(x), ys)
    | KNormal.App(f, xs) -> AppCls(f, xs)
    | KNormal.Tuple(xs) -> Tuple(xs)
    | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (M.add_list xts env) known e)
    | KNormal.Get(x, y) -> Get(x, y)
    | KNormal.Put(x, y, z) -> Put(x, y, z)
    | KNormal.ExtArray(x) -> ExtArray(Id.L("min_caml_" ^ x))
    | KNormal.ExtTuple(x) -> ExtTuple(Id.L("min_caml_" ^ x))
    | KNormal.ExtFunApp(x, ys) -> AppDir(Id.L("min_caml_" ^ x), ys)
    | KNormal.Read -> Read
    | KNormal.Write(x) -> Write(x)
    | KNormal.Fasi(x) -> Fasi(x)
    | KNormal.Iasf(x) -> Iasf(x)
    | KNormal.Ftoi(x) -> Ftoi(x)
    | KNormal.Itof(x) -> Itof(x)
    | KNormal.Fabs(x) -> Fabs(x)
    | KNormal.Sqrt(x) -> Sqrt(x)
  in
  (r, e')

let f e =
  toplevel := [];
  let e' = g M.empty S.empty e in
  (* print_string "(\* =====Closure===== *\)\n"; *)
  (* List.iter (fun fdef -> print_string (pp_fundef fdef)) (List.rev !toplevel); *)
  (* print_string (pp_t e' 0); *)
  Prog(List.rev !toplevel, e')
