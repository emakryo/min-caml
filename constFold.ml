open KNormal

let memi x env =
  try (match M.find x env with Int(_) -> true | _ -> false)
  with Not_found -> false
let memf x env =
  try (match M.find x env with Float(_) -> true | _ -> false)
  with Not_found -> false
let memt x env =
  try (match M.find x env with Tuple(_) -> true | _ -> false)
  with Not_found -> false

let findi x env = (match M.find x env with Int(i) -> i | _ -> raise Not_found)
let findf x env = (match M.find x env with Float(d) -> d | _ -> raise Not_found)
let findt x env = (match M.find x env with Tuple(ys) -> ys | _ -> raise Not_found)

let rec g env (r, e) = (* ������߹��ߥ롼�������� (caml2html: constfold_g) *)
  match e with
  | Var(x) when memi x env -> (r, Int(findi x env))
  (* | Var(x) when memf x env -> Float(findf x env) *)
  (* | Var(x) when memt x env -> Tuple(findt x env) *)
  | Neg(x) when memi x env -> (r, Int(-(findi x env)))
  | Add(x, y) when memi x env && memi y env -> (r, Int(findi x env + findi y env)) (* ­�����Υ����� (caml2html: constfold_add) *)
  | Sub(x, y) when memi x env && memi y env -> (r, Int(findi x env - findi y env))
  | Mul(x, y) when memi x env && memi y env -> (r, Int(findi x env * findi y env))
  | Div(x, y) when memi x env && memi y env -> (r, Int(findi x env / findi y env))
  | Lsl(x, y) when memi x env && memi y env -> (r, Int(findi x env lsl findi y env))
  | Lsr(x, y) when memi x env && memi y env -> (r, Int(findi x env lsr findi y env))
  | FNeg(x) when memf x env -> (r, Float(-.(findf x env)))
  | FAdd(x, y) when memf x env && memf y env -> (r, Float(findf x env +. findf y env))
  | FSub(x, y) when memf x env && memf y env -> (r, Float(findf x env -. findf y env))
  | FMul(x, y) when memf x env && memf y env -> (r, Float(findf x env *. findf y env))
  | FDiv(x, y) when memf x env && memf y env -> (r, Float(findf x env /. findf y env))
  | IfEq(x, y, e1, e2) when memi x env && memi y env -> if findi x env = findi y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) when memf x env && memf y env -> if findf x env = findf y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) -> (r, IfEq(x, y, g env e1, g env e2))
  | IfLE(x, y, e1, e2) when memi x env && memi y env -> if findi x env <= findi y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) when memf x env && memf y env -> if findf x env <= findf y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) -> (r, IfLE(x, y, g env e1, g env e2))
  | Let((x, t), e1, e2) -> (* let�Υ����� (caml2html: constfold_let) *)
     let (r1', e1') = g env e1 in
     let e2' = g (M.add x e1' env) e2 in
     (r, Let((x, t), (r1', e1'), e2'))
  | LetRec({ name = x; args = ys; body = e1 }, e2) ->
     (r, LetRec({ name = x; args = ys; body = g env e1 }, g env e2))
  | LetTuple(xts, y, e) when memt y env ->
     List.fold_left2
       (fun e' xt z -> (r, Let(xt, (r, Var(z)), e'))) (*TODO: attach range to id*)
       (g env e)
       xts
       (findt y env)
  | LetTuple(xts, y, e) -> (r, LetTuple(xts, y, g env e))
  | e -> (r, e)
	     
let f = g M.empty
