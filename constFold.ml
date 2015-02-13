open KNormal

external getsgl : float -> int = "getsgl"

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

let rec g env (r, e) = (* 定数畳み込みルーチン本体 (caml2html: constfold_g) *)
  match e with
  | Var(x) when memi x env -> (r, Int(findi x env))
  | Var(x) when memf x env -> (r, Float(findf x env))
  | Var(x) when memt x env -> (r, Tuple(findt x env))
  | Neg(x) when memi x env -> (r, Int(-(findi x env)))
  | Add(x, y) when memi x env && memi y env -> (r, Int(findi x env + findi y env))
  | Add(x, y) when memi x env && findi x env = 0 -> (r, Var(y))
  | Add(x, y) when memi y env && findi y env = 0 -> (r, Var(x))
  | Add(x, y) when x == y -> 
     let one = Id.genid "one" in
     let e1 = (r, Int(1)) in
     let e2 = (r, Lsl(x, one)) in
     (r, Let((one, Type.Int), e1, e2))
  | Sub(x, y) when memi x env && memi y env -> (r, Int(findi x env - findi y env))
  | Sub(x, y) when x == y -> (r, Int(0))
  | Sub(x, y) when memi x env && findi x env = 0 -> (r, Neg(y))
  | Sub(x, y) when memi y env && findi y env = 0 -> (r, Var(x))
  | Lsl(x, y) when memi x env && memi y env -> (r, Int(findi x env lsl findi y env))
  | Lsl(x, y) when memi x env && findi x env = 0 -> (r, Int(0))
  | Lsl(x, y) when memi y env && findi y env = 0 -> (r, Var(x))
  | Lsr(x, y) when memi x env && memi y env -> (r, Int(findi x env lsr findi y env))
  | Lsr(x, y) when memi x env && findi x env = 0 -> (r, Int(0))
  | Lsr(x, y) when memi y env && findi y env = 0 -> (r, Var(x))
  | Lor(x, y) when memi x env && memi y env -> (r, Int(findi x env lor findi y env))
  | Lor(x, y) when memi x env && findi x env = 0 -> (r, Var(y))
  | Lor(x, y) when memi y env && findi y env = 0 -> (r, Var(x))
  | Lor(x, y) when memi x env && findi x env = -1 -> (r, Int(-1))
  | Lor(x, y) when memi y env && findi y env = -1 -> (r, Int(-1))
  | Land(x, y) when memi x env && memi y env -> (r, Int(findi x env land findi y env))
  | Land(x, y) when memi x env && findi x env = 0 -> (r, Int(0))
  | Land(x, y) when memi y env && findi y env = 0 -> (r, Int(0))
  | Land(x, y) when memi x env && findi x env = -1 -> (r, Var(y))
  | Land(x, y) when memi y env && findi y env = -1 -> (r, Var(x))
  | FNeg(x) when memf x env -> (r, Float(-.(findf x env)))
  | FAdd(x, y) when memf x env && memf y env -> (r, Float(findf x env +. findf y env))
  | FAdd(x, y) when memf x env && findf x env = 0.0 -> (r, Var(y))
  | FAdd(x, y) when memf y env && findf y env = 0.0 -> (r, Var(x))
  | FSub(x, y) when memf x env && memf y env -> (r, Float(findf x env -. findf y env))
  | FSub(x, y) when x == y -> (r, Float(0.0))
  | FSub(x, y) when memf x env && findf x env = 0.0 -> (r, FNeg(y))
  | FSub(x, y) when memf y env && findf y env = 0.0 -> (r, Var(x))
  | FMul(x, y) when memf x env && memf y env -> (r, Float(findf x env *. findf y env))
  | FMul(x, y) when memf x env && findf x env = 0.0 -> (r, Float(0.0))
  | FMul(x, y) when memf y env && findf y env = 0.0 -> (r, Float(0.0))
  | FMul(x, y) when memf x env && findf x env = 1.0 -> (r, Var(y))
  | FMul(x, y) when memf y env && findf y env = 1.0 -> (r, Var(x))
  | FMul(x, y) when memf x env && findf x env = -1.0 -> (r, FNeg(y))
  | FMul(x, y) when memf y env && findf y env = -1.0 -> (r, FNeg(x))
  | FDiv(x, y) when memf x env && memf y env -> (r, Float(findf x env /. findf y env))
  | FDiv(x, y) when memf x env && findf x env = 0.0 -> (r, Float(0.0))
  | FDiv(x, y) when memf x env && findf x env = 1.0 -> (r, FInv(y))
  | FDiv(x, y) when memf y env && findf y env = 1.0 -> (r, Var(x))
  | FDiv(x, y) when memf x env && findf x env = -1.0 ->
     let y_neg = Id.genid (y ^ "_neg") in
     let e1 = (r, FNeg(y)) in
     let e2 = (r, FInv(y_neg)) in
     (r, Let((y_neg, Type.Float), e1, e2))
  | FDiv(x, y) when memf y env && findf y env = -1.0 -> (r, FNeg(x))
  | FDiv(x, y) when memf y env -> 
     let y_inv = Id.genid (y ^ "_inv") in
     let e1 = (r, Float (1.0 /. findf y env)) in
     let e2 = (r, FMul (x, y_inv)) in
     (r, Let((y_inv, Type.Float), e1, e2))
  | IfEq(x, y, e1, e2) when memi x env && memi y env -> if findi x env = findi y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) when memf x env && memf y env -> if findf x env = findf y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) -> (r, IfEq(x, y, g env e1, g env e2))
  | IfLE(x, y, e1, e2) when memi x env && memi y env -> if findi x env <= findi y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) when memf x env && memf y env -> if findf x env <= findf y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) -> (r, IfLE(x, y, g env e1, g env e2))
  | Let((x, t), e1, e2) -> (* letのケース (caml2html: constfold_let) *)
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
  | Ftoi(x) when memi x env -> (r, Int (int_of_float (findf x env)))
  | Itof(x) when memf x env -> (r, Float (float_of_int (findi x env)))
  | Sqrt(x) when memf x env -> (r, Float (sqrt (findf x env)))
  | Fabs(x) when memf x env -> (r, Float (abs_float (findf x env)))
  | e -> (r, e)
	     
let f = g M.empty
