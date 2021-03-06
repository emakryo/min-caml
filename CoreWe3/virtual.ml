(* translation into CoreWe3 assembly (infinite number of virtual registers) *)

open Asm

external getsgl : float -> int32 = "getsgl"  

let rec g env dest e = (* 式の仮想マシンコード生成 *)
  let e' = g' env dest e in
  List.map new_t e'
and g' env dest (r, e) = (* 式の仮想マシンコード生成 *)
    match e with
    | Closure.Unit -> [Nop]
    | Closure.Int(i) -> [Li(dest, Int32.of_int i)]
    | Closure.Float(d) -> [FLi(dest, d)]
    | Closure.Neg(x) -> [Neg(dest, x)]
    | Closure.Add(x, y) -> [Add(dest, x, V (y))]
    | Closure.Sub(x, y) -> [Sub(dest, x, y)]
    | Closure.Lsl(x, y) -> [Shl(dest, x, V(y))]
    | Closure.Lsr(x, y) -> [Shr(dest, x, V(y))]
    | Closure.Lor(x, y) -> [Or(dest, x, y)]
    | Closure.Land(x, y) -> [And(dest, x, y)]
    | Closure.FNeg(x) -> [FSub(dest, freg_zero, x)]
    | Closure.FInv(x) -> [FInv(dest, x)]
    | Closure.FAdd(x, y) -> [FAdd(dest, x, y)]
    | Closure.FSub(x, y) -> [FSub(dest, x, y)]
    | Closure.FMul(x, y) -> [FMul(dest, x, y)]
    | Closure.FDiv(x, y) -> 
       let z = Id.genid "z" in
       [FInv((z, Type.Float), y); FMul(dest, x, z)]
    | Closure.Fabs(x) -> [FAbs(dest, x)]
    | Closure.Sqrt(x) -> [Sqrt(dest, x)]
    | Closure.IfEq(x, y, e1, e2) -> 
       (match M.find x env with
	| Type.Bool | Type.Int -> 
	   [If(dest, Eq, (x, V(y)), g env dest e1, g env dest e2)]
	| Type.Float ->
	   [IfF(dest, Eq, (x, y), g env dest e1, g env dest e2)]
	| _ -> failwith "equality supported only for bool, int and float.")
    | Closure.IfLE(x, y, e1, e2) ->
       (match M.find x env with
	| Type.Bool | Type.Int -> 
	   [If(dest, LE, (x, V(y)), g env dest e1, g env dest e2)]
	| Type.Float ->
	   [IfF(dest, LE, (x, y), g env dest e1, g env dest e2)]
	| _ -> failwith "inequality supported only for bool, int and float.")
    | Closure.Let ((x, t), e1, e2) ->
       let e1' = g' env (x, t) e1 in
       let e2' = g' (M.add x t env) dest e2 in
       e1' @ e2'
    | Closure.Var (x) -> [move_reg dest x]
    | Closure.MakeCls ((x, t), {Closure.entry = l; Closure.actual_fv = ys}, e2) ->
       failwith "Sorry, closure is not supported yet..."
    | Closure.AppCls (x, ys) ->
       failwith "Sorry, closure is not supported yet..."
    | Closure.AppDir (Id.L(l), ys) ->
       let yts = List.map (fun y -> (y, M.find y env)) ys in
       let (yts, zts) = partition_by_type yts in
       [Call(dest, Id.L(l), yts, zts)]
    | Closure.Tuple (xs) -> (* 組の生成 *)
       let (tup, ty) = dest in
       let xts = List.map (fun x -> (x, M.find x env)) xs in
       let (len, store) = 
	 List.fold_left
	   (fun (i, store) (x, t) ->
	    match t with
	    | Type.Unit -> (i + 1, store)
	    | Type.Float -> (i + 1, (FSt(x, tup, i))::store)
	    | _ -> (i + 1, (St(x, tup, i))::store))
	   (0, []) 
	   xts in
       [Mr(dest, reg_hp)] @ store @ [Add((reg_hp, Type.Int), reg_hp, C(len))]
    | Closure.LetTuple (xts, y, e2) ->
       let s = Closure.fv e2 in
       let (len, load) = 
	 List.fold_left
	   (fun (i, load) (x, t) ->
	    if not (S.mem x s) then 
	      (i + 1, load)
	    else
	      match t with
	      | Type.Unit -> (i + 1, load)
	      | Type.Float -> (i + 1, (FLd((x, t), y, i))::load)
	      | _ -> (i + 1, (Ld((x, t), y, i))::load))
	   (0, []) 
	   xts in
       let e2' = g' (M.add_list xts env) dest e2 in
       load @ e2'
    | Closure.Get (x, y) -> (* 配列の読み出し *)
       let addr = Id.genid "array" in  
       (match M.find x env with
	| Type.Array(Type.Unit) -> [Nop]
	| Type.Array(Type.Float) -> [Add((addr, Type.Int), x, V(y)); FLd(dest, addr, 0)]
	| Type.Array(_) -> [Add((addr, Type.Int), x, V(y)); Ld(dest, addr, 0)]
	| _ -> assert false)
    | Closure.Put (x, y, z) ->
       let addr = Id.genid "array" in 
       (match M.find x env with
	| Type.Array(Type.Unit) -> [Nop]
	| Type.Array(Type.Float) -> [Add((addr, Type.Int), x, V(y)); FSt(z, addr, 0)]
	| Type.Array(_) -> [Add((addr, Type.Int), x, V(y)); St(z, addr, 0)]
	| _ -> assert false)
    | Closure.ExtArray l | Closure.ExtTuple l -> 
       [LoadLabel(dest, l)]
    | Closure.Read -> 
       let (x, t) = dest in
       (match t with
	| Type.Int -> [Ld(dest, reg_zero, io_addr)]
	| Type.Float -> [FLd(dest, reg_zero, io_addr)]
	| _ -> failwith "read supported only for int and float.")
    | Closure.Write(x) -> 
       (match M.find x env with
	| Type.Int -> [St(x, reg_zero, io_addr)]
	| Type.Float -> [FSt(x, reg_zero, io_addr)]
	| _ -> failwith "write supported only for int and float.")
    | Closure.Fasi(x) ->
       let tmp = Id.genid "stk" in
       [FSave(x, tmp); Restore(dest, tmp)]
    | Closure.Iasf(x) ->
       let tmp = Id.genid "stk" in
       [Save(x, tmp); FRestore(dest, tmp)]
    | Closure.Ftoi(x) ->
       [FToI(dest, x)]
    | Closure.Itof(x) ->
       [IToF(dest, x)] 
    | Closure.Floor(x) ->
       [Floor(dest, x)]

(* 関数の仮想マシンコード生成 *)
let h { Closure.name = (Id.L(x), t); Closure.args = yts; 
	Closure.formal_fv = zts; Closure.body = e} =
  let env = M.add x t (M.add_list yts (M.add_list zts M.empty)) in
  match t with
  | Type.Fun (_, t_ret) ->
     let (yts, zts) = partition_by_type yts in
     let bdy = g env (ret_reg t_ret, t_ret) e in
     {name = Id.L(x); args = yts; fargs = zts; body = bdy; ret = t_ret}
  | _ -> assert false

(* プログラム全体の仮想マシンコード生成 *)
let f (Closure.Prog (fundefs, e)) =
  let e = g M.empty (ret_reg Type.Unit, Type.Unit) e in
  let fundefs = List.map h fundefs in
  Prog (fundefs, e)
