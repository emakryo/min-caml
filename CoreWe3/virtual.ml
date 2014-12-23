(* translation into CoreWe3 assembly (infinite number of virtual registers) *)

open Asm

external getsgl : float -> int32 = "getsgl"

let data = ref [] (* 浮動小数点数の定数テーブル *)

let classify xts ini addi =
  List.fold_left
    (fun acc (x, t) -> 
     match t with
     | Type.Unit -> acc
     | _ -> addi acc x t) ini xts

let expand xts ini addi = 
  classify
    xts
    ini
    (fun (offset, acc) x t -> (offset + 1, addi x t offset acc))

let rec g env (r, e) = (* 式の仮想マシンコード生成 *)
  match e with
  | Closure.Unit -> Ans (Nop)
  | Closure.Int (i) ->
     let i32 = Int32.of_int i in
     Ans (Li (i32))
  | Closure.Float (d) -> 
     Ans (Li (getsgl d))
  | Closure.Neg (x) -> Ans (Neg (x))
  | Closure.Add (x, y) -> Ans (Add (x, V (y)))
  | Closure.Sub (x, y) -> Ans (Sub (x, y))
  | Closure.Lsl (x, y) -> Ans (Slw (x, V(y)))
  | Closure.Lsr (x, y) -> Ans (Srw (x, V(y)))
  | Closure.FNeg (x) -> Ans (FNeg (x))
  | Closure.FInv (x) -> Ans (FInv (x))
  | Closure.FAdd (x, y) -> Ans (FAdd (x, y))
  | Closure.FSub (x, y) -> Ans (FSub (x, y))
  | Closure.FMul (x, y) -> Ans (FMul (x, y))
  | Closure.FDiv (x, y) -> Ans (FDiv (x, y))
  | Closure.IfEq (x, y, e1, e2) -> 
     (match M.find x env with
      | Type.Bool | Type.Int | Type.Float -> Ans (IfEq (x, y, g env e1, g env e2))
      | _ -> failwith "equality supported only for bool, int and float.")
  | Closure.IfLE (x, y, e1, e2) ->
     (match M.find x env with
      | Type.Bool | Type.Int -> Ans (IfLE (x, y, g env e1, g env e2))
      | Type.Float ->  Ans (IfFLE (x, y, g env e1, g env e2))
      | _ -> failwith "inequality supported only for bool, int.")
  | Closure.Let ((x, t1), e1, e2) ->
     let e1' = g env e1 in
     let e2' = g (M.add x t1 env) e2 in
     concat e1' (x, t1) e2'
  | Closure.Var (x) ->
     (match M.find x env with
      | Type.Unit -> Ans (Nop)
      | _ -> Ans (Mr (x)))
  | Closure.MakeCls ((x, t), {Closure.entry = l; Closure.actual_fv = ys}, e2) ->
     failwith "Sorry, closure is not supported yet..."
     (* (\* closure のアドレスをセットしてからストア *\) *)
     (* let e2' = g (M.add x t env) e2 in *)
     (* let (offset, store_fv) =  *)
     (*   expand *)
     (* 	 (List.map (fun y -> (y, M.find y env)) ys) *)
     (* 	 (1, e2') *)
     (* 	 (fun y _ offset store_fv -> seq (Stw (y, x, offset), store_fv)) in *)
     (* Let ((x, t), Mr (reg_hp),  *)
     (* 	  Let ((reg_hp, Type.Int), Add (reg_hp, C (offset)),  *)
     (* 	       let z = Id.genid "l" in   *)
     (* 	       Let ((z, Type.Int), SetL(l),  *)
     (* 		    seq (Stw (z, x, 0), store_fv)))) *)
  | Closure.AppCls (x, ys) ->
     failwith "Sorry, closure is not supported yet..."
     (* Ans (CallCls (x, ys)) *)
  | Closure.AppDir (Id.L(x), ys) ->
     Ans (CallDir (Id.L(x), ys))
  | Closure.Tuple (xs) -> (* 組の生成 *)
     let y = Id.genid "t" in
     let (offset, store) = 
       expand
	 (List.map (fun x -> (x, M.find x env)) xs)
	 (0, Ans (Mr (y)))
	 (fun x _ offset store -> seq (Stw (x, y, offset), store))  in
     Let ((y, Type.Tuple (List.map (fun x -> M.find x env) xs)), Mr (reg_hp),
	  Let ((reg_hp, Type.Int), Add (reg_hp, C (offset)), store))
  | Closure.LetTuple (xts, y, e2) ->
     let s = Closure.fv e2 in
     let (offset, load) = 
       expand
	 xts
	 (0, g (M.add_list xts env) e2)
	 (fun x t offset load ->
	  if not (S.mem x s) then load 
	  else Let ((x, t), Lwz (y, offset), load)) in
     load
  | Closure.Get (x, y) -> (* 配列の読み出し *)
     let addr = Id.genid "o" in  
     (match M.find x env with
      | Type.Array (Type.Unit) -> Ans (Nop)
      | Type.Array (_) ->
	 Let ((addr, Type.Int), Add (x, V(y)),
	      Ans (Lwz (addr, 0)))
      | _ -> assert false)
  | Closure.Put (x, y, z) ->
     let addr = Id.genid "o" in 
     (match M.find x env with
      | Type.Array (Type.Unit) -> Ans (Nop)
      | Type.Array (_) ->
	 Let ((addr, Type.Int), Add (x, V(y)), 
	      Ans (Stw (z, addr, 0))) 
      | _ -> assert false)
  | Closure.ExtArray l -> 
     Ans (SetL (l))
  | Closure.ExtTuple l -> 
     Ans (SetL (l))
  (* | Closure.FAdd (_, _)| Closure.FSub (_, _)|Closure.FMul (_, _)| Closure.FDiv (_, _) -> *)
  (*    failwith "Sorry, native floating-point operations are not supported yet..." *)

(* 関数の仮想マシンコード生成 *)
let h { Closure.name = (Id.L(x), t); Closure.args = yts; 
	Closure.formal_fv = zts; Closure.body = e} =
  let ys = List.map (fun (y, t) -> y) yts in
  let (offset, load) = 
    expand
      zts
      (4, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
      (fun z t offset load -> Let ((z, t), Lwz (reg_cl, offset), load)) in
  match t with
  | Type.Fun (_, t2) ->
     { name = Id.L(x); args = ys; body = load; ret = t2 }
  | _ -> assert false

(* プログラム全体の仮想マシンコード生成 *)
let f (Closure.Prog (fundefs, e)) =
  data := [];
  let fundefs = List.map h fundefs in
  let e = g M.empty e in
  Prog (!data, fundefs, e)
