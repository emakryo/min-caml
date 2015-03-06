open Asm

let constreg_mem x env = M.mem x env && List.mem_assoc (M.find x env) !constregs
let constreg_find x env = 
  if constreg_mem x env then
    List.assoc (M.find x env) !constregs
  else x
let constfreg_mem x env = M.mem x env && List.mem_assoc (M.find x env) !constfregs
let constfreg_find x env = 
  if constfreg_mem x env then
    List.assoc (M.find x env) !constfregs
  else x
let imm_mem x env = 
  if M.mem x env then 
    let imm = M.find x env in
    -imm_max <= imm && imm < imm_max
  else false
let imm_find x env =
  if M.mem x env then
    let imm = M.find x env in
    if List.mem_assoc imm !constregs then
      V(List.assoc (M.find x env) !constregs)
    else if -imm_max <= imm && imm < imm_max then
      C(imm)
    else V(x)
  else V(x)

let rec g (envi, envf) = function
  | [] -> []
  | (i, e, b)::es ->
     let (envi, envf) =
       match e with 
       | Save(x, s) when M.mem x envi -> (M.add s (M.find x envi) envi, envf)
       | FSave(x, s) when M.mem x envf -> (envi, M.add s (M.find x envf) envf) 
       | _ -> (envi, envf) in
     let e =
       match e with
       | Nop -> Nop
       | Ld((x, t), y, i) -> Ld((x, t), constreg_find y envi, i)
       | St(x, y, i) -> St(constreg_find x envi, constreg_find y envi, i)
       | FLd((x, t), y, i) -> FLd((x, t), constreg_find y envi, i)
       | FSt(x, y, i) -> FSt(constfreg_find x envf, constreg_find y envi, i)
       | IToF((x, t), y) -> IToF((x, t), constreg_find y envi)
       | FToI((x, t), y) -> FToI((x, t), constfreg_find y envf)
       | Neg((x, t), y) -> Neg((x, t), constreg_find y envi)
       | Add((x, t), y, V(z)) -> Add((x, t), constreg_find y envi, imm_find z envi)
       | Add((x, t), y, C(i)) -> Add((x, t), constreg_find y envi, C(i))
       | Sub((x, t), y, z) when imm_mem z envi -> Add((x, t), constreg_find y envi, C(-(M.find z envi)))
       | Sub((x, t), y, z) -> Sub((x, t), constreg_find y envi, constreg_find z envi)
       | And((x, t), y, z) -> And((x, t), constreg_find y envi, constreg_find z envi)
       | Or((x, t), y, z) -> Or((x, t), constreg_find y envi, constreg_find z envi)
       | Li((x, t), i) -> Li((x, t), i)
       | Shl((x, t), y, V(z)) -> Shl((x, t), constreg_find y envi, imm_find z envi)
       | Shl((x, t), y, C(i)) -> Shl((x, t), constreg_find y envi, C(i))
       | Shr((x, t), y, V(z)) -> Shr((x, t), constreg_find y envi, imm_find z envi)
       | Shr((x, t), y, C(i)) -> Shr((x, t), constreg_find y envi, C(i))
       | FAdd((x, t), y, z) -> FAdd((x, t), constfreg_find y envf, constfreg_find z envf)
       | FSub((x, t), y, z) -> FSub((x, t), constfreg_find y envf, constfreg_find z envf)
       | FMul((x, t), y, z) -> FMul((x, t), constfreg_find y envf, constfreg_find z envf)
       | FInv((x, t), y) -> FInv((x, t), constfreg_find y envf)
       | FAbs((x, t), y) -> FAbs((x, t), constfreg_find y envf)
       | Sqrt((x, t), y) -> Sqrt((x, t), constfreg_find y envf)
       | FLi((x, t), f) -> FLi((x, t), f)
       | If((x, t), cond, (y, V(z)), e_then, e_else) ->
	  If((x, t), cond, (constreg_find y envi, imm_find z envi), g (envi, envf) e_then, g (envi, envf) e_else)
       | If((x, t), cond, (y, C(i)), e_then, e_else) ->
	  If((x, t), cond, (constreg_find y envi, C(i)), g (envi, envf) e_then, g (envi, envf) e_else)
       | IfF((x, t), cond, (y, z), e_then, e_else) ->
	  IfF((x, t), cond, (constfreg_find y envf, constfreg_find z envf), g (envi, envf) e_then, g (envi, envf) e_else)
       | Call((x, t), f, yts, zts) -> Call((x, t), f, yts, zts)
       | LoadLabel((x, t), l) -> LoadLabel((x, t), l)
       | Mr((x, t), y) when x = y -> Mr((x, t), y)
       | Mr((x, t), y) when constreg_mem y envi -> Mr((x, t), constreg_find y envi)
       | Mr((x, t), y) when M.mem y envi -> Li((x, t), Int32.of_int (M.find y envi))
       | Mr((x, t), y) -> Mr((x, t), y)
       | FMr((x, t), y) when x = y -> Mr((x, t), y)
       | FMr((x, t), y) when constfreg_mem y envf -> FMr((x, t), constfreg_find y envf)
       | FMr((x, t), y) when M.mem y envf -> FLi((x, t), M.find y envf)
       | FMr((x, t), y) -> FMr((x, t), y)
       | Save(x, s) when M.mem s envi -> Nop
       | Save(x, s) -> Save(x, s)
       | Restore((x, t), s) when constreg_mem s envi -> Mr((x, t), constreg_find s envi)
       | Restore((x, t), s) when M.mem s envi -> Li((x, t), Int32.of_int (M.find s envi))
       | Restore((x, t), s) -> Restore((x, t), s)
       | FSave(x, s) when M.mem s envf -> Nop
       | FSave(x, s) -> FSave(x, s)
       | FRestore((x, t), s) when constfreg_mem s envf -> FMr((x, t), constfreg_find s envf)
       | FRestore((x, t), s) when M.mem s envf -> FLi((x, t), M.find s envf)
       | FRestore((x, t), s) -> FRestore((x, t), s) in
     let (envi, envf) =
       match e with
       | Li((x, t), i) ->
	  (M.add x (Int32.to_int i) envi, envf)
       | FLi((x, t), f) ->
	  (envi, M.add x f envf)
       | Mr((x, t), y) when M.mem y envi ->
	  (M.add x (M.find y envi) envi, envf)
       | FMr((x, t), y) when M.mem y envf ->
	  (envi, M.add x (M.find y envf) envf)
       | e -> 
	  let (defi, deff) = Liveness.def_set (i, e, b) in
	  let folder = (fun x env -> M.remove x env) in
	  (S.fold folder defi envi, S.fold folder deff envf) in
     (i, e, b)::(g (envi, envf) es)

let init_envs () =
  let envi = List.fold_left (fun envi (x, r) -> M.add r x envi) M.empty !constregs in
  let envf = List.fold_left (fun envi (x, r) -> M.add r x envi) M.empty !constfregs in
  (envi, envf)

(* トップレベル関数の 14 bit 即値最適化 *)
let h { name = l; args = yts; fargs = zts; body = e; ret = t } =
  { name = l; args = yts; fargs = zts; body = g (init_envs()) e; ret = t }

(* プログラム全体の 14 bit 即値最適化 *)
let f (Prog(fundefs, e)) = 
  (* (Prog(fundefs, e)) *)
  Prog(List.map h fundefs, g (init_envs ()) e)
