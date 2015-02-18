open Asm

external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"
external getsgl : float -> int32 = "getsgl"

(* let stackset = ref S.empty (\* すでに Save された変数の集合 *\) *)
(* let stackmap = ref [] (\* Save された変数のスタックにおける位置 *\) *)
(* let save x =  *)
(*   stackset := S.add x !stackset; *)
(*   if not (List.mem x !stackmap) then *)
(*     stackmap := !stackmap @ [x] *)
(* let savef x =  *)
(*   stackset := S.add x !stackset; *)
(*   if not (List.mem x !stackmap) then *)
(*     (let pad =  *)
(*        if List.length !stackmap mod 2 = 0 then [] else [Id.gentmp Type.Int] in *)
(*      stackmap := !stackmap @ pad @ [x; x]) *)
(* let locate x =  *)
(*   let rec loc = function  *)
(*     | [] -> [] *)
(*     | y :: zs when x = y -> 0 :: List.map succ (loc zs) *)
(*     | y :: zs -> List.map succ (loc zs) in *)
(*   loc !stackmap *)
(* let offset x = 1 * List.hd (locate x) *)
(* let stacksize () = List.length !stackmap *)

let reg r = 
  if is_reg r 
  then String.sub r 1 (String.length r - 1)
  else r 

(* (\* 関数呼び出しのために引数を並べ替える (register shuffling) *\) *)
(* let rec shuffle sw xys =  *)
(*   (\* remove identical moves *\) *)
(*   let (_, xys) = List.partition (fun (x, y) -> x = y) xys in *)
(*     (\* find acyclic moves *\) *)
(*     match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with *)
(*       | ([], []) -> [] *)
(*       | ((x, y) :: xys, []) -> (\* no acyclic moves; resolve a cyclic move *\) *)
(* 	  (y, sw) :: (x, y) ::  *)
(* 	    shuffle sw (List.map (function  *)
(* 				    | (y', z) when y = y' -> (sw, z) *)
(* 				    | yz -> yz) xys) *)
(*       | (xys, acyc) -> acyc @ shuffle sw xys *)

let rec rm_nop = function
  | [] -> []
  | e::es -> (rm_nop' e) @ (rm_nop es)
and rm_nop'(i, e, b) = 
  match e with
  | Nop -> []
  | Mr((x, _), y) | FMr((x, _), y) when x == y  -> []
  | If(cnd, dest, e_then, e_else) -> 
     [(i, If(cnd, dest, rm_nop e_then, rm_nop e_else), b)]
  | IfF(cnd, dest, e_then, e_else) -> 
     [(i, IfF(cnd, dest, rm_nop e_then, rm_nop e_else), b)]
  | e -> [(i, e, b)]

let rec g oc = function (* 命令列のアセンブリ生成 *)
  | (_, []) -> ()
  | (tail, [e]) -> g' oc (tail, e)
  | (tail, e::es) -> g' oc (false, e); g oc (tail, es)
and g' oc (tail, (i, e, b)) =  (* 各命令のアセンブリ生成 *)
  let at = if b then "@" else "" in
  match (tail, e) with
  | (false, Nop) -> 
     Printf.fprintf oc "\tADDI%s\t%s\t%s\t0\t#Nop\n" at (reg reg_zero) (reg reg_zero)
  | (false, Mr((x, t), y)) when x == y -> 
     Printf.fprintf oc "\tADDI%s\t%s\t%s\t0\t#Nop\n" at (reg x) (reg y)
  | (false, Mr((x, t), y)) -> 
     Printf.fprintf oc "\tADDI%s\t%s\t%s\t0\t#Mr\n" at (reg x) (reg y)
  | (false, FMr((x, t), y)) when x == y -> 
     Printf.fprintf oc "\tFADD%s\t%s\t%s\t%s\t#Nop\n" at (reg x) (reg y) (reg freg_zero)
  | (false, FMr((x, t), y)) -> 
     Printf.fprintf oc "\tFADD%s\t%s\t%s\t%s\t#FMr\n" at (reg x) (reg y) (reg freg_zero)
  | (false, Ld((x, t), y, i)) -> 
     Printf.fprintf oc "\tLD%s\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, St(x, y, i)) -> 
     Printf.fprintf oc "\tST%s\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, FLd((x, t), y, i)) -> 
     Printf.fprintf oc "\tFLD%s\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, FSt(x, y, i)) -> 
     Printf.fprintf oc "\tFST%s\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, Li((x, t), i)) -> 
     Printf.fprintf oc "\tLDI%s\t%s\t%ld\n" at (reg x) i
  | (false, FLi((x, t), d)) -> 
     Printf.fprintf oc "\tFLDI%s\t%s\t0x%lx\t#%f\n" at (reg x) (getsgl d) d
  | (false, IToF((x, t), y)) -> 
     Printf.fprintf oc "\tITOF%s\t%s\t%s\n" at (reg x) (reg y)
  | (false, FToI((x, t), y)) -> 
     Printf.fprintf oc "\tFTOI%s\t%s\t%s\n" at (reg x) (reg y)
  | (false, Neg((x, t), y)) -> 
     Printf.fprintf oc "\tSUB%s\t%s\t%s\t%s\t#Neg\n" at (reg x) (reg reg_zero) (reg y)
  | (false, Add((x, t), y, V(z))) -> 
     Printf.fprintf oc "\tADD%s\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Add((x, t), y, C(i))) -> 
     Printf.fprintf oc "\tADDI%s\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, Sub((x, t), y, z)) -> 
     Printf.fprintf oc "\tSUB%s\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, And((x, t), y, z)) -> 
     Printf.fprintf oc "\tAND%s\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Or((x, t), y, z)) -> 
     Printf.fprintf oc "\tOR%s\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Shl((x, t), y, V(z))) -> 
     Printf.fprintf oc "\tSHL%s\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Shl((x, t), y, C(i))) -> 
     Printf.fprintf oc "\tSHLI%s\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, Shr((x, t), y, V(z))) -> 
     Printf.fprintf oc "\tSHR%s\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Shr((x, t), y, C(i))) -> 
     Printf.fprintf oc "\tSHRI%s\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, FAdd((x, t), y, z)) -> 
     Printf.fprintf oc "\tFADD%s\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, FSub((x, t), y, z)) -> 
     Printf.fprintf oc "\tFSub%s\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, FMul((x, t), y, z)) -> 
     Printf.fprintf oc "\tFMUL%s\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, FInv((x, t), y)) -> 
     Printf.fprintf oc "\tFINV%s\t%s\t%s\n" at (reg x) (reg y)
  | (false, FAbs((x, t), y)) -> 
     Printf.fprintf oc "\tFABS%s\t%s\t%s\n" at (reg x) (reg y)
  | (false, Sqrt((x, t), y)) -> 
     Printf.fprintf oc "\tFSQRT%s\t%s\t%s\n" at (reg x) (reg y)
  (* | (false, IAsF((x, t), y)) -> (\*TODO: implement virtual instruction*\) *)
  (*    Printf.fprintf oc "\tIASF%s\t%s\t%s\n" at (reg x) (reg y) *)
  (* | (false, FAsI((x, t), y)) -> (\*TODO: implement virtual instruction*\) *)
  (*    Printf.fprintf oc "\tFASI%s\t%s\t%s\n" at (reg x) (reg y) *)
  | (false, LoadLabel((x, t), Id.L(l))) -> 
     Printf.fprintf oc "\tLDI%s\t%s\t.%s\n" at (reg x) l
  | (false, Save(x, y)) -> (*TODO: implement virtual instruction*)
     Printf.fprintf oc "\tSAVE%s\t%s\t%s\n" at (reg x) (reg y)
  | (false, Restore((x, t), y)) -> (*TODO: implement virtual instruction*)
     Printf.fprintf oc "\tRSTR%s\t%s\t%s\n" at (reg x) (reg y)
  | (true, (Nop | Mr _ | FMr _ | Ld _ | St _ | FLd _ | FSt _ | Li _ | FLi _ | IToF _ | FToI _ | Neg _ | Add _ | Sub _ | And _ | Or _ | Shl _ | Shr _ | FAdd _ | FSub _ | FMul _ | FInv _ | FAbs _ | Sqrt _ (* | IAsF _ | FAsI _  *)| LoadLabel _ | Save _ | Restore _ as e)) ->
     g' oc (false, (i, e, b));
     Printf.fprintf oc "\tRET\n"
  | (tail, If(cnd, (x, y'), e1, e2)) ->
     let bc = "J" ^ cond_of_string cnd in
     (match y' with
      | V(y) -> Printf.fprintf oc "\tCMP%s\t%s\t%s\n" at (reg x) (reg y)
      | C(i) -> Printf.fprintf oc "\tCMPI%s\t%s\t%d\n" at (reg x) i);
     if tail then
       g'_tail_if oc e1 e2 bc
     else
       g'_non_tail_if oc e1 e2 bc
  | (tail, IfF(cnd, (x, y), e1, e2)) ->
     let bc = "J" ^ cond_of_string cnd in
     Printf.fprintf oc "\tFCMP%s\t%s\t%s\n" at (reg x) (reg y);
     if tail then
       g'_tail_if oc e1 e2 bc
     else
       g'_non_tail_if oc e1 e2 bc
  | (true, Call((x, t), Id.L(l), ys)) -> (* 末尾呼び出し *)
     Printf.fprintf oc "\tJ\t:%s\n" l
  | (false, Call((x, t), Id.L(l), ys)) -> (*TODO: implement stack operation*)
     Printf.fprintf oc "\tJSUB\t:%s\n" l
and g'_tail_if oc e1 e2 bc = 
  let b_then = Id.genid (bc ^ "_then") in
  Printf.fprintf oc "\t%s\t:%s\n" bc b_then;
  g oc (true, e2);
  Printf.fprintf oc ":%s\n" b_then;
  g oc (true, e1)
and g'_non_tail_if oc e1 e2 bc = 
  let b_then = Id.genid (bc ^ "_then") in
  let b_cont = Id.genid (bc ^ "_cont") in
  Printf.fprintf oc "\t%s\t:%s\n" bc b_then;
  g oc (false, e2);
  Printf.fprintf oc "\tJ\t:%s\n" b_cont;
  Printf.fprintf oc ":%s\n" b_then;
  g oc (false, e1);
  Printf.fprintf oc ":%s\n" b_cont

let h oc { name = Id.L(x); args = _; body = e; ret = _ } =
  Printf.fprintf oc ":%s\n" x;
  g oc (true, rm_nop e)

let f oc (Prog(fundefs, e))  =
  Format.eprintf "generating assembly...@.";
  List.iter (fun fundef -> h oc fundef) fundefs;
  Format.eprintf "generating assembly...@.";  
  Printf.fprintf oc ":_min_caml_start # main entry point\n";
  g oc (false, rm_nop e);
  Printf.fprintf oc "\tJ\t0\n" 
