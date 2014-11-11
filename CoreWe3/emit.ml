open Asm

external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"

let stackset = ref S.empty (* すでに Save された変数の集合 *)
let stackmap = ref [] (* Save された変数のスタックにおける位置 *)
let save x = 
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let savef x = 
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    (let pad = 
       if List.length !stackmap mod 2 = 0 then [] else [Id.gentmp Type.Int] in
     stackmap := !stackmap @ pad @ [x; x])
let locate x = 
  let rec loc = function 
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
  loc !stackmap
let offset x = 1 * List.hd (locate x)
let stacksize () = List.length !stackmap

let reg r = 
  if is_reg r 
  then String.sub r 1 (String.length r - 1)
  else r 

let load_label r label =
  "\tlis\t" ^ (reg r) ^ ", ha16(" ^ label ^ ")\n" ^
    "\taddi\t" ^ (reg r) ^ ", " ^ (reg r) ^ ", lo16(" ^ label ^ ")\n"

(* 関数呼び出しのために引数を並べ替える (register shuffling) *)
let rec shuffle sw xys = 
  (* remove identical moves *)
  let (_, xys) = List.partition (fun (x, y) -> x = y) xys in
    (* find acyclic moves *)
    match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
      | ([], []) -> []
      | ((x, y) :: xys, []) -> (* no acyclic moves; resolve a cyclic move *)
	  (y, sw) :: (x, y) :: 
	    shuffle sw (List.map (function 
				    | (y', z) when y = y' -> (sw, z)
				    | yz -> yz) xys)
      | (xys, acyc) -> acyc @ shuffle sw xys

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 *)
let rec g oc = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc (dest, exp)
  | (dest, Let((x, t), exp, e)) -> g' oc (NonTail (x), exp); g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 *)
  (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> ()
  | (NonTail(x), Li(i)) when (imm_min <= i) && (i < imm_max) -> 
     Printf.fprintf oc "\tADDI\t%s\tr0\t%ld\n" (reg x) i
  | (NonTail(x), Li(i)) -> 
     let n = Int32.shift_right_logical i 16 in
     let m = Int32.logxor i (Int32.shift_left n 16) in     
     Printf.fprintf oc "\tLDIH\t%s\t%ld\n" (reg x) n;
     Printf.fprintf oc "\tLDIL\t%s\t%ld\n" (reg x) m
  | (NonTail(x), SetL(Id.L(y))) -> 
     let s = load_label x y in
     Printf.fprintf oc "%s" s
  | (NonTail(x), Mr(y)) when x = y -> ()
  | (NonTail(x), Mr(y)) -> Printf.fprintf oc "\tADDI\t%s\t%s\t0\n" (reg x) (reg y)
  | (NonTail(x), Neg(y)) -> Printf.fprintf oc "\tSUB\t%s\tr0\t%s\n" (reg x) (reg y)
  | (NonTail(x), Add(y, V(z))) -> 
     Printf.fprintf oc "\tADD\t%s\t%s\t%s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Add(y, C(z))) -> 
     Printf.fprintf oc "\tADDI\t%s\t%s\t%d\n" (reg x) (reg y) z
  | (NonTail(x), Sub(y, z)) -> 
     Printf.fprintf oc "\tSUB\t%s\t%s\t%s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), And(y, z)) -> 
     Printf.fprintf oc "\tAND\t%s\t%s\t%s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Or(y, z)) -> 
     Printf.fprintf oc "\tOR\t%s\t%s\t%s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Slw(y, V(z))) -> 
     Printf.fprintf oc "\tSHL\t%s\t%s\t%s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Slw(y, C(z))) -> 
     Printf.fprintf oc "\tSHLI\t%s\t%s\t%d\n" (reg x) (reg y) z
  | (NonTail(x), Srw(y, V(z))) -> 
     Printf.fprintf oc "\tSHR\t%s\t%s\t%s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Srw(y, C(z))) -> 
     Printf.fprintf oc "\tSHRI\t%s\t%s\t%d\n" (reg x) (reg y) z
  | (NonTail(x), Lwz(y, c)) ->
     Printf.fprintf oc "\tLD\t%s\t%s\t%d\n" (reg x) (reg y) c
  | (NonTail(_), Stw(x, y, c)) ->
     Printf.fprintf oc "\tST\t%s\t%s\t%d\n" (reg x) (reg y) c
  | (NonTail(x), FNeg(y)) -> 
      Printf.fprintf oc "\tFNEG\t%s\t%s\n" (reg x) (reg y)
  | (NonTail(_), Comment(s)) -> Printf.fprintf oc "#\t%s\n" s
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y))
       when List.mem x allregs && not (S.mem y !stackset) ->
     save y;
     Printf.fprintf oc "\tST\t%s\t%s\t%d\n" (reg x) (reg reg_sp) (offset y)
     (* Printf.fprintf oc "\tPUSH\t%s\n" (reg x) *)
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) when List.mem x allregs ->
      Printf.fprintf oc "\tLD\t%s\t%s\t%d\n" (reg x) (reg reg_sp) (offset y)
  | (NonTail(x), Restore(y))->
     failwith "Only registers can be resutored.."
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Comment _ | Save _ as exp)) ->
     g' oc (NonTail(Id.gentmp Type.Unit), exp);
     Printf.fprintf oc "\tRET\n";
  | (Tail, (Li _ | SetL _ | Mr _ | Neg _ | Add _ | Sub _ | And _ | Or _ | Slw _ | Srw _ |Lwz _ | FNeg _ as exp)) -> 
     g' oc (NonTail(regs.(0)), exp);
     Printf.fprintf oc "\tRET\n";
  | (Tail, (Restore(x) as exp)) ->
     (match locate x with
      | [i] -> g' oc (NonTail(regs.(0)), exp)
      | [i; j] when (i + 1 = j) -> g' oc (NonTail(regs.(0)), exp)
      | _ -> assert false);
     Printf.fprintf oc "\tRET\n";
  | (Tail, IfEq(x, y, e1, e2)) ->
     g'_tail_if oc e1 e2 "BEQ" (reg x) (reg y)
  | (Tail, IfLE(x, y, e1, e2)) ->
     g'_tail_if oc e1 e2 "BLE" (reg x) (reg y)
  | (NonTail(z), IfEq(x, y, e1, e2)) ->
     g'_non_tail_if oc (NonTail(z)) e1 e2 "BEQ" (reg x) (reg y)
  | (NonTail(z), IfLE(x, y, e1, e2)) ->
     g'_non_tail_if oc (NonTail(z)) e1 e2 "BLE" (reg x) (reg y)
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys)) -> (* 末尾呼び出し *)
     g'_args oc [(x, reg_cl)] ys;
     Printf.fprintf oc "\tlwz\t%s, 0(%s)\n" (reg reg_sw) (reg reg_cl);
     Printf.fprintf oc "\tmtctr\t%s\n\tbctr\n" (reg reg_sw);
  | (Tail, CallDir(Id.L(x), ys)) -> (* 末尾呼び出し *)
     g'_args oc [] ys;
     Printf.fprintf oc "\tBEQ\tr0\tr0\t:%s\n" x;
  | (NonTail(a), CallCls(x, ys)) ->
     g'_args oc [(x, reg_cl)] ys;
     let ss = stacksize () in
     Printf.fprintf oc "\tstw\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
     Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
     Printf.fprintf oc "\tlwz\t%s, 0(%s)\n" reg_tmp (reg reg_cl);
     Printf.fprintf oc "\tmtctr\t%s\n" reg_tmp;
     Printf.fprintf oc "\tbctrl\n";
     Printf.fprintf oc "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss;
     Printf.fprintf oc "\tlwz\t%s, %d(%s)\n" reg_tmp (ss - 4) reg_sp;
     (if List.mem a allregs && a <> regs.(0) then 
	Printf.fprintf oc "\tmr\t%s, %s\n" (reg a) (reg regs.(0)));
     Printf.fprintf oc "\tmtlr\t%s\n" reg_tmp
  | (NonTail(a), CallDir(Id.L(x), ys)) -> 
     g'_args oc [] ys;
     let ss = stacksize () in
     Printf.fprintf oc "\tPUSH\t%s\n" (reg reg_sp);
     (if ss <> 0 then
       Printf.fprintf oc "\tADDI\t%s\t%s\t%d\n" (reg reg_sp) (reg reg_sp) ss);
     Printf.fprintf oc "\tJSUB\t:%s\n" x;
     Printf.fprintf oc "\tPOP\t%s\n" (reg reg_sp);
     (if List.mem a allregs && a <> regs.(0) then
	Printf.fprintf oc "\tADDI\t%s\t%s\t0\n" (reg a) (reg regs.(0)));
and g'_tail_if oc e1 e2 bc x y = 
  let b_then = Id.genid (bc ^ "_then") in
  Printf.fprintf oc "\t%s\t%s\t%s\t:%s\n" bc x y b_then;
  let stackset_back = !stackset in
  g oc (Tail, e2);
  Printf.fprintf oc ":%s\n" b_then;
  stackset := stackset_back;
  g oc (Tail, e1)
and g'_non_tail_if oc dest e1 e2 bc x y = 
  let b_then = Id.genid (bc ^ "_then") in
  let b_cont = Id.genid (bc ^ "_cont") in
  Printf.fprintf oc "\t%s\t%s\t%s\t:%s\n" bc x y b_then;
  let stackset_back = !stackset in
  g oc (dest, e2);
  let stackset1 = !stackset in
  Printf.fprintf oc "\tBEQ\tr0\tr0\t:%s\n" b_cont;
  Printf.fprintf oc ":%s\n" b_then;
  stackset := stackset_back;
  g oc (dest, e1);
  Printf.fprintf oc ":%s\n" b_cont;
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2
and g'_args oc x_reg_cl ys = 
  let (i, yrs) = 
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl) ys in
  List.iter
    (fun (y, r) -> Printf.fprintf oc "\tADDI\t%s\t%s\t0\n" (reg r) (reg y))
    (shuffle reg_sw yrs)

let h oc { name = Id.L(x); args = _; body = e; ret = _ } =
  Printf.fprintf oc ":%s\n" x;
  stackset := S.empty;
  stackmap := [];
  g oc (Tail, e)

let f oc (Prog(data, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  (* Printf.fprintf oc "\tBEQ\tr0\tr0\t:_min_caml_start\n"; *)
  List.iter (fun fundef -> h oc fundef) fundefs;
  Printf.fprintf oc ":_min_caml_start # main entry point\n";
  Printf.fprintf oc "\tLDI\t%s\t%ld\t#init sp\n" (reg reg_sp) sp_default;
  Printf.fprintf oc "\tLDI\t%s\t%ld\t#init hp\n" (reg reg_hp) hp_default;
  let rec readlines ic = 
    try
      let line = input_line ic in
      Printf.fprintf oc "%s\n" line;
      readlines ic
    with e -> 
      close_in_noerr ic in
  readlines (open_in "./CoreWe3/init_globals.s");
  stackset := S.empty;
  stackmap := [];
  g oc (NonTail("r0"), e);
