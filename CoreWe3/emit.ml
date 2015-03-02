open Asm

external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"
external getsgl : float -> int32 = "getsgl"

let reg r = 
  if is_reg r then 
    let p = r.[1] in
    let n = int_of_string (String.sub r 2 (String.length r - 2)) in
    Format.sprintf "%c%d" p n
  else 
    r 

type stk_frm = { map : int M.t; size : int; save_rl: bool }
let rec gather_stkset tail call_sset = function
  | [] -> call_sset
  | [e] -> gather_stkset' tail call_sset e
  | e::es ->
     gather_stkset tail (gather_stkset' false call_sset e) es
and gather_stkset' tail (call, sset) e = 
  match get_inst e with
  | If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else) ->
     gather_stkset tail (gather_stkset tail (call, sset) e_else) e_then
  | Save(_, sv) | FSave(_, sv) -> (call, S.add sv sset)
  | Call(_) -> (call || (not tail), sset)
  | _  -> (call, sset)

let mk_stk oc e top =
  let (call, sset) = gather_stkset (not top) (false, S.empty) e in
  let save_rl = call && not top in
  let (_, map) =
    S.fold (fun sv (i, senv) -> (i + 1, M.add sv i senv)) sset (1, M.empty) in
  let size = (M.cardinal map) + if call && not top then 1 else 0 in
  let sfrm = { map = map; size = size; save_rl = save_rl} in
  (if sfrm.size > 0 then
     Printf.fprintf oc "\tADDI\t%s\t%s\t%d\t#make stack frame\n" (reg reg_sp) (reg reg_sp) (-sfrm.size));
  (if sfrm.save_rl then
     Printf.fprintf oc "\tST\t%s\t%s\t%d\t#save link register\n" (reg reg_link) (reg reg_sp) (sfrm.size));
  sfrm

let rm_stk oc sfrm =
  (if sfrm.save_rl then
     Printf.fprintf oc "\tLD\t%s\t%s\t%d\t#restore link register\n" (reg reg_link) (reg reg_sp) sfrm.size);
  (if sfrm.size > 0 then
     Printf.fprintf oc "\tADDI\t%s\t%s\t%d\t#delete stack frame\n" (reg reg_sp) (reg reg_sp) sfrm.size)
	   
let rec rm_nop = function
  (* | e -> e *)
  | [] -> []
  | e::es -> (rm_nop' e) @ (rm_nop es)
and rm_nop' (i, e, b) = 
  match e with
  | Nop -> []
  | Mr((x, _), y) | FMr((x, _), y) when x == y  -> []
  | If(dest, cnd, cmp, e_then, e_else) -> 
     [(i, If(dest, cnd, cmp, rm_nop e_then, rm_nop e_else), b)]
  | IfF(dest, cnd, cmp, e_then, e_else) -> 
     [(i, IfF(dest, cnd, cmp, rm_nop e_then, rm_nop e_else), b)]
  | _ -> [(i, e, b)]

let rec g oc sfrm = function (* 命令列のアセンブリ生成 *)
  | (false, []) -> ()
  | (true, []) -> rm_stk oc sfrm; Printf.fprintf oc "\tRET\n"
  | (tail, [e]) -> g' oc sfrm (tail, e)
  | (tail, e::es) -> g' oc sfrm (false, e); g oc sfrm (tail, es)
and g' oc sfrm (tail, (i, e, b)) =  (* 各命令のアセンブリ生成 *)
  let at = if b then "@" else "" in
  (* let at = if b then "@" else "<"^(string_of_int i)^">" in *)
  match (tail, e) with
  | (false, Nop) -> 
     Printf.fprintf oc "\t%sADDI\t%s\t%s\t0\t#Nop\n" at (reg reg_zero) (reg reg_zero)
  | (false, Mr((x, t), y)) when x == y -> 
     Printf.fprintf oc "\t%sADDI\t%s\t%s\t0\t#Nop\n" at (reg x) (reg y)
  | (false, Mr((x, t), y)) -> 
     Printf.fprintf oc "\t%sADDI\t%s\t%s\t0\t#Mr\n" at (reg x) (reg y)
  | (false, FMr((x, t), y)) when x == y -> 
     Printf.fprintf oc "\t%sFADD\t%s\t%s\t%s\t#Nop\n" at (reg x) (reg y) (reg freg_zero)
  | (false, FMr((x, t), y)) -> 
     Printf.fprintf oc "\t%sFADD\t%s\t%s\t%s\t#FMr\n" at (reg x) (reg y) (reg freg_zero)
  | (false, Ld((x, t), y, i)) -> 
     Printf.fprintf oc "\t%sLD\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, St(x, y, i)) -> 
     Printf.fprintf oc "\t%sST\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, FLd((x, t), y, i)) -> 
     Printf.fprintf oc "\t%sFLD\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, FSt(x, y, i)) -> 
     Printf.fprintf oc "\t%sFST\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, Li((x, t), i)) -> 
     Printf.fprintf oc "\t%sLDI\t%s\t%ld\n" at (reg x) i
  | (false, FLi((x, t), d)) -> 
     Printf.fprintf oc "\t%sVFLDI\t%s\t%e\t#0x%lx\n" at (reg x) d (getsgl d)
  | (false, IToF((x, t), y)) -> 
     Printf.fprintf oc "\t%sITOF\t%s\t%s\n" at (reg x) (reg y)
  | (false, FToI((x, t), y)) -> 
     Printf.fprintf oc "\t%sFTOI\t%s\t%s\n" at (reg x) (reg y)
  | (false, Neg((x, t), y)) -> 
     Printf.fprintf oc "\t%sSUB\t%s\t%s\t%s\t#Neg\n" at (reg x) (reg reg_zero) (reg y)
  | (false, Add((x, t), y, V(z))) -> 
     Printf.fprintf oc "\t%sADD\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Add((x, t), y, C(i))) -> 
     Printf.fprintf oc "\t%sADDI\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, Sub((x, t), y, z)) -> 
     Printf.fprintf oc "\t%sSUB\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, And((x, t), y, z)) -> 
     Printf.fprintf oc "\t%sAND\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Or((x, t), y, z)) -> 
     Printf.fprintf oc "\t%sOR\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Shl((x, t), y, V(z))) -> 
     Printf.fprintf oc "\t%sSHL\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Shl((x, t), y, C(i))) -> 
     Printf.fprintf oc "\t%sSHLI\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, Shr((x, t), y, V(z))) -> 
     Printf.fprintf oc "\t%sSHR\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, Shr((x, t), y, C(i))) -> 
     Printf.fprintf oc "\t%sSHRI\t%s\t%s\t%d\n" at (reg x) (reg y) i
  | (false, FAdd((x, t), y, z)) -> 
     Printf.fprintf oc "\t%sFADD\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, FSub((x, t), y, z)) -> 
     Printf.fprintf oc "\t%sFSub\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, FMul((x, t), y, z)) -> 
     Printf.fprintf oc "\t%sFMUL\t%s\t%s\t%s\n" at (reg x) (reg y) (reg z)
  | (false, FInv((x, t), y)) -> 
     Printf.fprintf oc "\t%sFINV\t%s\t%s\n" at (reg x) (reg y)
  | (false, FAbs((x, t), y)) -> 
     Printf.fprintf oc "\t%sFABS\t%s\t%s\n" at (reg x) (reg y)
  | (false, Sqrt((x, t), y)) -> 
     Printf.fprintf oc "\t%sFSQRT\t%s\t%s\n" at (reg x) (reg y)
  | (false, LoadLabel((x, t), Id.L(l))) -> 
     Printf.fprintf oc "\t%sLDI\t%s\t.%s\n" at (reg x) l
  | (false, Save(x, sv)) ->
     Printf.fprintf oc "\t%sST\t%s\t%s\t%d\t#Save\n" at (reg x) (reg reg_sp) (M.find sv sfrm.map)
  | (false, Restore((x, t), sv)) ->
     Printf.fprintf oc "\t%sLD\t%s\t%s\t%d\t#Restore\n" at (reg x) (reg reg_sp) (M.find sv sfrm.map)
  | (false, FSave(x, sv)) -> 
     Printf.fprintf oc "\t%sFST\t%s\t%s\t%d\t#Save\n" at (reg x) (reg reg_sp) (M.find sv sfrm.map)
  | (false, FRestore((x, t), sv)) -> 
     Printf.fprintf oc "\t%sFLD\t%s\t%s\t%d\t#Restore\n" at (reg x) (reg reg_sp) (M.find sv sfrm.map)
  | (true, (Nop | Mr _ | FMr _ | Ld _ | St _ | FLd _ | FSt _ | Li _ | FLi _ | IToF _ | FToI _ | Neg _ | Add _ | Sub _ | And _ | Or _ | Shl _ | Shr _ | FAdd _ | FSub _ | FMul _ | FInv _ | FAbs _ | Sqrt _ (* | IAsF _ | FAsI _  *)| LoadLabel _ | Save _ | Restore _ | FSave _ | FRestore _ as e)) ->
     g' oc sfrm (false, (i, e, b));
     rm_stk oc sfrm;
     Printf.fprintf oc "\tRET\n"
  | (tail, If(dest, cnd, (x, y'), e1, e2)) ->
     let bc = "J" ^ cond_of_string cnd in
     (match y' with
      | V(y) -> Printf.fprintf oc "\t%sCMP\t%s\t%s\n" at (reg x) (reg y)
      | C(i) -> Printf.fprintf oc "\t%sCMPI\t%s\t%d\n" at (reg x) i);
     if tail then
       g'_tail_if oc sfrm e1 e2 bc
     else
       g'_non_tail_if oc sfrm  e1 e2 bc
  | (tail, IfF(dest, cnd, (x, y), e1, e2)) ->
     let bc = "J" ^ cond_of_string cnd in
     Printf.fprintf oc "\t%sFCMP\t%s\t%s\n" at (reg x) (reg y);
     if tail then
       g'_tail_if oc sfrm e1 e2 bc
     else
       g'_non_tail_if oc sfrm e1 e2 bc
  | (true, Call((x, t), Id.L(l), yts, zts)) -> (* 末尾呼び出し *)
     rm_stk oc sfrm;
     Printf.fprintf oc "\t%sJ\t:%s\t\t#%s := %s(%s)\n" at l (reg x) (reg l) (String.concat ", " (List.map (fun yt -> reg (fst yt)) (yts @ zts)))
  | (false, Call((x, t), Id.L(l), yts, zts)) -> (*TODO: implement stack operation*)
     Printf.fprintf oc "\t%sJSUB\t:%s\t\t#%s := %s(%s)\n" at l (reg x) (reg l) (String.concat ", " (List.map (fun yt -> reg (fst yt)) (yts @ zts)));
and g'_tail_if oc sfrm e1 e2 bc = 
  let b_then = Id.genid (bc ^ "_then") in
  Printf.fprintf oc "\t%s\t:%s\n" bc b_then;
  g oc sfrm (true, e2);
  Printf.fprintf oc ":%s\n" b_then;
  g oc sfrm (true, e1)
and g'_non_tail_if oc sfrm e1 e2 bc = 
  let b_then = Id.genid (bc ^ "_then") in
  let b_cont = Id.genid (bc ^ "_cont") in
  Printf.fprintf oc "\t%s\t:%s\n" bc b_then;
  g oc sfrm (false, e2);
  Printf.fprintf oc "\tJ\t:%s\n" b_cont;
  Printf.fprintf oc ":%s\n" b_then;
  g oc sfrm (false, e1);
  Printf.fprintf oc ":%s\n" b_cont  

let h oc { name = Id.L(x); args = _; body = e; ret = _ } =
  Printf.fprintf oc ":%s\n" x;
  let e = rm_nop e in
  let sfrm = mk_stk oc e false in
  g oc sfrm (true, e)

let f oc (Prog(fundefs, e))  =
  Format.eprintf "generating assembly...@.";
  List.iter (fun fundef -> h oc fundef) fundefs;
  Printf.fprintf oc ":_min_caml_start # main entry point\n";
  let e = rm_nop e in
  let sfrm = mk_stk oc e true in
  g oc sfrm (false, e);
  Printf.fprintf oc "\tJ\t0\t#halt\n" 
