(* CoreWe3 assembly with a few virtual instructions *)

external getflt : int32 -> float = "getflt"

type id_or_imm = V of Id.t | C of int
and dest = Id.t * Type.t
and cond = Eq | LE | LT 
and t = int * inst * bool (*ノードid * 命令 * 依存フラグ*)
and inst = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Ld of dest * Id.t * int
  | St of Id.t * Id.t * int
  | FLd of dest * Id.t * int
  | FSt of Id.t * Id.t * int
  | IToF of dest * Id.t
  | FToI of dest * Id.t
  | Floor of dest * Id.t
  | Neg of dest * Id.t
  | Add of dest * Id.t * id_or_imm
  | Sub of dest * Id.t * Id.t
  | And of dest * Id.t * Id.t
  | Or of dest * Id.t * Id.t
  | Li of dest * int32
  | Shl of dest * Id.t * id_or_imm
  | Shr of dest * Id.t * id_or_imm
  | FAdd of dest * Id.t * Id.t
  | FSub of dest * Id.t * Id.t
  | FMul of dest * Id.t * Id.t
  | FInv of dest * Id.t
  | FAbs of dest * Id.t
  | Sqrt of dest * Id.t
  | FLi of dest * float
  | If of dest * cond * (Id.t * id_or_imm) * t list (*then*) * t list (*else*) 
  | IfF of dest * cond * (Id.t * Id.t) * t list * t list
  | Call of dest * Id.l * dest list (*args*) * dest list (*fargs*)
  | LoadLabel of dest * Id.l
  | Mr of dest * Id.t
  | FMr of dest * Id.t
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of dest * Id.t (* スタック変数から値を復元 *)
  | FSave of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | FRestore of dest * Id.t (* スタック変数から値を復元 *)
type fundef =
    { name : Id.l; args : (Id.t * Type.t) list; fargs : (Id.t * Type.t) list; body : t list; ret : Type.t }
type prog = Prog of fundef list * t list

let cond_of_string = function
  | Eq -> "EQ" 
  | LE -> "LE"
  | LT -> "LT"

let foldr_by_type fi fl xts acc =
  List.fold_right (fun (x, t) acc -> 
		   match t with
		   | Type.Unit -> acc
		   | Type.Float -> fl (x, t) acc
		   | _ -> fi (x, t) acc) xts acc
let foldr_tup_by_type f xts accs =
  foldr_by_type 
    (fun xt (acci, accf) -> (f xt acci, accf)) 
    (fun xt (acci, accf) -> (acci, f xt accf))
    xts accs
let partition_by_type xts =
  foldr_tup_by_type (fun xt xts -> xt::xts) xts ([], [])

let tuple2_map f (x, y) = (f x, f y)
let tuple2_map2 f (x1, y1) (x2, y2) = (f x1 x2, f y1 y2)
let tuple2_map3 f (x1, y1) (x2, y2) (x3, y3) = (f x1 x2 x3, f y1 y2 y3)
let tuple2_map4 f (x1, y1) (x2, y2) (x3, y3) (x4, y4) = (f x1 x2 x3 x4, f y1 y2 y3 y4)

let counter = ref 0
let new_id () = incr counter; !counter

let new_t e = (new_id (), e, false)

let get_inst (i, e, b) = e
let get_id (i, e, b) = i
let get_flag (i, e, b) = b
let get_dests e = 
  match get_inst e with
  | Nop | St(_) | FSt(_)| Save(_) | FSave(_) ->
     []
  | Ld(xt, _, _) | FLd(xt, _, _) | IToF(xt, _) | FToI(xt, _) | Floor(xt, _) | Neg(xt, _) | Add(xt, _, _) | Sub(xt, _, _) | And(xt, _, _) | Or(xt, _, _) | Li(xt, _) | Shl(xt, _, _) | Shr(xt, _, _) | FAdd(xt, _, _) | FSub(xt, _, _) | FMul(xt, _, _) | FInv(xt, _) | FAbs(xt, _) | Sqrt(xt, _) | FLi(xt, _)  | If(xt, _, _, _, _) | IfF(xt, _, _, _, _) | Call(xt, _, _, _) | LoadLabel(xt, _) | Mr(xt, _) | FMr(xt, _) | Restore(xt, _) | FRestore(xt, _) ->
     [xt]

let reg_of_int i = "%r" ^ (Format.sprintf "%02d" i)
let freg_of_int i = "%f" ^ (Format.sprintf "%02d" i)

let reg_zero = reg_of_int 0
let reg_hp = reg_of_int 1
let reg_sp = reg_of_int 2
let reg_cond = reg_of_int 30
let reg_link = reg_of_int 31
let freg_zero = freg_of_int 0
let hp_default = 0x00000
let sp_default = 0xfdfff

let special_regs = [reg_hp; reg_sp; reg_cond; reg_link]
let allregs = Array.init 32 (fun i -> reg_of_int i)
let allfregs = Array.init 32 (fun i -> freg_of_int i)
let constregs = ref [(0, reg_zero)]
let constfregs = ref [(0.0, freg_zero)]
let regs () = Array.sub allregs 3 (32 - 2 - 2 - (List.length !constregs))
let fregs () = Array.sub allfregs 1 (32 - (List.length !constfregs))
let reglist () = Array.to_list (regs ())
let freglist () = Array.to_list (fregs ())
let regset () = S.of_list (reglist ())
let fregset () = S.of_list (freglist ())

let add_constreg x = 
  Format.eprintf "constreg %d@." x;
  let i = 30 - (List.length !constregs) in
  constregs := (x, reg_of_int i)::(!constregs)  
let add_constfreg x = 
  Format.eprintf "constreg %e@." x;
  let i = 32 - (List.length !constfregs) in
  constfregs := (x, freg_of_int i)::(!constfregs)
let add_constfreg_hex x = 
  add_constfreg (getflt x)
  
let is_reg x = x.[0] = '%'
let ret_reg = function
  | Type.Float -> (fregs ()).(0)
  | Type.Unit -> reg_zero
  | _ -> (regs ()).(0)

let move_reg (x, t) y = 
  match t with
  | Type.Unit -> Nop
  | Type.Float -> FMr((x, t), y)
  | _ -> Mr((x, t), y)

(* remove_and_uniq : S.t -> Id.t list -> Id.t list *)
let rec remove_and_uniq xs = function 
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

let fv_id_or_imm = function V (x) -> [x] | _ -> []
let rec fv_exp = function
  | Nop | Li(_) | FLi(_) | LoadLabel(_) | Restore(_)| FRestore(_) -> []
  | Ld(_, x, _) | FLd(_, x, _) | IToF(_, x) | FToI(_, x) | Floor(_, x) | Neg(_, x)  | FInv(_, x) | FAbs(_, x) | Sqrt(_, x) | Mr(_, x) | Save(x, _) | FSave(x, _) | FMr(_, x) -> 
     [x]
  | St(x, y, _) | FSt(x, y, _) | Sub(_, x, y) | And(_, x, y) | Or(_, x, y) | FAdd(_, x, y) | FSub(_, x, y) | FMul(_, x, y) -> 
     [x; y]  
  | Add(_, x, y') | Shl(_, x, y')| Shr(_, x, y') -> 
     x :: (fv_id_or_imm y')
  | If(_, _, (x, y'), e_then, e_else) ->
     x :: (fv_id_or_imm y') @ (remove_and_uniq S.empty (fv e_then @ fv e_else))
  | IfF(_, _, (x, y), e_then, e_else) -> 
     [x; y] @ (remove_and_uniq S.empty (fv e_then @ fv e_else))
  | Call (_, _, yts, zts) -> 
     (List.map fst yts) @ (List.map fst zts)
and fv = function 
  | [] -> []
  | (_, e, _)::e_rest -> (fv_exp e) @ (fv e_rest)

let ext_env env e = M.add_list (get_dests e) env

let imm_max = 32768

let io_addr = -1
