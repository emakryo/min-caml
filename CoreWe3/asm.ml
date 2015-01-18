(* CoreWe3 assembly with a few virtual instructions *)

type id_or_imm = V of Id.t | C of int
type t = Id.range * exp
and cond = Eq | NE | LE | LT | GE | GT
and exp = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Ld of (Id.t * Type.t) * Id.t * int
  | St of Id.t * Id.t * int
  | IToF of (Id.t * Type.t) * Id.t
  | FToI of (Id.t * Type.t) * Id.t
  | Neg of (Id.t * Type.t) * Id.t
  | Add of (Id.t * Type.t) * Id.t * id_or_imm
  | Sub of (Id.t * Type.t) * Id.t * Id.t
  | And of (Id.t * Type.t) * Id.t * Id.t
  | Or of (Id.t * Type.t) * Id.t * Id.t
  | Li of (Id.t * Type.t) * int32
  | Shl of (Id.t * Type.t) * Id.t * id_or_imm
  | Shr of (Id.t * Type.t) * Id.t * id_or_imm
  | FAdd of (Id.t * Type.t) * Id.t * Id.t
  | FSub of (Id.t * Type.t) * Id.t * Id.t
  | FMul of (Id.t * Type.t) * Id.t * Id.t
  | FInv of (Id.t * Type.t) * Id.t
  | FAbs of (Id.t * Type.t) * Id.t
  | FLi of (Id.t * Type.t) * float
  | If of cond * (Id.t * id_or_imm) * t list (*then*) * t list (*else*) * t list (*cont*) 
  | IfF of cond * (Id.t * id_or_imm) * t list * t list * t list
  | Call of (Id.t * Type.t) * Id.l * Id.t list
  | LoadLabel of (Id.t * Type.t) * Id.l
  | Mr of (Id.t * Type.t) * Id.t
  | FMr of (Id.t * Type.t) * Id.t
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of (Id.t * Type.t) * Id.t (* スタック変数から値を復元 *)
type fundef =
    { name : Id.l; args : Id.t list; body : t list; ret : Type.t }
type prog = Prog of fundef list * t

let reg_of_int i = "%r" ^ (string_of_int i)
let freg_of_int i = "%f" ^ (string_of_int i)
let is_reg x = x.[0] = '%'

let regs = Array.init (32-5) (fun i -> "%r" ^ (string_of_int (i + 3)));; (*r3-r29*)
let fregs = Array.init 32 (fun i -> "%f" ^ (string_of_int i))
let reglist = Array.to_list regs
let freglist = Array.to_list fregs
let reg_zero = "%r0"
let reg_hp = "%r1"
let reg_sp = "%r2"
let hp_default = 0x00000
let sp_default = 0x777ff

(* remove_and_uniq : S.t -> Id.t list -> Id.t list *)
let rec remove_and_uniq xs = function 
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

let fv_id_or_imm = function V (x) -> [x] | _ -> []
let rec fv_exp = function
  | Nop | Li(_) | FLi(_) | LoadLabel(_) | Restore(_) -> []
  | Ld(_, x, _) -> [x]
  | St(x, y, _) -> [x; y]
  | IToF(_, x) | FToI(_, x) | Neg(_, x) | Mr(_, x) | Save(x, _) -> [x]
  | Add(_, x, y') | Shl(_, x, y')| Shr(_, x, y') -> [x; fv_id_or_imm y']
  | Sub(_, x, y) | And(_, x, y) | Or(_, x, y) -> [x; y]
  | FAdd(_, x, y) | FSub(_, x, y) | FMul(_, x, y)  | FInv(_, x, y) -> [x; y]
  | FAbs(_, x) | FMr(, x) -> [x]
  | If(_, (x, y'), e_then, e_else, e_cont) | IfF(_, (x, y'), e_then, e_else, e_cont) -> 
    [x; fv_id_or_imm y'] @ (remove_and_uniq S.empty (fv e_then @ fv e_else)) @ (fv e_cont)
  | Call (_, xs) -> xs
and fv = function 
  | [] -> []
  | (r, e)::e_rest -> (fv_exp e)@(fv e_rest)

let imm_max = 0x7fff
let imm_min = 0x8000
