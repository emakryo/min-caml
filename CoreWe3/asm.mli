type id_or_imm = V of Id.t | C of int
and cond = Eq | LE | LT 
and t = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Ld of (Id.t * Type.t) * Id.t * int
  | St of Id.t * Id.t * int
  | FLd of (Id.t * Type.t) * Id.t * int
  | FSt of Id.t * Id.t * int
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
  | Sqrt of (Id.t * Type.t) * Id.t
  | FLi of (Id.t * Type.t) * float
  | If of cond * (Id.t * id_or_imm) * t list (*then*) * t list (*else*) 
  | IfF of cond * (Id.t * Id.t) * t list * t list
  | Call of (Id.t * Type.t) * Id.l * Id.t list
  | LoadLabel of (Id.t * Type.t) * Id.l
  | Mr of (Id.t * Type.t) * Id.t
  | FMr of (Id.t * Type.t) * Id.t
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of (Id.t * Type.t) * Id.t (* スタック変数から値を復元 *)
  | IAsF of (Id.t * Type.t) * Id.t
  | FAsI of (Id.t * Type.t) * Id.t
type fundef =
    { name : Id.l; args : Id.t list; body : t list; ret : Type.t }
type prog = Prog of fundef list * t list

val cond_of_string : cond -> string

val reg_of_int : int -> string
val freg_of_int : int -> string
val is_reg : string -> bool

val regs : Id.t array
val fregs : Id.t array
val reglist : Id.t list
val freglist : Id.t list
val reg_zero : Id.t
val reg_hp : Id.t
val reg_sp : Id.t
val hp_default : int
val sp_default : int

val fv : t list -> Id.t list

val imm_max : int
val imm_min : int

val io_addr : int
