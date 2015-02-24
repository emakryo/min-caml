type id_or_imm = V of Id.t | C of int
and dest = Id.t * Type.t
and stkvar = Vr of Id.t | I of int | F of float
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
  | Call of dest * Id.l * Id.t list
  | LoadLabel of dest * Id.l
  | Mr of dest * Id.t
  | FMr of dest * Id.t
  | Save of Id.t * stkvar (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of dest * stkvar (* スタック変数から値を復元 *)
  (* | IAsF of dest * Id.t *)
  (* | FAsI of dest * Id.t *)
type fundef =
    { name : Id.l; args : Id.t list; body : t list; ret : Type.t }
type prog = Prog of fundef list * t list

val cond_of_string : cond -> string

val new_id : unit -> int
val new_t : inst -> t

val get_inst : t -> inst

val reg_of_int : int -> string
val freg_of_int : int -> string

val regs : Id.t array
val fregs : Id.t array
val reglist : Id.t list
val freglist : Id.t list
val reg_zero : Id.t
val reg_hp : Id.t
val reg_sp : Id.t
val reg_cond : Id.t
val reg_link : Id.t
val freg_zero : Id.t
val hp_default : int
val sp_default : int

val is_reg : string -> bool
val ret_reg : Type.t -> string
val move_reg : (Id.t * Type.t) -> Id.t -> inst

val fv_id_or_imm : id_or_imm -> Id.t list
val fv : t list -> Id.t list

val imm_max : int
val imm_min : int

val io_addr : int
