
type id_or_imm = V of Id.t | C of int
and dest = Id.t * Type.t
and cond = Eq | LE | LT 
and t = int * inst * bool (*�Ρ���id * ̿�� * ��¸�ե饰*)
and inst = (* ��İ�Ĥ�̿����б����뼰 *)
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
  | Call of dest * Id.l * (Id.t * Type.t) list
  | LoadLabel of dest * Id.l
  | Mr of dest * Id.t
  | FMr of dest * Id.t
  | Save of Id.t * Id.t (* �쥸�����ѿ����ͤ򥹥��å��ѿ�����¸ *)
  | Restore of dest * Id.t (* �����å��ѿ������ͤ����� *)
  | FSave of Id.t * Id.t (* �쥸�����ѿ����ͤ򥹥��å��ѿ�����¸ *)
  | FRestore of dest * Id.t (* �����å��ѿ������ͤ����� *)
type fundef =
    { name : Id.l; args : (Id.t * Type.t) list; body : t list; ret : Type.t }
type prog = Prog of fundef list * t list

val cond_of_string : cond -> string

val foldr_by_type : (dest -> 'b -> 'b) -> (dest -> 'b -> 'b) -> dest list -> 'b -> 'b
val foldr_tup_by_type : (dest -> 'b -> 'b) -> dest list -> 'b * 'b -> 'b * 'b
val partition_by_type :  dest list -> dest list * dest list

val tuple2_map : ('a -> 'b) -> 'a * 'a -> 'b * 'b 
val tuple2_map2 : ('a -> 'b -> 'c) -> 'a * 'a -> 'b * 'b -> 'c * 'c
val tuple2_map3 : ('a -> 'b -> 'c -> 'd) -> 'a * 'a -> 'b * 'b -> 'c * 'c -> 'd * 'd
val tuple2_map4 : ('a -> 'b -> 'c -> 'd -> 'e) -> 'a * 'a -> 'b * 'b -> 'c * 'c -> 'd * 'd -> 'e * 'e

val new_id : unit -> int
val new_t : inst -> t

val get_inst : t -> inst
val get_id : t -> int
val get_flag : t -> bool
val get_dests : t -> dest list

val reg_of_int : int -> string
val freg_of_int : int -> string

val regs : Id.t array
val fregs : Id.t array
val reglist : Id.t list
val freglist : Id.t list
val regset : S.t
val fregset : S.t
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

val ext_env : Type.t M.t -> t -> Type.t M.t

val imm_max : int
val imm_min : int

val io_addr : int
