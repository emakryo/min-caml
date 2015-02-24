(* CoreWe3 assembly with a few virtual instructions *)

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

let cond_of_string = function
  | Eq -> "EQ" 
  | LE -> "LE"
  | LT -> "LT"

let counter = ref 0
let new_id () = incr counter; !counter

let new_t e = (new_id (), e, false)

let get_inst (i, e, b) = e

let reg_of_int i = "%r" ^ (string_of_int i)
let freg_of_int i = "%f" ^ (string_of_int i)

let regs = Array.init (32-5) (fun i -> reg_of_int (i + 3));; (*r3-r29*)
let fregs = Array.init (32-1) (fun i -> freg_of_int (i + 1))
let reglist = Array.to_list regs
let freglist = Array.to_list fregs
let reg_zero = reg_of_int 0
let reg_hp = reg_of_int 1
let reg_sp = reg_of_int 2
let reg_cond = reg_of_int 30
let reg_link = reg_of_int 31
let freg_zero = freg_of_int 0
let hp_default = 0x00000
let sp_default = 0x777ff

let is_reg x = x.[0] = '%'
let ret_reg = function
  | Type.Float -> fregs.(0)
  | Type.Unit -> reg_zero
  | _ -> regs.(0)

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
  | Nop | Li(_) | FLi(_) | LoadLabel(_) | Restore(_) -> []
  | Ld(_, x, _) | FLd(_, x, _) | IToF(_, x) | FToI(_, x) (* | IAsF(_, x) | FAsI(_, x) *) | Neg(_, x)  | FInv(_, x) | FAbs(_, x) | Sqrt(_, x) | Mr(_, x) | Save(x, _) | FMr(_, x) -> 
     [x]
  | St(x, y, _) | FSt(x, y, _) | Sub(_, x, y) | And(_, x, y) | Or(_, x, y) | FAdd(_, x, y) | FSub(_, x, y) | FMul(_, x, y) -> 
     [x; y]  
  | Add(_, x, y') | Shl(_, x, y')| Shr(_, x, y') -> 
     x :: (fv_id_or_imm y')
  | If(_, _, (x, y'), e_then, e_else) ->
     x :: (fv_id_or_imm y') @ (remove_and_uniq S.empty (fv e_then @ fv e_else))
  | IfF(_, _, (x, y), e_then, e_else) -> 
     [x; y] @ (remove_and_uniq S.empty (fv e_then @ fv e_else))
  | Call (_, _, xs) -> 
     xs
and fv = function 
  | [] -> []
  | (_, e, _)::e_rest -> (fv_exp e)@(fv e_rest)

let imm_max = 0x7fff
let imm_min = 0x8000

let io_addr = 0xFFFFF
