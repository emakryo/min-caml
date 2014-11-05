(* PowerPC assembly with a few virtual instructions *)

type id_or_imm = V of Id.t | C of int
type t = (* ̿����� *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
and exp = (* ��İ�Ĥ�̿����б����뼰 *)
  | Nop
  | Li of int32
  (* | FLi of Id.l *)
  | SetL of Id.l
  | Mr of Id.t
  | Neg of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * Id.t
  | And of Id.t * Id.t
  | Or of Id.t * Id.t
  | Slw of Id.t * Id.t
  | Srw of Id.t * Id.t
  | Lwz of Id.t * int
  | Stw of Id.t * Id.t * int
  (* | FMr of Id.t  *)
  (* | FNeg of Id.t *)
  (* | FAdd of Id.t * Id.t *)
  (* | FSub of Id.t * Id.t *)
  (* | FMul of Id.t * Id.t *)
  (* | FDiv of Id.t * Id.t *)
  (* | Lfd of Id.t * id_or_imm *)
  (* | Stfd of Id.t * Id.t * id_or_imm *)
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  (* | IfGE of Id.t * id_or_imm * t * t *)
  (* | IfFEq of Id.t * Id.t * t * t *)
  (* | IfFLE of Id.t * Id.t * t * t *)
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list
  | CallDir of Id.l * Id.t list
  | Save of Id.t * Id.t (* �쥸�����ѿ����ͤ򥹥��å��ѿ�����¸ *)
  | Restore of Id.t (* �����å��ѿ������ͤ����� *)
type fundef =
    { name : Id.l; args : Id.t list; body : t; ret : Type.t }
(* �ץ���������� = ��ư���������ơ��֥� + �ȥåץ�٥�ؿ� + �ᥤ��μ� *)
type prog = Prog of (Id.l * float) list * fundef list * t

(* shorthand of Let for float *)
(* fletd : Id.t * exp * t -> t *)
let fletd (x, e1, e2) = Let ((x, Type.Float), e1, e2)
(* shorthand of Let for unit *)
(* seq : exp * t -> t *)
let seq (e1, e2) = Let ((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs = [| "%r3";  "%r4"; "%r5"; "%r6"; "%r7"; "%r8"; "%r9"; "%r10"; "%r11"; "%r12"; "%r13"; "%r14"|]
(* let regs = Array.init 27 (fun i -> Printf.sprintf "_R_%d" i) *)
(* let fregs = Array.init 32 (fun i -> Printf.sprintf "%%f%d" i) *)
let allregs = Array.to_list regs
(* let allfregs = Array.to_list fregs *)
let reg_cl = regs.(Array.length regs - 1) (* closure address *)
let reg_sw = regs.(Array.length regs - 2) (* temporary for swap *)
(* let reg_fsw = fregs.(Array.length fregs - 1) (\* temporary for swap *\) *)
let reg_hp = "%r2"
let reg_sp = "%r1"
let reg_tmp = "%r15"

(* is_reg : Id.t -> bool *)
let is_reg x = x.[0] = '%'

(* remove_and_uniq : S.t -> Id.t list -> Id.t list *)
let rec remove_and_uniq xs = function 
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(* free variables in the order of use (for spilling) *)
(* fv_id_or_imm : id_or_imm -> Id.t list *)
let fv_id_or_imm = function V (x) -> [x] | _ -> []
(* fv_exp : Id.t list -> t -> S.t list *)
let rec fv_exp = function
  | Nop | Li (_) (* | FLi (_) *) | SetL (_) | Comment (_) | Restore (_) -> []
  | Mr (x) | Neg (x) (* | FMr (x) | FNeg (x) *) | Save (x, _) -> [x]
  | Add (x, y') ->
	x :: fv_id_or_imm y'
  (* | Lfd (x, y')  *)| Lwz (x, y') -> [x]
  | Sub (x, y) | And (x, y) | Or (x, y) | Slw (x, y) | Srw (x, y) ->
      [x; y]
  (* | FAdd (x, y) | FSub (x, y) | FMul (x, y) | FDiv (x, y) -> *)
  (*     [x; y] *)
  | Stw (x, y, z') (* | Stfd (x, y, z')  *)-> [x; y]
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) (* | IfGE (x, y', e1, e2) *) -> 
    [x; y'] @ remove_and_uniq S.empty (fv e1 @ fv e2)
  (* | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) -> *)
  (*     x :: y :: remove_and_uniq S.empty (fv e1 @ fv e2) *)
  | CallCls (x, ys) -> x :: ys
  | CallDir (_, ys) -> ys 
and fv = function 
  | Ans (exp) -> fv_exp exp
  | Let ((x, t), exp, e) ->
      fv_exp exp @ remove_and_uniq (S.singleton x) (fv e)

(* fv : t -> Id.t list *)
let fv e = remove_and_uniq S.empty (fv e)

(* concat : t -> Id.t * Type.t -> t -> t *)
let rec concat e1 xt e2 = match e1 with
  | Ans (exp) -> Let (xt, exp, e2)
  | Let (yt, exp, e1') -> Let (yt, exp, concat e1' xt e2)

(* align : int -> int *)
let align i = if i mod 8 = 0 then i else i + 4

let imm_max = Int32.of_int 0x8000
let imm_min = Int32.of_int (-0x8000)

let letbigimm i = 
  let n = Int32.shift_right_logical i 16 in
  let m = Int32.logxor i (Int32.shift_left n 16) in
  let sft = Id.genid "sft" in
  let hi1 = Id.genid "hi" in
  let hi2 = Id.genid "hi" in
  let lo1 = Id.genid "lo" in
  let lo2 = Id.genid "lo" in
  let lo3 = Id.genid "lo" in
  Let ((sft, Type.Int), Li (Int32.of_int 16), 
       Let ((hi1, Type.Int), Li n, 
	    Let ((hi2, Type.Int), Slw (hi1, sft), 
		 Let ((lo1, Type.Int), Li m, 
		      Let ((lo2, Type.Int), Slw (lo1, sft), 
			   Let ((lo3, Type.Int), Srw (lo2, sft), 
				Ans (Or (hi2, lo3))))))))