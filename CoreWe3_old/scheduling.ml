open Asm

type vertex = Vertex of (Id.t * Type.t) option * exp * int ref
and edge = Edge of vertex * vertex

let rec mkgraph (vtx, edg) t = 
  match t with 
  | Ans (exp) -> ([(None, exp, 0)], [])
  | Let (xt, exp, t) -> 
     (Some xt, exp, [], 0)

let f (Prog(data, fundefs, e)) = 
  let fundefs' = List.map h fundefs in
  let e', regenv' = g (Id.gentmp Type.Unit, Type.Unit) (Ans(Nop)) M.empty e in
  Prog(data, fundefs', e')
