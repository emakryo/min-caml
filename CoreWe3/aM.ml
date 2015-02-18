
module AM =
  Map.Make
    (struct
      type t = Asm.t
      let compare (i, _, _) (j, _, _) = compare i j
    end)
include AM

let add_list xys env = List.fold_left (fun env (x, y) -> add x y env) env xys

let of_list xys = List.fold_left (fun env (x, y) -> add x y env) AM.empty xys

(* let test () =  *)
(*   let ad = Add(("x", Type.Int), "y", V("z")) in *)
(*   let ad2 = Add(("x", Type.Int), "y", C(9)) in *)
(*   let sb = Sub(("z", Type.Int), "x", "y") in *)
(*   let e1 = new_t ad in *)
(*   let e2 = new_t ad2 in *)
(*   let e3 = new_t sb in *)
(*   let mp = AM.of_list (List.map (fun e -> (e, def_set e)) [e1; e2; e3]) in *)
(*   List.iter  *)
(*     (fun e ->  *)
(*      let u_set = AM.find e mp in *)
(*      let u_str = S.fold (fun s xs -> xs ^ " " ^ s) u_set "" in *)
(*      Format.eprintf "cardinal: %s@." u_str) [e1;e2;e3]; *)
