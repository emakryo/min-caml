open Asm

let rec mk_igraph mps igs = function  (* 干渉グラフ *)
  | [] -> igs
  | e::es ->
     let igs =
       match get_inst e with
       | If(_, _, _, e_then, e_else) | IfF(_, _, _, e_then, e_else) ->
	  mk_igraph mps (mk_igraph mps igs e_then) e_else
       | _ -> igs in
     let liveouts = tuple2_map (Liveness.get_liveout e) mps in
     let isets =
       match get_inst e with
       | Mr(_) | FMr(_) -> tuple2_map2 S.diff liveouts (Liveness.use_set e)
       | _  -> liveouts in
     let dsets = Liveness.def_set e in
     let igs = 
       tuple2_map3 
	 (fun ig dset iset ->
	  S.fold (fun x ig ->
		  S.fold (fun y ig ->
			  UG.add_edge (x, y) ig)
			 iset ig)
		 dset ig
	 ) igs dsets isets in
     mk_igraph mps igs es

let h ({ name = Id.L(x); args = yts; body = e; ret = t } as fdef) =
  let mps = Liveness.h fdef in
  let igs = mk_igraph mps (UG.new_graph (), UG.new_graph ()) e in
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  UG.pp_graph (fst igs);
  UG.pp_graph (snd igs);
  ()

let f (Prog(fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  List.iter h fundefs;
  let s = Liveness.g e in
  Prog(fundefs, e)
