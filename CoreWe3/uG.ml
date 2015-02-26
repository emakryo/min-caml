type ugraph = {nodes : S.t; edges : S.t M.t}

let new_graph () = {nodes = S.empty; edges = M.empty}
		     
let nodes ug = ug.nodes

let adj x ug = if M.mem x ug.edges then M.find x ug.edges else S.empty

let deg x ug = S.cardinal (adj x ug)

let add_edge (x, y) ug = 
  let nds = S.add x (S.add y ug.nodes) in
  let egs = 
    if x = y then 
      ug.edges 
    else
      let adj_x = S.add y (adj x ug) in
      let adj_y = S.add x (adj y ug) in
      M.add y adj_y (M.add x adj_x ug.edges) in
  {nodes = nds; edges = egs}
let rm_edge (x, y) ug = 
  let adj_x = S.remove y (adj x ug) in
  let adj_y = S.remove x (adj y ug) in
  {ug with edges = M.add y adj_y (M.add x adj_x ug.edges)}
let has_edge (x, y) ug = 
  S.mem y (adj x ug)
let add_node x ug =
  {ug with nodes = S.add x ug.nodes}
let rm_node x ug =
  let adj_x = adj x ug in
  let egs = S.fold (fun y egs -> M.add y (S.remove x (adj y ug)) egs) adj_x ug.edges in
  {nodes = S.remove x ug.nodes; edges = M.remove x egs}

let add_prod_edges xset yset ug = 
  S.fold (fun x ug ->
	  S.fold (fun y ug ->
		  add_edge (x, y) ug)
		 yset ug)
	 xset ug

let add_adj x ys ug =
  let adj_x = adj x ug in
  {nodes = S.add x ug.nodes; edges = M.add x (S.union ys adj_x) ug.edges}

let pp_graph ug =
  S.iter
    (fun x ->
     Format.eprintf "%s -> %s@." x (String.concat ", " (S.to_list (adj x ug)))) ug.nodes
