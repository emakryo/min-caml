type igraph = string M.t 

let new_graph () = M.empty

let adj x ig = if M.mem x ig then M.find x ig else S.empty

let deg x ig = S.cardinal (adj x ig)

let add_edge (x, y) ig = 
  if x = y then 
    ig 
  else
    let adj_x = S.add y (adj x ig) in
    let adj_y = S.add x (adj y ig) in
    M.add y adj_y (M.add x adj_x ig)
let rm_edge (x, y) ig = 
  let adj_x = S.remove y (adj x ig) in
  let adj_y = S.remove x (adj y ig) in
  M.add y adj_y (M.add x adj_x ig)

let pp_graph ig =
  M.iter
    (fun x adj_x ->
     Format.eprintf "%s -> %s@." x (String.concat ", " (S.to_list adj_x))) ig
