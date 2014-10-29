let rec f x y z = 
  let z = x + y + z in
  let w = x + y + z in
  (z, w, x + y + z) in
    let (x, y, z) = f 2 4 5 in
    print_int (x + y + z)
