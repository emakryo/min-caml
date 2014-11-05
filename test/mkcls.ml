let rec test1 _ =
  let z = 4 in 
  let rec f x = x - z in
  f 8
in
let rec test2 _ =
  let rec g x = x - 2 in
  g 6
in
let rec test3 _ =
  let rec f x = x - 1 in
  f
in
let rec test4 _ =
  let rec g h = 
    let rec i x = h x in 
    i in
  g
in
let rec test5 _ =
  let rec i x = x in
  let z = 4 in
  let rec f x = i (z - 5) in
  if z < 6 then (i, f 7) else (f, 8)
in
let rec test6 _ =
  let rec fact x =
    if x = 1.0 then 1.0 else x *. fact (x -. 1.0) in
  fact 6.0
in
let res1 = test1 () in
let res2 = test2 () in
let res3 = test3 () in
let res4 = test4 () in
let res5 = test5 () in
let res6 = test6 () in
()
