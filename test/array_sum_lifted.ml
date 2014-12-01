let rec array_sum_aux acc i ar n = 
  if i < n then 
    array_sum_aux (acc + ar.(i)) (i + 1) ar n
  else
    acc in
let rec array_sum ar n =
  array_sum_aux 0 0 ar n in
let ar = Array.create 4 0 in
ar.(0) <- 1; ar.(1) <- 2; ar.(2) <- 4; ar.(3) <- 8;
print_int (array_sum ar 4)
