let rec array_sum ar n =
  let rec array_sum_aux acc i = 
    if i < n then 
      array_sum_aux (acc + ar.(i)) (i + 1)	  
    else 
      acc in
  array_sum_aux 0 0 in
let ar = Array.create 4 0 in
ar.(0) <- 1; ar.(1) <- 2; ar.(2) <- 4; ar.(3) <- 8;
print_int (array_sum ar 4)
