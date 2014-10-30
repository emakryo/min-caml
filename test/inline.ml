let rec f x = 
  if x = 0 then
    0
  else
    let y = x - 1 in
    let z = f y in
    x + z in
print_int (f 10)
