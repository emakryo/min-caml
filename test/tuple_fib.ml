let rec tuple_fib n accs =
  let (a1, a2) = accs in
  if n <= 1 then a1 else tuple_fib (n - 1) (a2, a2 + a1) in
print_char (tuple_fib 4 (1, 1))
