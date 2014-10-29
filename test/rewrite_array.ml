let a = Array.create 1 0 in
    let x = a.(0) in
    a.(0) <- 1;
    let y = a.(0) in
    print_int x;
    print_newline ();
    print_int y    
