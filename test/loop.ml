let rec f _ = f () in
    (Array.create 1 f).(0) <- f
