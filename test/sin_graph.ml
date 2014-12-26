(* let rec print_byte c = print_char (char_of_int c) in *)
(* let image_size = Array.create 2 0 in *)

let rec print_byte c = print_char c in
let rec mkcanvas _ =
  let dummy = Array.create 0 false in
  let canvas = Array.create image_size.(1) dummy in
  let rec mkline canvas j = 
    if j < image_size.(1) then
      (canvas.(j) <- Array.create image_size.(0) false;
      mkline canvas (j + 1))
    else
      canvas
  in
  mkline canvas 0
in
let rec plot canvas =
  let rec calc_j i = 
    let w = float_of_int image_size.(0) in
    let h = float_of_int image_size.(1) in
    let xmin = -6.283185307179586 in
    let xmax = 6.283185307179586 in
    let ymin = -1.1 in
    let ymax = 1.1 in
    let x = (xmax -. xmin) /. w *. (float_of_int i) +. xmin in
    let y = sin x in
    int_of_float ((ymax -. y) /. (ymax -. ymin) *. h)
  in
  let rec plot_point canvas i = 
    if i < image_size.(0) then
      let j = calc_j i in
      canvas.(j).(i) <- true;
      plot_point canvas (i + 1)
    else
      ()
  in
  plot_point canvas 0
in
let rec write_ppm_header _ =
  (print_byte 80; (* 'P' *)
   print_byte (48 + 6); (* +6 if binary *)
   print_byte 10;
   print_byte (48 + 1); (* width fixed to 128px *)
   print_byte (48 + 2);
   print_byte (48 + 8);
   print_byte 32;
   print_byte (48 + 1); (* height fixed to 128px *)
   print_byte (48 + 2);
   print_byte (48 + 8);
   print_byte 10;
   print_byte (48 + 2); 
   print_byte (48 + 5);
   print_byte (48 + 5);
   print_byte 10)
in
let rec emit canvas = 
  let rec emitpixcel canvas j i = 
    if i < image_size.(0) then
      let x = if canvas.(j).(i) then 0 else 255 in
      print_byte x;
      print_byte x;
      print_byte x;
      emitpixcel canvas j (i + 1)
    else
      ()
  in  
  let rec emitline canvas j = 
    if j < image_size.(1) then
      (emitpixcel canvas j 0;
       emitline canvas (j + 1))
    else
      ()
  in
  emitline canvas 0
in
let rec main _ = 
   image_size.(0) <- 128;
   image_size.(1) <- 128;
   let canvas = mkcanvas () in
   plot canvas;
   write_ppm_header ();
   emit canvas
in
main ()
