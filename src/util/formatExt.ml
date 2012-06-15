open Format

type printer = formatter -> unit

let empty (fmt : formatter) : unit = ()
 
let nest (p : printer) (fmt : formatter) : unit =
  pp_open_vbox fmt 2;
  p fmt;
  pp_close_box fmt ()

let text s fmt = pp_print_string fmt s
 
let rec inter (sep : printer) (lst : printer list) (fmt : formatter) : unit = match lst with
    x1 :: x2 :: xs' ->
      pp_open_box fmt 2;
      x1 fmt; 
      pp_close_box fmt ();
      sep fmt;
      inter sep (x2 :: xs') fmt
  | [x] -> 
      pp_open_box fmt 2;
      x fmt;
      pp_close_box fmt ()
  | [] -> ()

let sep = inter (fun fmt -> pp_print_space fmt ())

let rec squish (lst : printer list) (fmt : formatter) : unit = match lst with
  | x :: xs -> x fmt; squish xs fmt
  | [] -> ()
 
 
let vert (p : printer list) (fmt : formatter) : unit = 
  pp_open_vbox fmt 0;
  sep p fmt;
  pp_close_box fmt ()
 
let hov n b (p : printer list) (fmt : formatter) : unit = 
  pp_open_hvbox fmt b;
  inter (fun fmt -> pp_print_break fmt n 0) p fmt;
  pp_close_box fmt ()

let horz (p : printer list) (fmt : formatter) : unit = 
  pp_open_hbox fmt ();
  sep p fmt;
  pp_close_box fmt ()
  
let horzOrVert (p : printer list) (fmt : formatter) : unit =
  pp_open_hvbox fmt 0;
  sep p fmt;
  pp_close_box fmt ()

let hnest n (p : printer) (fmt : formatter) : unit =
  pp_open_hvbox fmt n;
  p fmt;
  pp_close_box fmt ()

let print_space fmt = pp_print_space fmt ()

let hvert (p : printer list) (fmt : formatter) : unit =
  let rec intersperse a lst = match lst with
      [] -> []
    | [x] -> [x]
    | x :: xs -> x :: a :: (intersperse a xs)
  in
  hnest 2 (squish (intersperse print_space p)) fmt

let wrapBox (p : printer list) (fmt : formatter) : unit =
  pp_open_hovbox fmt 0;
  sep p fmt;
  pp_close_box fmt ()

let int n fmt = pp_print_int fmt n
 
let float f fmt = pp_print_float fmt f
 
let enclose l r (inner : printer) (fmt : formatter) = 
  pp_open_hvbox fmt 2;
  pp_print_string fmt l;
  inner fmt;
  pp_print_string fmt r;
  pp_close_box fmt ()
 
let parens = enclose "(" ")"
 
let braces = enclose "{" "}"
 
let brackets = enclose "[" "]"

let angles = enclose "<" ">"

let to_string (f : 'a -> printer) (x : 'a) : string  =
  f x str_formatter;
  flush_str_formatter ()
