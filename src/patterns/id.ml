type t = Str of string | Num of int

let next_name = ref 0

let gen_id () = 
  incr next_name;
  Num (!next_name - 1)

let id_of_string x = Str x

let string_of_id t = match t with
  | Num n -> "#" ^ string_of_int n
  | Str s -> s

let compare t1 t2 = match t1, t2 with
  | Num n1, Num n2 -> Pervasives.compare n1 n2
  | Num _, Str _ -> -1
  | Str _, Num _ -> 1
  | Str s1, Str s2 -> String.compare s1 s2
