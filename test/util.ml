let cartesian (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list =
  List.concat (List.map (fun e -> List.map (fun e' -> (e, e')) l2) l1)

let cart_sq (x : 'a list) : ('a * 'a) list = cartesian x x

let rec range_inc (a : int) (b : int) : 'a list =
  if a > b then [] else a :: range_inc (a + 1) b
