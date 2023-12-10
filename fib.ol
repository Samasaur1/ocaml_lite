(* This is a pain to implement because you can't match on literals in OCaml_lite *)
let rec fib (i: int): int =
    if i < 0
    then 0
    else
        (if i = 0
        then 0
        else
            (if i = 1
            then 1
            else
                (if i = 2
                then 1
                else
                    let prev = fib (i - 1) in
                    let prev_prev = fib (i - 2) in
                    prev + prev_prev
                )
            )
        );;

let fifth_fib = fib 5;;

let u = print_string ("The fifth Fibonnaci number is " ^ string_of_int fifth_fib);;
let u = print_string ("The tenth Fibonnaci number is " ^ string_of_int (fib 10));;
