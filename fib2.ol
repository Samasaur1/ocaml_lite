type number =
    | Zero
    | Succ of number;;

let rec number_of_int (i: int): number =
    if i < 0 then Zero else
        (if i = 0 then Zero else
            let prev = number_of_int (i-1) in
            Succ prev
        );;

(* This is actually _still_ a pain because you can't easily nest match exprs *)
let rec fib (n: number): int =
    match n with
    | Zero => 0
    | Succ np => (match np with
        | Zero => (* i.e. 1 *) 1
        | Succ npp => (match npp with
            | Zero => (* i.e. 2 *) 1
            | Succ nppp => let prev = fib np in let prev_prev = fib npp in prev + prev_prev
            )
        );;

let u = print_string ("The fifth Fibonacci number is " ^ string_of_int (fib (number_of_int 5)));;
let u = print_string ("The tenth Fibonacci number is " ^ string_of_int (fib (number_of_int 10)));;
