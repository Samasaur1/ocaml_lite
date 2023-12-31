open OUnit2
open Ocaml_lite.Lexer
open Ocaml_lite.Parser
open Ocaml_lite.Interpreter

let interpreter_tests = "interpreter tests" >::: [
  "basic single binding" >::
  (fun _ -> assert_equal
    (IntLiteral 1)
    (List.assoc "x"
      (interpret (parse (tokenize "let x = 1;;")))
    )
  );
  "simple addition" >::
  (fun _ -> assert_equal
    (IntLiteral 2)
    (List.assoc "x"
      (interpret (parse (tokenize "let x = 1 + 1;;")))
    )
  );
  "simple multiplication" >::
  (fun _ -> assert_equal
    (IntLiteral 6)
    (List.assoc "x"
      (interpret (parse (tokenize "let x = 2 * 3;;")))
    )
  );
  "simple subtraction" >::
  (fun _ -> assert_equal
    (IntLiteral 2)
    (List.assoc "x"
      (interpret (parse (tokenize "let x = 5 - 3;;")))
    )
  );
  "square function (two bindings)" >::
  (fun _ -> assert_equal
    (IntLiteral 4)
    (List.assoc "y"
      (interpret (parse (tokenize "let square x = x * x;; let y = square 2;;")))
    )
  );
  "square function (let-in)" >::
  (fun _ -> assert_equal
    (IntLiteral 4)
    (List.assoc "y"
      (interpret (parse (tokenize "let y = let square x = x * x in square 2;;")))
    )
  );
  (* Parser forces you to match on only constructors *)
  (* "fibonacci" >:: (* this will fail per the spec because you can't match on literals *) *)
  (* (fun _ -> assert_equal *)
  (*   (IntLiteral 13) *)
  (*   (List.assoc "y" *)
  (*     (interpret (parse (tokenize "let rec fib x = match x with | 0 => 1 | 1 => 1 | 2 => 1 | n => fib (n-1) (n-2);; let y = fib 7;;"))) *)
  (*   ) *)
  (* ); *)
  "if-else (true)" >::
  (fun _ -> assert_equal
    (BoolLiteral true)
    (List.assoc "x"
      (interpret (parse (tokenize "let x = if 1 < 2 then true else false;;")))
    )
  );
  "if-else (false)" >::
  (fun _ -> assert_equal
    (BoolLiteral false)
    (List.assoc "x"
      (interpret (parse (tokenize "let x = if 1 = 2 then true else false;;")))
    )
  );
  "type definition binding" >::
  (fun _ -> assert_equal
    (ConstructorValue "MyInt") (* maybe unit type? *)
    (List.assoc "MyInt"
      (interpret (parse (tokenize "type t = | MyInt of int;;")))
    )
  );
  "type definition binding and assignment" >::
  (fun _ -> assert_equal
    (UserValue ("MyInt", [IntLiteral 1]))
    (List.assoc "x"
      (interpret (parse (tokenize "type t = | MyInt of int;; let x = MyInt 1;;")))
    )
  );
  (* Typechecker would catch this test *)
  (* "string + string" >:: *)
  (* (fun _ -> assert_equal *)
  (*   (IDontKnowYet) (* maybe an error? i think we can't get here, because the typechecker should have caught it *) *)
  (*   (List.assoc "x" *)
  (*     (interpret (parse (tokenize "let x = \"hello\" + \"world\";;"))) *)
  (*   ) *)
  (* ); *)
  "string concatenation" >::
  (fun _ -> assert_equal
    (StringLiteral "helloworld")
    (List.assoc "x"
      (interpret (parse (tokenize "let x = \"hello\" ^ \"world\";;")))
    )
  );
]
