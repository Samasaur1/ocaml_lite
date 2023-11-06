open OUnit2
open Ocaml_lite.Lexer
open Ocaml_lite.Ast
open Ocaml_lite.Parser
open Ocaml_lite.Typechecker

let typechecker_tests = "typechecker tests" >::: [
  "basic single binding" >::
  (fun _ -> assert_equal
    (IntType)
    (List.assoc "x"
      (typecheck (parse (tokenize "let x = 1;;")))
    )
  );
  "custom type" >::
  (fun _ -> assert_equal
    (UserDeclaredType "my_type")
    (List.assoc "x"
      (typecheck (parse (tokenize "type my_type = | TypeCons;; let x = TypeCons;;")))
    )
  );
  "function type (string_of_int, explicit param forwarding)" >::
  (fun _ -> assert_equal
    (FunctionType (IntType, StringType))
    (List.assoc "f"
      (typecheck (parse (tokenize "let f x = string_of_int x;;")))
    )
  );
  "function type (string_of_int, implicit param forwarding)" >::
  (fun _ -> assert_equal
    (FunctionType (IntType, StringType))
    (List.assoc "f"
      (typecheck (parse (tokenize "let f = string_of_int;;")))
    )
  );
  "function type (custom int -> string)" >::
  (fun _ -> assert_equal
    (FunctionType (IntType, StringType))
    (List.assoc "f"
      (typecheck (parse (tokenize "let f (x: int) = \"hello, world!\";;")))
    )
  );
  "identity function" >::
  (fun _ -> assert_equal
    (UserDeclaredType "I don't know yet")
    (List.assoc "id"
      (typecheck (parse (tokenize "let id x = x;;")))
    )
  );
  "multiple bindings" >::
  (fun _ -> assert_equal
    ((IntType, BoolType))
    (
      let env = (typecheck (parse (tokenize "let x = 1;; let y = true;;"))) in
      (List.assoc "x" env, List.assoc "y" env)
    )
  );
  "calling identity function on int literal" >::
  (fun _ -> assert_equal
    (IntType)
    (List.assoc "z"
      (typecheck (parse (tokenize "let id x = x;; let z = id 5;;")))
    )
  );
  "calling identity function on int var" >::
  (fun _ -> assert_equal
    (IntType)
    (List.assoc "z"
      (typecheck (parse (tokenize "let id x = x;; let y = 5;; let z = id y;;")))
    )
  );
  "int_of_string" >::
  (fun _ -> assert_equal
    (FunctionType (StringType, IntType))
    (List.assoc "f"
      (typecheck (parse (tokenize "let f = int_of_string;;")))
    )
  );
  "print_string" >::
  (fun _ -> assert_equal
    (FunctionType (StringType, UnitType))
    (List.assoc "f"
      (typecheck (parse (tokenize "let f = print_string;;")))
    )
  );
  "string + string" >::
  (fun _ -> try
    let env = typecheck (parse (tokenize "let x = \"hello\" + \"world\";;")) in
    assert_failure ("successfully typechecked string + string as " ^ string_of_typ (List.assoc "x" env))
  with
    | TypecheckError _ -> assert_bool "" true
    | _ -> assert_failure "Unexpected error");
  "string concatenation" >::
  (fun _ -> assert_equal
    (StringType)
    (List.assoc "x"
      (typecheck (parse (tokenize "let x = \"hello\" ^ \"world\";;")))
    )
  );
  "condition" >::
  (fun _ -> assert_equal
    (BoolType)
    (List.assoc "x"
      (typecheck (parse (tokenize "let x = 1 < 2;;")))
    )
  );
  "int ^ int" >::
  (fun _ -> try
    let env = typecheck (parse (tokenize "let x = 4 ^ 2")) in
    assert_failure ("successfully typechecked int ^ int as " ^ string_of_typ (List.assoc "x" env))
  with
    | TypecheckError _ -> assert_bool "" true
    | _ -> assert_failure "Unexpected error");
  "int + bool" >::
  (fun _ -> try
    let env = typecheck (parse (tokenize "let x = 1 + true;;")) in
    assert_failure ("successfully typechecked int + bool as " ^ string_of_typ (List.assoc "x" env))
  with
    | TypecheckError _ -> assert_bool "" true
    | _ -> assert_failure "Unexpected error");
  "application of int to int" >::
  (fun _ -> try
    let env = typecheck (parse (tokenize "let x = 5 10;;")) in
    assert_failure ("successfully typechecked int-int application as " ^ string_of_typ (List.assoc "x" env))
  with
    | TypecheckError _ -> assert_bool "" true
    | _ -> assert_failure "Unexpected error");
  "match with all ints" >::
  (fun _ -> assert_equal
    (IntType)
    (List.assoc "x"
      (typecheck (parse (tokenize "type t = | A | B;; let x = (let z = A in match z with | A => 0 | B => 0);;")))
    )
  );
  "match with int and bool" >::
  (fun _ -> try
    let env = typecheck (parse (tokenize "type t = | A | B;; let x = (let z = A in match z with | A => 0 | B => true);;")) in
    assert_failure ("successfully typechecked heterogenous match statement as " ^ string_of_typ (List.assoc "x" env))
  with
    | TypecheckError _ -> assert_bool "" true
    | _ -> assert_failure "Unexpected error");
]
