open OUnit2
open Util
open Ocaml_lite.Ast
open Ocaml_lite.Lexer
open Ocaml_lite.Parser
open Ocaml_lite.Typecheck

let typecheck_code (s : string) : env = typecheck (parse (tokenize s))

let rec reorder_polytypes (t : typ) (pol : int list) : typ =
  let rec help = function
    | TVar v when List.memq v pol -> [ v ]
    | TVar _ | TInt | TBool | TString | TUnit | TId _ -> []
    | TProduct ts -> map_concat_uniq help ts
    | TArrow (ta, tb) -> merge_uniq (help ta) (help tb)
  in
  match t with
  | PolyType (v, t) ->
      if List.memq v pol then
        failwith ("Type " ^ ty_to_string (TVar v) ^ " appears twice in list")
      else reorder_polytypes t (v :: pol)
  | MonoType t -> add_foralls t (help t)

let rec types_eq' (t1 : typ) (t2 : typ) : bool =
  match (t1, t2) with
  | PolyType (v1, t1), PolyType (v2, t2) ->
      let vn = gen_tidx () in
      types_eq' (subst_tval v1 vn t1) (subst_tval v2 vn t2)
  | MonoType t1, MonoType t2 -> t1 = t2
  | _ -> false

let types_eq (t1 : typ) (t2 : typ) : bool =
  types_eq' (reorder_polytypes t1 []) (reorder_polytypes t2 [])

(* TODO: Test unequal types *)

let test_type_cmp_simple _ =
  List.iter
    (fun x ->
      assert_equal (MonoType x) (MonoType x) ~printer:typ_to_string
        ~cmp:types_eq)
    [ TInt; TBool; TString; TUnit ]

let test_type_ne_simple _ =
  List.iter
    (fun (x, y) ->
      if x <> y then
        assert_equal (MonoType x) (MonoType y) ~printer:typ_to_string
          ~cmp:(negate_bifunc types_eq) ~msg:"Types were unexpectedly equal")
    (cart_sq [ TInt; TBool; TString; TUnit ])

let test_type_cmp_tid _ =
  List.iter
    (fun x ->
      assert_equal (MonoType (TId x)) (MonoType (TId x)) ~printer:typ_to_string
        ~cmp:types_eq)
    [ "a"; "foo"; "test" ]

let test_type_cmp_one_poly _ =
  let t1 = gen_tidx () in
  assert_equal
    (PolyType (t1, MonoType (TVar t1)))
    (PolyType (t1, MonoType (TVar t1)))
    ~printer:typ_to_string ~cmp:types_eq

let test_type_cmp_rename _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (PolyType (t1, MonoType (TVar t1)))
    (PolyType (t2, MonoType (TVar t2)))
    ~printer:typ_to_string ~cmp:types_eq

let test_type_cmp_swap _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (PolyType (t1, PolyType (t2, MonoType (TArrow (TVar t1, TVar t2)))))
    (PolyType (t2, PolyType (t1, MonoType (TArrow (TVar t1, TVar t2)))))
    ~printer:typ_to_string ~cmp:types_eq

let test_type_cmp_rename_shadow _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (PolyType (t1, PolyType (t2, MonoType (TArrow (TVar t1, TVar t2)))))
    (PolyType (t2, PolyType (t1, MonoType (TArrow (TVar t2, TVar t1)))))
    ~printer:typ_to_string ~cmp:types_eq

let test_type_cmp_rename_swap _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  let t3 = gen_tidx () in
  assert_equal
    (PolyType
       ( t1,
         PolyType
           ( t2,
             PolyType
               (t3, MonoType (TArrow (TVar t1, TArrow (TVar t2, TVar t3)))) ) ))
    (PolyType
       ( t2,
         PolyType
           ( t1,
             PolyType
               (t3, MonoType (TArrow (TVar t3, TArrow (TVar t1, TVar t2)))) ) ))
    ~printer:typ_to_string ~cmp:types_eq

let test_typecheck_simple _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = () ;;"))
    (MonoType TUnit) ~printer:typ_to_string ~cmp:types_eq

let test_typecheck_number _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = 0 ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_typecheck_bool _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = true ;;"))
    (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq;
  assert_equal
    (get_type "a" (typecheck_code "let a = false ;;"))
    (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq

let test_typecheck_string _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = \"str\" ;;"))
    (MonoType TString) ~printer:typ_to_string ~cmp:types_eq

let test_simple_infer _ =
  assert_equal
    (get_type "b" (typecheck_code "let a = 0 ;; let b = a ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_simple_func _ =
  assert_equal
    (get_type "a" (typecheck_code "let a (b : int) = 0 ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_simple_lambda _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun (x : int) => 0 ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_arg_infer _ =
  assert_equal
    (get_type "a" (typecheck_code "let a (b : string) = b ;;"))
    (MonoType (TArrow (TString, TString)))
    ~printer:typ_to_string ~cmp:types_eq

let test_funcall _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let f (x : int) : int = x ;; let a = f 1 ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_multiarg_func _ =
  assert_equal
    (get_type "a" (typecheck_code "let a (b : int) (c : string) = b ;;"))
    (MonoType (TArrow (TInt, TArrow (TString, TInt))))
    ~printer:typ_to_string ~cmp:types_eq

let test_int_binops _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a = 1 " ^ x ^ " 1 ;;")))
        (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq)
    [ "+"; "-"; "*"; "/"; "mod" ]

let test_int_binop_fns _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a x y = x " ^ x ^ " y ;;")))
        (MonoType (TArrow (TInt, TArrow (TInt, TInt))))
        ~printer:typ_to_string ~cmp:types_eq)
    [ "+"; "-"; "*"; "/"; "mod" ]

let test_cmp_binops _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a = 1 " ^ x ^ " 1 ;;")))
        (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq)
    [ "<"; "=" ]

let test_lt_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x y = x < y ;;"))
    (MonoType (TArrow (TInt, TArrow (TInt, TBool))))
    ~printer:typ_to_string ~cmp:types_eq

let test_eq_fn _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x y = x = y ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TArrow (TVar t1, TBool)))))
    ~printer:typ_to_string ~cmp:types_eq

let test_str_concat _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = \"foo\" ^ \"bar\" ;;"))
    (MonoType TString) ~printer:typ_to_string ~cmp:types_eq

let test_str_concat_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x y = x ^ y ;;"))
    (MonoType (TArrow (TString, TArrow (TString, TString))))
    ~printer:typ_to_string ~cmp:types_eq

let test_logical_binops _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a = true " ^ x ^ " false ;;")))
        (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq)
    [ "&&"; "||" ]

let test_logical_binop_fns _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a x y = x " ^ x ^ " y ;;")))
        (MonoType (TArrow (TBool, TArrow (TBool, TBool))))
        ~printer:typ_to_string ~cmp:types_eq)
    [ "&&"; "||" ]

let test_lognot _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = not true ;;"))
    (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq

let test_lognot_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = not x ;;"))
    (MonoType (TArrow (TBool, TBool)))
    ~printer:typ_to_string ~cmp:types_eq

let test_bitnot _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = ~1 ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_bitnot_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = ~x ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_intstr _ =
  assert_equal
    (get_type "int_of_string" (typecheck_code ""))
    (MonoType (TArrow (TString, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_strint _ =
  assert_equal
    (get_type "string_of_int" (typecheck_code ""))
    (MonoType (TArrow (TInt, TString)))
    ~printer:typ_to_string ~cmp:types_eq

let test_print _ =
  assert_equal
    (get_type "print_string" (typecheck_code ""))
    (MonoType (TArrow (TString, TUnit)))
    ~printer:typ_to_string ~cmp:types_eq

(* TODO: Redefine builtin functions *)

let test_id_fn _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = x ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TVar t1))))
    ~printer:typ_to_string ~cmp:types_eq

let test_const_fn _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = 0 ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TInt))))
    ~printer:typ_to_string ~cmp:types_eq

let test_multi_gens _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x y = true ;;"))
    (PolyType
       (t1, PolyType (t2, MonoType (TArrow (TVar t1, TArrow (TVar t2, TBool))))))
    ~printer:typ_to_string ~cmp:types_eq

let test_mixed_generic _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x y = x + 1 ;;"))
    (PolyType (t1, MonoType (TArrow (TInt, TArrow (TVar t1, TInt)))))
    ~printer:typ_to_string ~cmp:types_eq

let test_recursion _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a x = a x ;;"))
    (PolyType (t1, PolyType (t2, MonoType (TArrow (TVar t1, TVar t2)))))
    ~printer:typ_to_string ~cmp:types_eq

let test_recurse_fun _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a = fun x => a x ;;"))
    (PolyType (t1, PolyType (t2, MonoType (TArrow (TVar t1, TVar t2)))))
    ~printer:typ_to_string ~cmp:types_eq

let test_multiarg_rec _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  let t3 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a x y = a x y ;;"))
    (PolyType
       ( t1,
         PolyType
           ( t2,
             PolyType
               (t3, MonoType (TArrow (TVar t1, TArrow (TVar t2, TVar t3)))) ) ))
    ~printer:typ_to_string ~cmp:types_eq

let test_multiarg_rec_fun _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  let t3 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a = fun x y => a x y ;;"))
    (PolyType
       ( t1,
         PolyType
           ( t2,
             PolyType
               (t3, MonoType (TArrow (TVar t1, TArrow (TVar t2, TVar t3)))) ) ))
    ~printer:typ_to_string ~cmp:types_eq

let test_flipped_rec _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a x y = a y x ;;"))
    (PolyType
       ( t1,
         PolyType (t2, MonoType (TArrow (TVar t1, TArrow (TVar t1, TVar t2))))
       ))
    ~printer:typ_to_string ~cmp:types_eq

let test_flipped_rec_fun _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a = fun x y => a y x ;;"))
    (PolyType
       ( t1,
         PolyType (t2, MonoType (TArrow (TVar t1, TArrow (TVar t1, TVar t2))))
       ))
    ~printer:typ_to_string ~cmp:types_eq

let test_shadow _ =
  assert_equal
    (get_type "a" (typecheck_code "let x = true ;; let a = let x = 1 in x ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_shadow_param _ =
  assert_equal
    (get_type "a" (typecheck_code "let x = true ;; let a (x : int) = x ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_shadow_ty _ =
  assert_equal
    (get_type "a" (typecheck_code "type t = | T ;; let a = let t = 1 in t ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_shadow_overwrite _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = true ;; let a = 0 ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

(* TODO: Better way to do this? *)
let test_shadow_rec _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let rec a x = 1 + (a (x - 1)) ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_shadow_fun _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let a = fun (x : int) => x ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_shadow_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "let x = true ;; let a (y : int) = match y with | x => x ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

(* TODO: A few more shadowing checks (in match, recursive inner functions) *)

let test_scope_limit _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let f (x : int) = x ;; let a = x ;;"))
    (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq

let test_scope_lim_inner _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let a = let f x = x in x ;;"))
    (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq

let test_scope_lim_fun _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let f = fun x => x + 1 ;; let a = x ;;"))
    (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq

let test_scope_lim_if _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "let x = true ;; let a b = if true then let x = 1 in b else x ;;"))
    (MonoType (TArrow (TBool, TBool)))
    ~printer:typ_to_string ~cmp:types_eq

let test_let_in _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = let x : int = 1 in x ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_let_in_untyped _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = let x = 1 in x ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_let_in_generic _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = let y = x in y ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TVar t1))))
    ~printer:typ_to_string ~cmp:types_eq

let test_let_in_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = let f (x : int) = 1 in f ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_let_in_mixed _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = let f y = x = y in f ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TArrow (TVar t1, TBool)))))
    ~printer:typ_to_string ~cmp:types_eq

let test_simple_cond _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = if true then 1 else 2 ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_infer_cond_bool _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = if x then 1 else 2 ;;"))
    (MonoType (TArrow (TBool, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_nested_cond_bool _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let a x = if if true then x else false then 1 else 2 ;;"))
    (MonoType (TArrow (TBool, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_cond_infer_same _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x y = if true then x else y ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TArrow (TVar t1, TVar t1)))))
    ~printer:typ_to_string ~cmp:types_eq

let test_cond_infer_val _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = if true then x else 1 ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_cond_infer_via_bool _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x y = if x then x else y ;;"))
    (MonoType (TArrow (TBool, TArrow (TBool, TBool))))
    ~printer:typ_to_string ~cmp:types_eq

let test_simple_fun _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun x => x + 1 ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_lambda_id _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a = fun x => x ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TVar t1))))
    ~printer:typ_to_string ~cmp:types_eq

let test_explicit_fun _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun (x : int) : int => 0 ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_fun_infer_ret _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun (x : int) => x ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_fun_infer_arg _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun x : int => x ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_fun_two_arg _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let a = fun (x : int) (y : int) : int => 0 ;;"))
    (MonoType (TArrow (TInt, TArrow (TInt, TInt))))
    ~printer:typ_to_string ~cmp:types_eq

let test_simple_funcall _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = string_of_int 1 ;;"))
    (MonoType TString) ~printer:typ_to_string ~cmp:types_eq

let test_funcall_value _ =
  assert_equal
    (get_type "a" (typecheck_code "let f x = x + 1 ;; let a = f 4 ;;"))
    (MonoType TInt) ~printer:typ_to_string ~cmp:types_eq

let test_funcall_infer _ =
  assert_equal
    (get_type "a" (typecheck_code "let f x = x ;; let a = f true ;;"))
    (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq

let test_simple_tuple _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = (1, 2) ;;"))
    (MonoType (TProduct [ TInt; TInt ]))
    ~printer:typ_to_string ~cmp:types_eq

let test_multitype_tuple _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = (1, true) ;;"))
    (MonoType (TProduct [ TInt; TBool ]))
    ~printer:typ_to_string ~cmp:types_eq

let test_long_tuple _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = (1, true, \"a\", ()) ;;"))
    (MonoType (TProduct [ TInt; TBool; TString; TUnit ]))
    ~printer:typ_to_string ~cmp:types_eq

let test_poly_tuple _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let f x = x ;; let a = (f, 4) ;;"))
    (PolyType (t1, MonoType (TProduct [ TArrow (TVar t1, TVar t1); TInt ])))
    ~printer:typ_to_string ~cmp:types_eq

let test_mult_poly_tuple _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let f x = x ;; let a = (f, f) ;;"))
    (PolyType
       ( t1,
         PolyType
           ( t2,
             MonoType
               (TProduct
                  [ TArrow (TVar t1, TVar t1); TArrow (TVar t2, TVar t2) ]) ) ))
    ~printer:typ_to_string ~cmp:types_eq

let test_simple_match _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = match 1 with | x => true ;;"))
    (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq

let test_two_arm_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let a = match 1 with | x => true | y => false ;;"))
    (MonoType TBool) ~printer:typ_to_string ~cmp:types_eq

let test_enum_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar ;;
           let a (x : t) = match x with | Foo => true | Bar => false ;;"))
    (MonoType (TArrow (TId "t", TBool)))
    ~printer:typ_to_string ~cmp:types_eq

let test_enum_match_infer _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar ;;
           let a x = match x with | Foo => true | Bar => false ;;"))
    (MonoType (TArrow (TId "t", TBool)))
    ~printer:typ_to_string ~cmp:types_eq

let test_val_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int | Bar of bool ;;
           let a (x : t) = match x with | Foo y => true | Bar z => z ;;"))
    (MonoType (TArrow (TId "t", TBool)))
    ~printer:typ_to_string ~cmp:types_eq

let test_val_match_infer _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int | Bar of bool ;;
           let a x = match x with | Foo y => true | Bar z => z ;;"))
    (MonoType (TArrow (TId "t", TBool)))
    ~printer:typ_to_string ~cmp:types_eq

let test_tup_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int * int | Bar of bool * int ;;
           let a (x : t) = match x with | Foo (v, w) => v | Bar (y, z) => z ;;"))
    (MonoType (TArrow (TId "t", TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_tup_match_infer _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int * int | Bar of bool * int ;;
           let a x = match x with | Foo (x, y) => x | Bar (z, w) => w ;;"))
    (MonoType (TArrow (TId "t", TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_mixed_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar of int | Baz of bool * int ;;
           let a (x : t) = match x with | Foo => 0 | Bar y => y | Baz (z, w) => w ;;"))
    (MonoType (TArrow (TId "t", TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_mixed_match_infer _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar of int | Baz of bool * int ;;
           let a x = match x with | Foo => 0 | Bar y => y | Baz (z, w) => w ;;"))
    (MonoType (TArrow (TId "t", TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_variadic_match _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = match x with | y => y ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TVar t1))))
    ~printer:typ_to_string ~cmp:types_eq

let test_match_infer_arm _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar ;; let a x y = match x with | Foo => y | Bar => 0 ;;"))
    (MonoType (TArrow (TId "t", TArrow (TInt, TInt))))
    ~printer:typ_to_string ~cmp:types_eq

let test_match_infer_many_arm _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar | Baz ;;
           let a x y z = match x with | Foo => y | Bar => 0 | Baz => z ;;"))
    (MonoType (TArrow (TId "t", TArrow (TInt, TArrow (TInt, TInt)))))
    ~printer:typ_to_string ~cmp:types_eq

let test_match_infer_vars _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar ;; let a x y = match x with | Foo => y | z => z ;;"))
    (MonoType (TArrow (TId "t", TArrow (TId "t", TId "t"))))
    ~printer:typ_to_string ~cmp:types_eq

let test_match_infer_val _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = match x with | y => y + 1 ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

(* TODO: There are definitely more things to test here *)

let test_curry _ =
  assert_equal
    (get_type "a" (typecheck_code "let f x y = x + y ;; let a = f 1 ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_generic_curry _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let f x y = 0 ;; let a = f 1 ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TInt))))
    ~printer:typ_to_string ~cmp:types_eq

let test_curry_infer _ =
  assert_equal
    (get_type "a" (typecheck_code "let f x y = x = y ;; let a = f 1 ;;"))
    (MonoType (TArrow (TInt, TBool)))
    ~printer:typ_to_string ~cmp:types_eq

let test_curry_ret _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let f x y : int = 0 ;; let a = f 1 ;;"))
    (PolyType (t1, MonoType (TArrow (TVar t1, TInt))))
    ~printer:typ_to_string ~cmp:types_eq

let test_higher_order _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a f = f 0 ;;"))
    (PolyType (t1, MonoType (TArrow (TArrow (TInt, TVar t1), TVar t1))))
    ~printer:typ_to_string ~cmp:types_eq

let test_higher_order_ret _ =
  assert_equal
    (get_type "a" (typecheck_code "let a f : bool = f 0 ;;"))
    (MonoType (TArrow (TArrow (TInt, TBool), TBool)))
    ~printer:typ_to_string ~cmp:types_eq

let test_higher_order_gen _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a f x = f x ;;"))
    (PolyType
       ( t1,
         PolyType
           ( t2,
             MonoType
               (TArrow (TArrow (TVar t1, TVar t2), TArrow (TVar t1, TVar t2)))
           ) ))
    ~printer:typ_to_string ~cmp:types_eq

let test_enum_variant _ =
  assert_equal
    (get_type "a" (typecheck_code "type t = | Foo ;; let a = Foo ;;"))
    (MonoType (TId "t")) ~printer:typ_to_string ~cmp:types_eq

let test_val_variant _ =
  assert_equal
    (get_type "a" (typecheck_code "type t = | Foo of int ;; let a = Foo 1 ;;"))
    (MonoType (TId "t")) ~printer:typ_to_string ~cmp:types_eq

let test_tuple_variant _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int * bool ;; let a = Foo (1, false) ;;"))
    (MonoType (TId "t")) ~printer:typ_to_string ~cmp:types_eq

let test_fun_is_monotype _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a"
       (typecheck_code "let a = (fun f x y => (f x, f y)) (fun x => x) ;;"))
    (PolyType
       ( t1,
         MonoType
           (TArrow (TVar t1, TArrow (TVar t1, TProduct [ TVar t1; TVar t1 ])))
       ))
    ~printer:typ_to_string ~cmp:types_eq

let test_let_is_polytype _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a"
       (typecheck_code "let a = let f x = x in (fun x y => (f x, f y)) ;;"))
    (PolyType
       ( t1,
         PolyType
           ( t2,
             MonoType
               (TArrow (TVar t1, TArrow (TVar t2, TProduct [ TVar t1; TVar t2 ])))
           ) ))
    ~printer:typ_to_string ~cmp:types_eq

let test_fibonacci _ =
  assert_equal
    (get_type "fib"
       (typecheck_code
          "let rec fib n = if n = 0 || n = 1 then 1 else fib (n - 1) + fib (n - 2) ;;"))
    (MonoType (TArrow (TInt, TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let test_list_len _ =
  assert_equal
    (get_type "len"
       (typecheck_code
          "type list = | Nil | Val of int * list ;;
           let rec len x = match x with | Nil => 0 | Val (_, r) => 1 + len r ;;"))
    (MonoType (TArrow (TId "list", TInt)))
    ~printer:typ_to_string ~cmp:types_eq

let typecheck_tests =
  "test suite for type checker "
  >::: [
         (* Type equality function *)
         "compare terminal types" >:: test_type_cmp_simple;
         "terminal types not equal" >:: test_type_ne_simple;
         "compare tid types" >:: test_type_cmp_tid;
         "compare simple polytypes" >:: test_type_cmp_one_poly;
         "compare polytypes with renaming" >:: test_type_cmp_rename;
         "compare swapped polytypes" >:: test_type_cmp_swap;
         "compare nastily-renamed polytypes" >:: test_type_cmp_rename_shadow;
         "swapped and renamed polytypes" >:: test_type_cmp_rename_swap;
         (* Simple lets *)
         "let with unit" >:: test_typecheck_simple;
         "let with number" >:: test_typecheck_number;
         "let with bool" >:: test_typecheck_bool;
         "let with string" >:: test_typecheck_string;
         "simple type inference" >:: test_simple_infer;
         "function type inference" >:: test_simple_func;
         "simple lambda inference" >:: test_simple_lambda;
         "inference from argument" >:: test_arg_infer;
         "function calls" >:: test_funcall;
         "function with multiple args" >:: test_multiarg_func;
         (* Arithmetic functions *)
         "int-to-int binary operations" >:: test_int_binops;
         "int binop functions" >:: test_int_binop_fns;
         "comparison binary operations" >:: test_cmp_binops;
         "comparison binop functions" >:: test_lt_fn;
         "equals as a function" >:: test_eq_fn;
         "string concatenation" >:: test_str_concat;
         "concatenation as a function" >:: test_str_concat_fn;
         "logical binary operations" >:: test_logical_binops;
         "logical binop functions" >:: test_logical_binop_fns;
         "logical not" >:: test_lognot;
         "lognot as a function" >:: test_lognot_fn;
         "bitwise not" >:: test_bitnot;
         "bitwise not as a function" >:: test_bitnot_fn;
         (* Builtin functions *)
         "type of int_of_string" >:: test_intstr;
         "type of string_of_int" >:: test_strint;
         "type of print_string" >:: test_print;
         (* Generic functions *)
         "identity function" >:: test_id_fn;
         "constant-valued function" >:: test_const_fn;
         "multi-argument generic function" >:: test_multi_gens;
         "mixed generic and non-generics" >:: test_mixed_generic;
         (* Recursive function defs (e.g. let rec a b = a b) *)
         "recursive def" >:: test_recursion;
         "recursive def using fun" >:: test_recurse_fun;
         "multi-arg recursive def" >:: test_multiarg_rec;
         "multi-arg recursive def with fun" >:: test_multiarg_rec_fun;
         "recursion by flipping args" >:: test_flipped_rec;
         "recursion by flipping args and fun" >:: test_flipped_rec_fun;
         (* Variable name shadowing *)
         "simple variable shadow" >:: test_shadow;
         "variable shadowed by param" >:: test_shadow_param;
         "variable with same name as type" >:: test_shadow_ty;
         "overwriting variable" >:: test_shadow_overwrite;
         "shadowing with recursive func" >:: test_shadow_rec;
         "shadowing with lambda" >:: test_shadow_fun;
         "shadowing with simple match" >:: test_shadow_match;
         (* Limited scope of variables *)
         "limited scope of param" >:: test_scope_limit;
         "scope limit in let-in" >:: test_scope_lim_inner;
         "scope limit in fun" >:: test_scope_lim_fun;
         "scope limit across if" >:: test_scope_lim_if;
         (* Let-in statements *)
         "simple let-in" >:: test_let_in;
         "untyped let-in" >:: test_let_in_untyped;
         "generic let-in" >:: test_let_in_generic;
         "let-in with arg" >:: test_let_in_fn;
         "mixed let-in" >:: test_let_in_mixed;
         (* Conditional statements *)
         "simple cond" >:: test_simple_cond;
         "infer boolean param" >:: test_infer_cond_bool;
         "nested boolean param" >:: test_nested_cond_bool;
         "infer same type across cond" >:: test_cond_infer_same;
         "infer type across cond" >:: test_cond_infer_val;
         "infer boolean then cond value" >:: test_cond_infer_via_bool;
         (* TODO: Lambda exprs *)
         "simple lambda" >:: test_simple_fun;
         "lambda id function" >:: test_lambda_id;
         "explicitly-typed fun" >:: test_explicit_fun;
         "infer fun ret from argument" >:: test_fun_infer_ret;
         "infer fun arg from argument" >:: test_fun_infer_arg;
         "multi-arg function" >:: test_fun_two_arg;
         (* TODO: Function calls *)
         "simple function call" >:: test_simple_funcall;
         "function call of custom fn" >:: test_funcall_value;
         "function call of variadic fn" >:: test_funcall_infer;
         (* Tuples *)
         "simple tuple" >:: test_simple_tuple;
         "tuple with differing types" >:: test_multitype_tuple;
         "long tuple" >:: test_long_tuple;
         "tuple containing polytype" >:: test_poly_tuple;
         "tuple with same polytype twice" >:: test_mult_poly_tuple;
         (* TODO: Match statements *)
         "simple match" >:: test_simple_match;
         "match with two arms" >:: test_two_arm_match;
         "match on enum type" >:: test_enum_match;
         "match on enum type w/inference" >:: test_enum_match_infer;
         "match on value type" >:: test_val_match;
         "match on value type w/inference" >:: test_val_match_infer;
         "match on tuple type" >:: test_tup_match;
         "match on tuple type w/inference" >:: test_tup_match_infer;
         "match on mixed type" >:: test_mixed_match;
         "match on mixed type w/inference" >:: test_mixed_match_infer;
         "match with no type clues" >:: test_variadic_match;
         "inference across match arms" >:: test_match_infer_arm;
         "inference across many arms" >:: test_match_infer_many_arm;
         "inference with match var" >:: test_match_infer_vars;
         "inference of matched value" >:: test_match_infer_val;
         (* Function currying *)
         "simple function currying" >:: test_curry;
         "curry with generic val" >:: test_generic_curry;
         "inferred arg through curry" >:: test_curry_infer;
         "inferred return type through curry" >:: test_curry_ret;
         (* Higher-order functions *)
         "simple higher-order function" >:: test_higher_order;
         "higher-order with fixed ret type" >:: test_higher_order_ret;
         "higher-order generic fn" >:: test_higher_order_gen;
         (* Custom types *)
         "enum-variant type" >:: test_enum_variant;
         "value-variant type" >:: test_val_variant;
         "tuple-variant type" >:: test_tuple_variant;
         (* TODO: Cursed/unintuitive expressions *)
         "fun is monotype" >:: test_fun_is_monotype;
         "let is polytype" >:: test_let_is_polytype;
         (* TODO: Real-world examples *)
         "fibonacci sequence" >:: test_fibonacci;
         "len of list" >:: test_list_len;
       ]
