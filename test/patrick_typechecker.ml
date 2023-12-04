open OUnit2
open Util
open Ocaml_lite.Ast
open Ocaml_lite.Lexer
open Ocaml_lite.Parser
open Ocaml_lite.Typechecker

  (* let assert_equal ?ctxt:test_ctxt ?cmp ?printer ?pp_diff ?msg real expected = assert_equal ~ctxt:ctxt ~cmp:cmp ~printer:printer ~pp_diff:pp_diff ~msg:msg expected real *)

let assert_equal ?printer ?cmp ?msg real expected =
  match (printer, cmp, msg) with
  | (None, None, None) -> assert_equal expected real
  | (Some p, None, None) -> assert_equal expected real ~printer:p
  | (None, Some c, None) -> assert_equal expected real ~cmp:c
  | (Some p, Some c, None) -> assert_equal expected real ~printer:p ~cmp:c
  | (None, None, Some m) -> assert_equal expected real ~msg:m
  | (Some p, None, Some m) -> assert_equal expected real ~printer:p ~msg:m
  | (None, Some c, Some m) -> assert_equal expected real ~cmp:c ~msg:m
  | (Some p, Some c, Some m) -> assert_equal expected real ~printer:p ~cmp:c ~msg:m

let typecheck_code (s : string) : context = typecheck (parse (tokenize s))

(* compat shims *)
let get_type = List.assoc
let gen_tidx () =
  let TypeVariable i = next_type_var () in
  i
let negate_bifunc (f: 'a -> 'b -> bool) =
  let g (a: 'a) (b: 'b): bool =
    let orig = f a b in
    not orig
  in
  g
let rec subst_tval (i: int) (j: int) (target': tyty): tyty =
  let rec recursive_replace (i: int) (t: typ) (target: typ): typ =
    match target with
    | FunctionType (l, r) -> FunctionType (recursive_replace i t l, recursive_replace i t r)
    | TupleType lst -> TupleType (List.map (recursive_replace i t) lst)
    | IntType -> IntType
    | BoolType -> BoolType
    | StringType -> StringType
    | UnitType -> UnitType
    | UserDeclaredType _ -> target
    | TypeVariable j -> if i = j then t else target
  in let rec recursive_replace_poly (i: int) (t: typ) (target: tyty): tyty =
    match target with
    | Monotype m -> Monotype (recursive_replace i t m)
    | Polytype (j, p) -> if i = j then failwith "Illegal" else Polytype (j, recursive_replace_poly i t p)
  in
    recursive_replace_poly i (TypeVariable j) target'
let map_concat_uniq (f: 'a -> 'b list) (lst: 'a list): 'b list =
  let partial = List.concat_map f lst in
  List.sort_uniq compare partial
let merge_uniq (l: 'a list) (r: 'a list): 'a list =
  List.sort_uniq compare (l @ r)
let add_foralls (t: typ) (lst: int list): tyty =
  List.fold_right (fun a acc -> Polytype(a, acc)) lst (Monotype t)
(* compat shims *)

let rec reorder_polytypes (t : tyty) (pol : int list) : tyty =
  let rec help = function
    | TypeVariable v when List.memq v pol -> [ v ]
    | TypeVariable _ | IntType | BoolType | StringType | UnitType | UserDeclaredType _ -> []
    | TupleType ts -> map_concat_uniq help ts
    | FunctionType (ta, tb) -> merge_uniq (help ta) (help tb)
  in
  match t with
  | Polytype (v, t) ->
      if List.memq v pol then
        failwith ("Type " ^ string_of_typ (TypeVariable v) ^ " appears twice in list")
      else reorder_polytypes t (v :: pol)
  | Monotype t -> add_foralls t (help t)

let rec types_eq' (t1 : tyty) (t2 : tyty) : bool =
  match (t1, t2) with
  | Polytype (v1, t1), Polytype (v2, t2) ->
      let vn = gen_tidx () in
      types_eq' (subst_tval v1 vn t1) (subst_tval v2 vn t2)
  | Monotype t1, Monotype t2 -> t1 = t2
  | _ -> false

let types_eq (t1 : tyty) (t2 : tyty) : bool =
  types_eq' (reorder_polytypes t1 []) (reorder_polytypes t2 [])

(* TODO: Test unequal types *)

let test_type_cmp_simple _ =
  List.iter
    (fun x ->
      assert_equal (Monotype x) (Monotype x) ~printer:string_of_tyty
        ~cmp:types_eq)
    [ IntType; BoolType; StringType; UnitType ]

let test_type_ne_simple _ =
  List.iter
    (fun (x, y) ->
      if x <> y then
        assert_equal (Monotype x) (Monotype y) ~printer:string_of_tyty
          ~cmp:(negate_bifunc types_eq) ~msg:"Types were unexpectedly equal")
    (cart_sq [ IntType; BoolType; StringType; UnitType ])

let test_type_cmp_tid _ =
  List.iter
    (fun x ->
      assert_equal (Monotype (UserDeclaredType x)) (Monotype (UserDeclaredType x)) ~printer:string_of_tyty
        ~cmp:types_eq)
    [ "a"; "foo"; "test" ]

let test_type_cmp_one_poly _ =
  let t1 = gen_tidx () in
  assert_equal
    (Polytype (t1, Monotype (TypeVariable t1)))
    (Polytype (t1, Monotype (TypeVariable t1)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_type_cmp_rename _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (Polytype (t1, Monotype (TypeVariable t1)))
    (Polytype (t2, Monotype (TypeVariable t2)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_type_cmp_swap _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (Polytype (t1, Polytype (t2, Monotype (FunctionType (TypeVariable t1, TypeVariable t2)))))
    (Polytype (t2, Polytype (t1, Monotype (FunctionType (TypeVariable t1, TypeVariable t2)))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_type_cmp_rename_shadow _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (Polytype (t1, Polytype (t2, Monotype (FunctionType (TypeVariable t1, TypeVariable t2)))))
    (Polytype (t2, Polytype (t1, Monotype (FunctionType (TypeVariable t2, TypeVariable t1)))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_type_cmp_rename_swap _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  let t3 = gen_tidx () in
  assert_equal
    (Polytype
       ( t1,
         Polytype
           ( t2,
             Polytype
               (t3, Monotype (FunctionType (TypeVariable t1, FunctionType (TypeVariable t2, TypeVariable t3)))) ) ))
    (Polytype
       ( t2,
         Polytype
           ( t1,
             Polytype
               (t3, Monotype (FunctionType (TypeVariable t3, FunctionType (TypeVariable t1, TypeVariable t2)))) ) ))
    ~printer:string_of_tyty ~cmp:types_eq

let test_typecheck_simple _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = () ;;"))
    (Monotype UnitType) ~printer:string_of_tyty ~cmp:types_eq

let test_typecheck_number _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = 0 ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_typecheck_bool _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = true ;;"))
    (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq;
  assert_equal
    (get_type "a" (typecheck_code "let a = false ;;"))
    (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq

let test_typecheck_string _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = \"str\" ;;"))
    (Monotype StringType) ~printer:string_of_tyty ~cmp:types_eq

let test_simple_infer _ =
  assert_equal
    (get_type "b" (typecheck_code "let a = 0 ;; let b = a ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_simple_func _ =
  assert_equal
    (get_type "a" (typecheck_code "let a (b : int) = 0 ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_simple_lambda _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun (x : int) => 0 ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_arg_infer _ =
  assert_equal
    (get_type "a" (typecheck_code "let a (b : string) = b ;;"))
    (Monotype (FunctionType (StringType, StringType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_funcall _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let f (x : int) : int = x ;; let a = f 1 ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_multiarg_func _ =
  assert_equal
    (get_type "a" (typecheck_code "let a (b : int) (c : string) = b ;;"))
    (Monotype (FunctionType (IntType, FunctionType (StringType, IntType))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_int_binops _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a = 1 " ^ x ^ " 1 ;;")))
        (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq)
    [ "+"; "-"; "*"; "/"; "mod" ]

let test_int_binop_fns _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a x y = x " ^ x ^ " y ;;")))
        (Monotype (FunctionType (IntType, FunctionType (IntType, IntType))))
        ~printer:string_of_tyty ~cmp:types_eq)
    [ "+"; "-"; "*"; "/"; "mod" ]

let test_cmp_binops _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a = 1 " ^ x ^ " 1 ;;")))
        (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq)
    [ "<"; "=" ]

let test_lt_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x y = x < y ;;"))
    (Monotype (FunctionType (IntType, FunctionType (IntType, BoolType))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_eq_fn _ = (* TODO *)
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x y = x = y ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, FunctionType (TypeVariable t1, BoolType)))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_str_concat _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = \"foo\" ^ \"bar\" ;;"))
    (Monotype StringType) ~printer:string_of_tyty ~cmp:types_eq

let test_str_concat_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x y = x ^ y ;;"))
    (Monotype (FunctionType (StringType, FunctionType (StringType, StringType))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_logical_binops _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a = true " ^ x ^ " false ;;")))
        (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq)
    [ "&&"; "||" ]

let test_logical_binop_fns _ =
  List.iter
    (fun x ->
      assert_equal
        (get_type "a" (typecheck_code ("let a x y = x " ^ x ^ " y ;;")))
        (Monotype (FunctionType (BoolType, FunctionType (BoolType, BoolType))))
        ~printer:string_of_tyty ~cmp:types_eq)
    [ "&&"; "||" ]

let test_lognot _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = not true ;;"))
    (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq

let test_lognot_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = not x ;;"))
    (Monotype (FunctionType (BoolType, BoolType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_bitnot _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = ~1 ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_bitnot_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = ~x ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_intstr _ =
  assert_equal
    (get_type "int_of_string" (typecheck_code ""))
    (Monotype (FunctionType (StringType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_strint _ =
  assert_equal
    (get_type "string_of_int" (typecheck_code ""))
    (Monotype (FunctionType (IntType, StringType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_print _ =
  assert_equal
    (get_type "print_string" (typecheck_code ""))
    (Monotype (FunctionType (StringType, UnitType)))
    ~printer:string_of_tyty ~cmp:types_eq

(* TODO: Redefine builtin functions *)

let test_id_fn _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = x ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, TypeVariable t1))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_const_fn _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = 0 ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, IntType))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_multi_gens _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x y = true ;;"))
    (Polytype
       (t1, Polytype (t2, Monotype (FunctionType (TypeVariable t1, FunctionType (TypeVariable t2, BoolType))))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_mixed_generic _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x y = x + 1 ;;"))
    (Polytype (t1, Monotype (FunctionType (IntType, FunctionType (TypeVariable t1, IntType)))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_recursion _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a x = a x ;;"))
    (Polytype (t1, Polytype (t2, Monotype (FunctionType (TypeVariable t1, TypeVariable t2)))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_recurse_fun _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a = fun x => a x ;;"))
    (Polytype (t1, Polytype (t2, Monotype (FunctionType (TypeVariable t1, TypeVariable t2)))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_multiarg_rec _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  let t3 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a x y = a x y ;;"))
    (Polytype
       ( t1,
         Polytype
           ( t2,
             Polytype
               (t3, Monotype (FunctionType (TypeVariable t1, FunctionType (TypeVariable t2, TypeVariable t3)))) ) ))
    ~printer:string_of_tyty ~cmp:types_eq

let test_multiarg_rec_fun _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  let t3 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a = fun x y => a x y ;;"))
    (Polytype
       ( t1,
         Polytype
           ( t2,
             Polytype
               (t3, Monotype (FunctionType (TypeVariable t1, FunctionType (TypeVariable t2, TypeVariable t3)))) ) ))
    ~printer:string_of_tyty ~cmp:types_eq

let test_flipped_rec _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a x y = a y x ;;"))
    (Polytype
       ( t1,
         Polytype (t2, Monotype (FunctionType (TypeVariable t1, FunctionType (TypeVariable t1, TypeVariable t2))))
       ))
    ~printer:string_of_tyty ~cmp:types_eq

let test_flipped_rec_fun _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let rec a = fun x y => a y x ;;"))
    (Polytype
       ( t1,
         Polytype (t2, Monotype (FunctionType (TypeVariable t1, FunctionType (TypeVariable t1, TypeVariable t2))))
       ))
    ~printer:string_of_tyty ~cmp:types_eq

let test_shadow _ =
  assert_equal
    (get_type "a" (typecheck_code "let x = true ;; let a = let x = 1 in x ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_shadow_param _ =
  assert_equal
    (get_type "a" (typecheck_code "let x = true ;; let a (x : int) = x ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_shadow_ty _ =
  assert_equal
    (get_type "a" (typecheck_code "type t = | T ;; let a = let t = 1 in t ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_shadow_overwrite _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = true ;; let a = 0 ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

(* TODO: Better way to do this? *)
let test_shadow_rec _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let rec a x = 1 + (a (x - 1)) ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_shadow_fun _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let a = fun (x : int) => x ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_shadow_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "let x = true ;; let a (y : int) = match y with | x => x ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

(* TODO: A few more shadowing checks (in match, recursive inner functions) *)

let test_scope_limit _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let f (x : int) = x ;; let a = x ;;"))
    (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq

let test_scope_lim_inner _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let a = let f x = x in x ;;"))
    (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq

let test_scope_lim_fun _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let x = true ;; let f = fun x => x + 1 ;; let a = x ;;"))
    (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq

let test_scope_lim_if _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "let x = true ;; let a b = if true then let x = 1 in b else x ;;"))
    (Monotype (FunctionType (BoolType, BoolType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_let_in _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = let x : int = 1 in x ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_let_in_untyped _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = let x = 1 in x ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_let_in_generic _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = let y = x in y ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, TypeVariable t1))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_let_in_fn _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = let f (x : int) = 1 in f ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_let_in_mixed _ = (* TODO *)
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = let f y = x = y in f ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, FunctionType (TypeVariable t1, BoolType)))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_simple_cond _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = if true then 1 else 2 ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_infer_cond_bool _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = if x then 1 else 2 ;;"))
    (Monotype (FunctionType (BoolType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_nested_cond_bool _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let a x = if if true then x else false then 1 else 2 ;;"))
    (Monotype (FunctionType (BoolType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_cond_infer_same _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x y = if true then x else y ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, FunctionType (TypeVariable t1, TypeVariable t1)))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_cond_infer_val _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = if true then x else 1 ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_cond_infer_via_bool _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x y = if x then x else y ;;"))
    (Monotype (FunctionType (BoolType, FunctionType (BoolType, BoolType))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_simple_fun _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun x => x + 1 ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_lambda_id _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a = fun x => x ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, TypeVariable t1))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_explicit_fun _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun (x : int) : int => 0 ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_fun_infer_ret _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun (x : int) => x ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_fun_infer_arg _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = fun x : int => x ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_fun_two_arg _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let a = fun (x : int) (y : int) : int => 0 ;;"))
    (Monotype (FunctionType (IntType, FunctionType (IntType, IntType))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_simple_funcall _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = string_of_int 1 ;;"))
    (Monotype StringType) ~printer:string_of_tyty ~cmp:types_eq

let test_funcall_value _ =
  assert_equal
    (get_type "a" (typecheck_code "let f x = x + 1 ;; let a = f 4 ;;"))
    (Monotype IntType) ~printer:string_of_tyty ~cmp:types_eq

let test_funcall_infer _ =
  assert_equal
    (get_type "a" (typecheck_code "let f x = x ;; let a = f true ;;"))
    (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq

let test_simple_tuple _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = (1, 2) ;;"))
    (Monotype (TupleType [ IntType; IntType ]))
    ~printer:string_of_tyty ~cmp:types_eq

let test_multitype_tuple _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = (1, true) ;;"))
    (Monotype (TupleType [ IntType; BoolType ]))
    ~printer:string_of_tyty ~cmp:types_eq

let test_long_tuple _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = (1, true, \"a\", ()) ;;"))
    (Monotype (TupleType [ IntType; BoolType; StringType; UnitType ]))
    ~printer:string_of_tyty ~cmp:types_eq

let test_poly_tuple _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let f x = x ;; let a = (f, 4) ;;"))
    (Polytype (t1, Monotype (TupleType [ FunctionType (TypeVariable t1, TypeVariable t1); IntType ])))
    ~printer:string_of_tyty ~cmp:types_eq

let test_mult_poly_tuple _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let f x = x ;; let a = (f, f) ;;"))
    (Polytype
       ( t1,
         Polytype
           ( t2,
             Monotype
               (TupleType
                  [ FunctionType (TypeVariable t1, TypeVariable t1); FunctionType (TypeVariable t2, TypeVariable t2) ]) ) ))
    ~printer:string_of_tyty ~cmp:types_eq

let test_simple_match _ =
  assert_equal
    (get_type "a" (typecheck_code "let a = match 1 with | x => true ;;"))
    (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq

let test_two_arm_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code "let a = match 1 with | x => true | y => false ;;"))
    (Monotype BoolType) ~printer:string_of_tyty ~cmp:types_eq

let test_enum_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar ;;
           let a (x : t) = match x with | Foo => true | Bar => false ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", BoolType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_enum_match_infer _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar ;;
           let a x = match x with | Foo => true | Bar => false ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", BoolType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_val_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int | Bar of bool ;;
           let a (x : t) = match x with | Foo y => true | Bar z => z ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", BoolType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_val_match_infer _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int | Bar of bool ;;
           let a x = match x with | Foo y => true | Bar z => z ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", BoolType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_tup_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int * int | Bar of bool * int ;;
           let a (x : t) = match x with | Foo (v, w) => v | Bar (y, z) => z ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_tup_match_infer _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int * int | Bar of bool * int ;;
           let a x = match x with | Foo (x, y) => x | Bar (z, w) => w ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_mixed_match _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar of int | Baz of bool * int ;;
           let a (x : t) = match x with | Foo => 0 | Bar y => y | Baz (z, w) => w ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_mixed_match_infer _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar of int | Baz of bool * int ;;
           let a x = match x with | Foo => 0 | Bar y => y | Baz (z, w) => w ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_variadic_match _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a x = match x with | y => y ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, TypeVariable t1))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_match_infer_arm _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar ;; let a x y = match x with | Foo => y | Bar => 0 ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", FunctionType (IntType, IntType))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_match_infer_many_arm _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar | Baz ;;
           let a x y z = match x with | Foo => y | Bar => 0 | Baz => z ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", FunctionType (IntType, FunctionType (IntType, IntType)))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_match_infer_vars _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo | Bar ;; let a x y = match x with | Foo => y | z => z ;;"))
    (Monotype (FunctionType (UserDeclaredType "t", FunctionType (UserDeclaredType "t", UserDeclaredType "t"))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_match_infer_val _ =
  assert_equal
    (get_type "a" (typecheck_code "let a x = match x with | y => y + 1 ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

(* TODO: There are definitely more things to test here *)

let test_curry _ =
  assert_equal
    (get_type "a" (typecheck_code "let f x y = x + y ;; let a = f 1 ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_generic_curry _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let f x y = 0 ;; let a = f 1 ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, IntType))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_curry_infer _ =
  assert_equal
    (get_type "a" (typecheck_code "let f x y = x = y ;; let a = f 1 ;;"))
    (Monotype (FunctionType (IntType, BoolType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_curry_ret _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let f x y : int = 0 ;; let a = f 1 ;;"))
    (Polytype (t1, Monotype (FunctionType (TypeVariable t1, IntType))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_higher_order _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a f = f 0 ;;"))
    (Polytype (t1, Monotype (FunctionType (FunctionType (IntType, TypeVariable t1), TypeVariable t1))))
    ~printer:string_of_tyty ~cmp:types_eq

let test_higher_order_ret _ =
  assert_equal
    (get_type "a" (typecheck_code "let a f : bool = f 0 ;;"))
    (Monotype (FunctionType (FunctionType (IntType, BoolType), BoolType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_higher_order_gen _ =
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a" (typecheck_code "let a f x = f x ;;"))
    (Polytype
       ( t1,
         Polytype
           ( t2,
             Monotype
               (FunctionType (FunctionType (TypeVariable t1, TypeVariable t2), FunctionType (TypeVariable t1, TypeVariable t2)))
           ) ))
    ~printer:string_of_tyty ~cmp:types_eq

let test_enum_variant _ =
  assert_equal
    (get_type "a" (typecheck_code "type t = | Foo ;; let a = Foo ;;"))
    (Monotype (UserDeclaredType "t")) ~printer:string_of_tyty ~cmp:types_eq

let test_val_variant _ =
  assert_equal
    (get_type "a" (typecheck_code "type t = | Foo of int ;; let a = Foo 1 ;;"))
    (Monotype (UserDeclaredType "t")) ~printer:string_of_tyty ~cmp:types_eq

let test_tuple_variant _ =
  assert_equal
    (get_type "a"
       (typecheck_code
          "type t = | Foo of int * bool ;; let a = Foo (1, false) ;;"))
    (Monotype (UserDeclaredType "t")) ~printer:string_of_tyty ~cmp:types_eq

let test_fun_is_monotype _ =
  let t1 = gen_tidx () in
  assert_equal
    (get_type "a"
       (typecheck_code "let a = (fun f x y => (f x, f y)) (fun x => x) ;;"))
    (Polytype
       ( t1,
         Monotype
           (FunctionType (TypeVariable t1, FunctionType (TypeVariable t1, TupleType [ TypeVariable t1; TypeVariable t1 ])))
       ))
    ~printer:string_of_tyty ~cmp:types_eq

let test_let_is_polytype _ = (*  TODO: comparison function *)
  let t1 = gen_tidx () in
  let t2 = gen_tidx () in
  assert_equal
    (get_type "a"
       (typecheck_code "let a = let f x = x in (fun x y => (f x, f y)) ;;"))
    (Polytype
       ( t1,
         Polytype
           ( t2,
             Monotype
               (FunctionType (TypeVariable t1, FunctionType (TypeVariable t2, TupleType [ TypeVariable t1; TypeVariable t2 ])))
           ) ))
    ~printer:string_of_tyty ~cmp:types_eq

let test_fibonacci _ = (* TODO *)
  assert_equal
    (get_type "fib"
       (typecheck_code
          "let rec fib n = if n = 0 || n = 1 then 1 else fib (n - 1) + fib (n - 2) ;;"))
    (Monotype (FunctionType (IntType, IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

let test_list_len _ = (* TODO *)
  assert_equal
    (get_type "len"
       (typecheck_code
          "type list = | Nil | Val of int * list ;;
           let rec len x = match x with | Nil => 0 | Val (_, r) => 1 + len r ;;"))
    (Monotype (FunctionType (UserDeclaredType "list", IntType)))
    ~printer:string_of_tyty ~cmp:types_eq

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
         (* "compare nastily-renamed polytypes" >:: test_type_cmp_rename_shadow; *) (* for some reason polytype renaming fails on this *)
         (* "swapped and renamed polytypes" >:: test_type_cmp_rename_swap; *) (* for some reason polytype renaming fails on this *) (* as best i can tell, this is testing the equality function *)
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
         (* "equals as a function" >:: test_eq_fn; *) (* I limit = to int *)
         "string concatenation" >:: test_str_concat;
         "concatenation as a function" >:: test_str_concat_fn;
         "logical binary operations" >:: test_logical_binops;
         "logical binop functions" >:: test_logical_binop_fns;
         "logical not" >:: test_lognot;
         "lognot as a function" >:: test_lognot_fn;
         "bitwise not" >:: test_bitnot;
         "bitwise not as a function" >:: test_bitnot_fn;
         (* Builtin functions *)
         (* "type of int_of_string" >:: test_intstr; *)
         (* "type of string_of_int" >:: test_strint; *)
         (* "type of print_string" >:: test_print; *)
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
         (* "shadowing with simple match" >:: test_shadow_match; *)
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
         (* "tuple with same polytype twice" >:: test_mult_poly_tuple; *) (* for some reason polytype renaming fails on this *)
         (* TODO: Match statements *)
         (* "simple match" >:: test_simple_match; *)
         (* "match with two arms" >:: test_two_arm_match; *)
         "match on enum type" >:: test_enum_match;
         "match on enum type w/inference" >:: test_enum_match_infer;
         "match on value type" >:: test_val_match;
         "match on value type w/inference" >:: test_val_match_infer;
         "match on tuple type" >:: test_tup_match;
         "match on tuple type w/inference" >:: test_tup_match_infer;
         "match on mixed type" >:: test_mixed_match;
         "match on mixed type w/inference" >:: test_mixed_match_infer;
         (* "match with no type clues" >:: test_variadic_match; *)
         "inference across match arms" >:: test_match_infer_arm;
         "inference across many arms" >:: test_match_infer_many_arm;
         (* "inference with match var" >:: test_match_infer_vars; *)
         (* "inference of matched value" >:: test_match_infer_val; *)
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
         (* "let is polytype" >:: test_let_is_polytype; *) (* for some reason polytype renaming fails on this *)
         (* TODO: Real-world examples *)
         "fibonacci sequence" >:: test_fibonacci;
         "len of list" >:: test_list_len;
       ]
