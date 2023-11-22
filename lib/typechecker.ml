open Ast

let next_var = ref 0
let next_type_var (_: unit): typ =
    let () = next_var := !next_var + 1 in
    TypeVariable !next_var

type tyty =
  | Monotype of typ
  | Polytype of int * tyty

exception TypecheckError of string

type solved_constraint =
  | Identity
  | NewConstraints of (tyty * tyty) list
  | Mapping of int * typ

  (* wrapper function for converting old-style constraints to new-style constraints *)
let monotonize (l: (typ * typ) list): (tyty * tyty) list =
  List.map
    (fun x -> let (l, r) = x in
      (Monotype l, Monotype r)
    )
    l

type context = (string * tyty) list

let rec typecheck (p: program): context =
  let Program (bds) = p in
  (* let (ctx, constraints) = List.fold_left (fun ((ctx, constraints), acc) -> acc) ([], []) bds in *)
  (* let (ctx, constraints) = List.fold_left (fun acc a -> let (ctx, constraints) = acc in let (ctx', constraints') = typecheck_binding ) ([], []) bds in *)
  let ctx =
    List.fold_left
      typecheck_binding
      ([("string_of_int", FunctionType (IntType, StringType)); ("int_of_string", FunctionType (StringType, IntType)); ("print_string", FunctionType (StringType, UnitType))] |> List.map (fun x -> let (s, t) = x in (s, Monotype t)))
      bds
  in
  (* let _ = print_string (List.map (fun mapping -> let (name, Monotype ty) = mapping in name ^ ": " ^ string_of_typ ty) ctx |> String.concat "\n") in *)
  ctx
and typecheck_binding (ctx: context) (b: binding): context =
  match b with
  | NonRecursiveBinding (name, params, ty, value) ->
      let param_ctx = List.map (fun p -> match p with | UntypedParam x -> (x, Monotype (next_type_var ())) | TypedParam (x, t) -> (x, Monotype t)) params in
        let (value_ty, constraints') = typecheck_expr (param_ctx @ ctx) value in
          let value_type = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, Monotype t) = x in t) param_ctx) value_ty in
            let substitutions = unify_constraints ((match ty with | None -> [] | Some t -> [(Monotype t, Monotype value_ty)]) @ constraints') in
              let substituted = apply_substitutions substitutions value_type in
                let generalized = generalize ctx substituted in
                  (name, generalized) :: ctx
  | RecursiveBinding (name, params, ty, value) ->
      let param_ctx' = List.map (fun p -> match p with | UntypedParam x -> (x, Monotype (next_type_var ())) | TypedParam (x, t) -> (x, Monotype t)) params in
        let param_ctx = (name, Monotype (next_type_var ())) :: param_ctx' in
          let (value_ty, constraints') = typecheck_expr (param_ctx @ ctx) value in
            let value_type = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, Monotype t) = x in t) param_ctx) value_ty in
              let substitutions = unify_constraints ((match ty with | None -> [] | Some t -> [(Monotype t, Monotype value_ty)]) @ constraints') in
                let substituted = apply_substitutions substitutions value_type in
                  let generalized = generalize ctx substituted in
                    (name, generalized) :: ctx
  | TypeDefBinding (name, constructors) ->
      (List.map (fun (c, args) -> match args with | None -> (c, Monotype (UserDeclaredType name)) | Some(t) -> (c, Monotype (FunctionType (t, UserDeclaredType name)))) constructors) @ ctx
and typecheck_expr (ctx: context) (e: expr): (typ * (tyty * tyty) list) =
  match e with
  | LetExpr (name, params, ty, value, body) ->
    (match params with
      (* | [] -> let (value_type, constraints) = typecheck_expr ctx value in *)
      (**)
      | _ ->
        let param_ctx = List.map (fun p -> match p with | UntypedParam x -> (x, Monotype (next_type_var ())) | TypedParam (x, t) -> (x, Monotype t)) params in
          let (value_ty, constraints') = typecheck_expr (param_ctx @ ctx) value in
            let value_type = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, Monotype t) = x in t) param_ctx) value_ty in
              let substitutions = unify_constraints ((match ty with | None -> [] | Some t -> [(Monotype t, Monotype value_ty)]) @ constraints') in
                let substituted = apply_substitutions substitutions value_type in
                  let generalized = generalize ctx substituted in
                    (* let (body_ty, new_constraints) = typecheck_expr ((name, generalized) :: ctx) body in *)
                    typecheck_expr ((name, generalized) :: ctx) body
        (* (UnitType, []) *)
    )
  | LetRecExpr (name, params, ty, value, body) ->
      let param_ctx' = List.map (fun p -> match p with | UntypedParam x -> (x, Monotype (next_type_var ())) | TypedParam (x, t) -> (x, Monotype t)) params in
        let param_ctx = (name, Monotype (next_type_var ())) :: param_ctx' in
          let (value_ty, constraints') = typecheck_expr (param_ctx @ ctx) value in
            let value_type = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, Monotype t) = x in t) param_ctx) value_ty in
              let substitutions = unify_constraints ((match ty with | None -> [] | Some t -> [(Monotype t, Monotype value_ty)]) @ constraints') in
                let substituted = apply_substitutions substitutions value_type in
                  let generalized = generalize ctx substituted in
                    typecheck_expr ((name, generalized) :: ctx) body
  | IfExpr (cond, iftrue, iffalse) ->
    let (cond_ty, c1) = typecheck_expr ctx cond in
      let (iftrue_ty, c2) = typecheck_expr ctx iftrue in
        let (iffalse_ty, c3) = typecheck_expr ctx iffalse in
          (iftrue_ty, ([(iftrue_ty, iffalse_ty); (cond_ty, BoolType)] |> monotonize) @ c1 @ c2 @ c3)
  | FunDefExpr (params, ty, body) -> let param_ctx = List.map (fun p -> match p with | UntypedParam x -> (x, Monotype (next_type_var ())) | TypedParam (x, t) -> (x, Monotype t)) params in
      let (body_ty, constraints') = typecheck_expr (param_ctx @ ctx) body in
        let type' = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, Monotype t) = x in t) param_ctx) body_ty in
          (match ty with
            | None -> (type', constraints')
            | Some t -> (type', (Monotype t, Monotype body_ty) :: constraints'))
  | FunAppExpr (l, r) -> let (l_ty, c1) = typecheck_expr ctx l in let (r_ty, c2) = typecheck_expr ctx r in
    let in' = next_type_var () in let out = next_type_var () in
      (out, ([(l_ty, FunctionType (in', out)); (r_ty, in')] |> monotonize) @ c1 @ c2)
  | TupleExpr (elements) -> let (constraints', types) = List.fold_left_map (fun acc el -> let (t, c) = typecheck_expr ctx el in (c @ acc, t)) [] elements in (TupleType types, constraints')
  | BinopExpr (l, op, r) -> let (l_ty, c1) = typecheck_expr ctx l in let (r_ty, c2) = typecheck_expr ctx r in
    (match op with
      | Plus -> (IntType, ([(l_ty, IntType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2)
      | Minus -> (IntType, ([(l_ty, IntType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2)
      | Times -> (IntType, ([(l_ty, IntType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2)
      | Divide -> (IntType, ([(l_ty, IntType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2)
      | Modulo -> (IntType, ([(l_ty, IntType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2)
      | LessThan -> (BoolType, ([(l_ty, IntType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2)
      | Equal -> (BoolType, ([(l_ty, IntType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2)
      | Concat -> (StringType, ([(l_ty, StringType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2)
      | And -> (BoolType, ([(l_ty, BoolType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2)
      | Or -> (BoolType, ([(l_ty, BoolType); (l_ty, r_ty)] |> monotonize) @ c1 @ c2))
  | UnopExpr (op, arg) -> let (arg_ty, c1) = typecheck_expr ctx arg in
    (match op with
      | NegateInt -> (IntType, (Monotype arg_ty, Monotype IntType) :: c1)
      | InvertBool -> (BoolType, (Monotype arg_ty, Monotype BoolType) :: c1)
    )
  | IntLiteralExpr _ -> (IntType, [])
  | BoolLiteralExpr _ -> (BoolType, [])
  | StringLiteralExpr _ -> (StringType, [])
  | VarExpr v -> 
    (match List.assoc_opt v ctx with
      | None -> raise (TypecheckError ("Variable " ^ v ^ " is not defined"))
      | Some (Monotype t) -> (t, [])
      (* | Some (Polytype (i, t)) -> failwith ("Polytype (" ^ string_of_int i) (* TODO: ??? *) *)
      | Some (Polytype (i, t)) -> let n = next_type_var () in (n, [Monotype n, Polytype (i, t)])
    )
  | UnitExpr -> (UnitType, [])
  | MatchExpr (matchval, branches) -> failwith "stub" (* TODO: auto-generated method stub *)
and unify_constraints (constraints: (tyty * tyty) list): (int * typ) list =
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
  in let rec occurs (i: int) (target: typ): bool =
    match target with
    | FunctionType (l, r) -> occurs i l || occurs i r
    | TupleType lst -> List.exists (occurs i) lst
    | IntType -> false
    | BoolType -> false
    | StringType -> false
    | UnitType -> false
    | UserDeclaredType _ -> false
    | TypeVariable j -> if i = j then true else false
  in let rec solve_constraint (c: tyty * tyty): solved_constraint =
    match c with
    | (Monotype l, Monotype r) -> 
      (match (l, r) with
        | (TypeVariable i, TypeVariable j) when i = j -> Identity
        | (TypeVariable i, TypeVariable j) when i <> j -> Mapping (i, TypeVariable j)
        | (TypeVariable i, t) | (t, TypeVariable i) -> if occurs i t then raise (TypecheckError "Infinite type") else Mapping (i, t)
        | (FunctionType (l, r), FunctionType (l', r')) -> NewConstraints [(Monotype l, Monotype l'); (Monotype r, Monotype r')]
        | (TupleType l1, TupleType l2) ->
          let subconstraints = (try
            List.map2
              (fun a b ->
                (Monotype a, Monotype b)
              )
              l1
              l2
          with
            | Invalid_argument _ -> raise (TypecheckError "Got two TupleTypes with different lengths")
          )
          in
          NewConstraints subconstraints
        | (IntType, IntType) -> Identity
        | (BoolType, BoolType) -> Identity
        | (StringType, StringType) -> Identity
        | (UnitType, UnitType) -> Identity
        | (UserDeclaredType s, UserDeclaredType r) -> if s = r then Identity else raise (TypecheckError ("Type " ^ s ^ " cannot be the same as type " ^ r))
        | (a, b) -> raise (TypecheckError ("Type " ^ string_of_typ a ^ " cannot be the same as type " ^ string_of_typ b))
      )
    | (Polytype (i, t), Monotype r) -> let v = next_type_var () in NewConstraints [(recursive_replace_poly i v t, Monotype r)]
    | (Monotype l, Polytype (i, t)) -> let v = next_type_var () in NewConstraints [(Monotype l, recursive_replace_poly i v t)]
    | (Polytype (il, tl), Polytype (ir, tr)) -> let vl = next_type_var () in let vr = next_type_var () in NewConstraints [(recursive_replace_poly il vl tl, recursive_replace_poly ir vr tr)]
  in let rec unify (substitutions: (int * typ) list) (cs: (tyty * tyty) list): (int * typ) list =
    match cs with
    | [] -> substitutions
    | c :: tail ->
      (match solve_constraint c with
        | Identity -> unify substitutions tail
        | NewConstraints cs' -> unify substitutions (cs' @ tail)
        | Mapping (i, t) -> unify ((i, t) :: substitutions) (List.map (fun x -> let (l, r) = x in (recursive_replace_poly i t l, recursive_replace_poly i t r)) tail)
      )
  in
  unify [] constraints
and apply_substitutions (substitutions: (int * typ) list) (target: typ): typ =
  match target with
    | FunctionType (l, r) -> FunctionType (apply_substitutions substitutions l, apply_substitutions substitutions r)
    | TupleType lst -> TupleType (List.map (apply_substitutions substitutions) lst)
    | IntType -> target
    | BoolType -> target
    | StringType -> target
    | UnitType -> target
    | UserDeclaredType _ -> target
    | TypeVariable j -> (match List.assoc_opt j substitutions with | None -> target | Some t -> t)
and generalize (ctx: context) (target: typ): tyty =
  let rec extract_type_vars (t: typ): int list =
    match t with
    | FunctionType (l, r) -> extract_type_vars l @ extract_type_vars r
    | TupleType lst -> List.concat_map extract_type_vars lst
    | IntType -> []
    | BoolType -> []
    | StringType -> []
    | UnitType -> []
    | UserDeclaredType _ -> []
    | TypeVariable i -> [i]
  and extract_type_vars_poly (t: tyty): int list =
    match t with
    | Monotype m -> extract_type_vars m
    (* I assume I will never have a polytype that doesn't actually appear (such as forall t0. bool) *)
    | Polytype (i, p) -> extract_type_vars_poly p
  in
    let tvs = extract_type_vars target in
    let _ = print_endline (List.map string_of_int tvs |> String.concat " ") in
    let preexisting_tvs = List.concat_map (fun x -> let (name, type') = x in extract_type_vars_poly type') ctx in
    let _ = print_endline (List.map string_of_int preexisting_tvs |> String.concat " ") in
    let final_tvs = List.fold_left (fun acc a -> List.filter (fun x -> x <> a) acc) tvs preexisting_tvs in
    let _ = print_endline (List.map string_of_int final_tvs |> String.concat " ") in
    let ftvs = List.sort_uniq compare final_tvs in
    List.fold_left (fun acc a -> Polytype (a, acc)) (Monotype target) ftvs
(* and generalize (type_vars: int list) (target: typ): tyty = *)
(*   match type_vars with *)
(*   | [] -> Monotype target *)
(*   | head :: tail -> let rest = generalize tail target in *)
(*       Polytype (head, rest) *)
(* and generalize (type_vars: int list) (target: typ): tyty = List.fold_left (fun acc a -> Polytype (a, acc)) (Monotype target) type_vars *)
