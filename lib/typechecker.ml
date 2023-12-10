open Ast

let next_var = ref 0
let next_type_var (_: unit): typ =
    let () = next_var := !next_var + 1 in
    TypeVariable !next_var

exception TypecheckError of string

type solved_constraint =
  | Identity
  | NewConstraints of (typ * typ) list
  | Mapping of int * typ

type context = (string * typ) list

let rec typecheck (p: program): context =
  let Program (bds) = p in
  (* let (ctx, constraints) = List.fold_left (fun ((ctx, constraints), acc) -> acc) ([], []) bds in *)
  (* let (ctx, constraints) = List.fold_left (fun acc a -> let (ctx, constraints) = acc in let (ctx', constraints') = typecheck_binding ) ([], []) bds in *)
  let ctx =
    List.fold_left
      typecheck_binding
      [("string_of_int", FunctionType (IntType, StringType)); ("int_of_string", FunctionType (StringType, IntType)); ("print_string", FunctionType (StringType, UnitType))]
      bds
  in
  (* let _ = print_string (List.map (fun mapping -> let (name, ty) = mapping in name ^ ": " ^ string_of_tyty ty) ctx |> String.concat "\n") in *)
  ctx
and typecheck_binding (ctx: context) (b: binding): context =
  let _ = print_endline ("Calling typecheck_binding on `" ^ string_of_binding 0 b ^ "` with context\n  " ^ (List.map (fun (name, ty) -> name ^ ": " ^ string_of_typ ty) ctx |> String.concat "\n  ")) in
  let result = typecheck_binding' ctx b in
  let _ = print_endline ("Exiting typecheck_binding on `" ^ string_of_binding 0 b ^ "` with context\n  " ^ (List.map (fun (name, ty) -> name ^ ": " ^ string_of_typ ty) result |> String.concat "\n  ")) in
  result
and typecheck_binding' (ctx: context) (b: binding): context =
  match b with
  | NonRecursiveBinding (name, params, ty, value) ->
      let param_ctx = List.map (fun p -> match p with | UntypedParam x -> (x, next_type_var ()) | TypedParam (x, t) -> (x, t)) params in
        let (value_ty, constraints') = typecheck_expr (param_ctx @ ctx) value in
          let value_type = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, t) = x in t) param_ctx) value_ty in
    (* let _ = print_endline (List.map (fun x -> let (l, r) = x in string_of_tyty l ^ " ~ " ^ string_of_tyty r) constraints' |> String.concat "\n") in *)
            let substitutions = unify_constraints ((match ty with | None -> [] | Some t -> [(t, value_ty)]) @ constraints') in
    (* let _ = print_endline (List.map (fun x -> let (i, t) = x in string_of_int i ^ " > " ^ string_of_typ t) substitutions |> String.concat "\n") in *)
              let substituted = apply_substitutions substitutions value_type in
    (* let _ = print_endline (string_of_typ substituted) in *)
                let generalized = generalize ctx substituted in
                  (name, generalized) :: ctx
  | RecursiveBinding (name, params, ty, value) ->
      let param_ctx' = List.map (fun p -> match p with | UntypedParam x -> (x, next_type_var ()) | TypedParam (x, t) -> (x, t)) params in (* (name, tyty) list - does not include self *)
    let this_binding_type_var = next_type_var () in
        let param_ctx = (name, this_binding_type_var) :: param_ctx' in (* add this function itself to the "parameters" *)
          let (value_ty, constraints') = typecheck_expr (param_ctx @ ctx) value in (* type of value of this binding (right side of =) *)
                                                                                  (* MUST be param_ctx' below so that we don't include the binding itself as a parameter *)
            let value_type = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, t) = x in t) param_ctx') value_ty in (* type of binding as a whole (either t or function to t) *)
    let other_constraints = (match ty with | None -> [] | Some t -> [(t, value_ty)]) @ [(this_binding_type_var, value_type)] in
              let substitutions = unify_constraints (other_constraints @ constraints') in
                let substituted = apply_substitutions substitutions value_type in
                  let generalized = generalize ctx substituted in
                    (name, generalized) :: ctx
  | TypeDefBinding (name, constructors) ->
      (List.map (fun (c, args) -> match args with | None -> (c, UserDeclaredType name) | Some(t) -> (c, FunctionType (t, UserDeclaredType name))) constructors) @ ctx
and typecheck_expr (ctx: context) (e: expr): (typ * (typ * typ) list) =
  let _ = print_endline ("Calling typecheck_expr on `" ^ string_of_expr e ^ "` with context:\n  " ^ (List.map (fun x -> let (name, ty) = x in name ^ ": " ^ string_of_typ ty) ctx |> String.concat "\n  ")) in
  let (t, constraints) = typecheck_expr' ctx e in
let _ = print_endline ("Exiting typecheck_expr on `" ^ string_of_expr e ^ "` (: " ^ string_of_typ t ^ ") with constraints:\n  " ^ (List.map (fun x -> let (l, r) = x in string_of_typ l ^ " ~ " ^ string_of_typ r) constraints |> String.concat "\n  ")) in
  (t, constraints)
and typecheck_expr' (ctx: context) (e: expr): (typ * (typ * typ) list) =
  match e with
  | LetExpr (name, params, ty, value, body) ->
    (match params with
      (* | [] -> let (value_type, constraints) = typecheck_expr ctx value in *)
      (**)
      | _ ->
        let param_ctx = List.map (fun p -> match p with | UntypedParam x -> (x, next_type_var ()) | TypedParam (x, t) -> (x, t)) params in
          let (value_ty, constraints') = typecheck_expr (param_ctx @ ctx) value in
            let value_type = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, t) = x in t) param_ctx) value_ty in
              let substitutions = unify_constraints ((match ty with | None -> [] | Some t -> [(t, value_ty)]) @ constraints') in
                let substituted = apply_substitutions substitutions value_type in
                  let generalized = generalize ctx substituted in
                    let (body_ty, new_constraints) = typecheck_expr ((name, generalized) :: ctx) body in
                      (body_ty, new_constraints @ constraints')
                    (* typecheck_expr ((name, generalized) :: ctx) body *)
        (* (UnitType, []) *)
    )
  | LetRecExpr (name, params, ty, value, body) ->
      let param_ctx' = List.map (fun p -> match p with | UntypedParam x -> (x, next_type_var ()) | TypedParam (x, t) -> (x, t)) params in
    let this_binding_type_var = next_type_var () in
        let param_ctx = (name, this_binding_type_var) :: param_ctx' in
          let (value_ty, constraints') = typecheck_expr (param_ctx @ ctx) value in
                                                                                  (* MUST be param_ctx' below so that we don't include the binding itself as a parameter *)
            let value_type = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, t) = x in t) param_ctx') value_ty in
    let other_constraints = (match ty with | None -> [] | Some t -> [(t, value_ty)]) @ [(this_binding_type_var, value_type)] in
              let substitutions = unify_constraints (other_constraints @ constraints') in
                let substituted = apply_substitutions substitutions value_type in
                  let generalized = generalize ctx substituted in
                    let (body_ty, new_constraints) = typecheck_expr ((name, generalized) :: ctx) body in
                      (body_ty, new_constraints @ constraints')
                    (* typecheck_expr ((name, generalized) :: ctx) body *)
  | IfExpr (cond, iftrue, iffalse) ->
    let (cond_ty, c1) = typecheck_expr ctx cond in
      let (iftrue_ty, c2) = typecheck_expr ctx iftrue in
        let (iffalse_ty, c3) = typecheck_expr ctx iffalse in
          (iftrue_ty, [(iftrue_ty, iffalse_ty); (cond_ty, BoolType)] @ c1 @ c2 @ c3)
  | FunDefExpr (params, ty, body) -> let param_ctx = List.map (fun p -> match p with | UntypedParam x -> (x, next_type_var ()) | TypedParam (x, t) -> (x, t)) params in
      let (body_ty, constraints') = typecheck_expr (param_ctx @ ctx) body in
        let type' = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, t) = x in t) param_ctx) body_ty in
          (match ty with
            | None -> (type', constraints')
            | Some t -> (type', (t, body_ty) :: constraints'))
  | FunAppExpr (l, r) -> let (l_ty, c1) = typecheck_expr ctx l in let (r_ty, c2) = typecheck_expr ctx r in
    let in' = next_type_var () in let out = next_type_var () in
      (out, [(l_ty, FunctionType (in', out)); (r_ty, in')] @ c1 @ c2)
  | TupleExpr (elements) -> let (constraints', types) = List.fold_left_map (fun acc el -> let (t, c) = typecheck_expr ctx el in (c @ acc, t)) [] elements in (TupleType types, constraints')
  | BinopExpr (l, op, r) -> let (l_ty, c1) = typecheck_expr ctx l in let (r_ty, c2) = typecheck_expr ctx r in
    (match op with
      | Plus -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2)
      | Minus -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2)
      | Times -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2)
      | Divide -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2)
      | Modulo -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2)
      | LessThan -> (BoolType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2)
      | Equal -> (BoolType, [(l_ty, r_ty)] @ c1 @ c2)
      | Concat -> (StringType, [(l_ty, StringType); (l_ty, r_ty)] @ c1 @ c2)
      | And -> (BoolType, [(l_ty, BoolType); (l_ty, r_ty)] @ c1 @ c2)
      | Or -> (BoolType, [(l_ty, BoolType); (l_ty, r_ty)] @ c1 @ c2))
  | UnopExpr (op, arg) -> let (arg_ty, c1) = typecheck_expr ctx arg in
    (match op with
      | NegateInt -> (IntType, (arg_ty, IntType) :: c1)
      | InvertBool -> (BoolType, (arg_ty, BoolType) :: c1)
    )
  | IntLiteralExpr _ -> (IntType, [])
  | BoolLiteralExpr _ -> (BoolType, [])
  | StringLiteralExpr _ -> (StringType, [])
  | VarExpr v -> 
    (match List.assoc_opt v ctx with
      | None -> raise (TypecheckError ("Variable " ^ v ^ " is not defined"))
      | Some t -> (t, [])
    )
  | UnitExpr -> (UnitType, [])
  | MatchExpr (matchval, branches) ->
    let (matchty, constraints) = typecheck_expr ctx matchval in
    let output_ty = next_type_var () in
    let checked_branches = List.concat_map
      (fun branch ->
        let MatchBranch (ctor, pvs, e) = branch in
        match List.assoc_opt ctor ctx with
        | None -> raise (TypecheckError ("Constructor '" ^ ctor ^ "' does not exist and thus cannot be used in match branch"))
        | Some (t) ->
          let (the_ty, (this_output_ty, new_constraints)) = match (t, pvs) with
            | (Polytype _, _) -> raise (TypecheckError "Cannot match on polytypes")
            | (UserDeclaredType u, None) -> (UserDeclaredType u, typecheck_expr ctx e)
            | (UserDeclaredType _, Some _) -> raise (TypecheckError ("Constructor '" ^ ctor ^ "' does not take parameters"))
            | (FunctionType (TupleType lst, r), Some (MultiplePatternVars lst2)) ->
              let new_ctx = List.map2 (fun ty name -> (name, ty)) lst lst2 in
                (r, typecheck_expr (new_ctx @ ctx) e)
            | (FunctionType (TupleType _, _), Some (SinglePatternVar _)) -> raise (TypecheckError ("Constructor '" ^ ctor ^ "' takes multiple parameters"))
            | (FunctionType (l, r), Some (SinglePatternVar v)) ->
                (r, typecheck_expr ((v, l) :: ctx) e)
            | (FunctionType (_, _), Some (MultiplePatternVars _)) -> raise (TypecheckError ("Constructor '" ^ ctor ^ "' only takes one parameter"))
            | (FunctionType (_, _), None) -> raise (TypecheckError ("Constructor '" ^ ctor ^ "' must take parameters"))
            | (_, _) -> raise (TypecheckError ("Cannot match on non-user-defined-type"))
          in

          [(matchty, the_ty); (output_ty, this_output_ty)] @ new_constraints
      )
      branches
    in
      (output_ty, checked_branches @ constraints)
and unify_constraints (constraints: (typ * typ) list): (int * typ) list =
(*   let _ = print_endline ("Calling typecheck_expr on `" ^ string_of_expr e ^ "` with context:\n  " ^ (List.map (fun x -> let (name, ty) = x in name ^ ": " ^ string_of_tyty ty) ctx |> String.concat "\n  ")) in *)
(*   let (t, constraints) = typecheck_expr' ctx e in *)
(* let _ = print_endline ("Exiting typecheck_expr on `" ^ string_of_expr e ^ "` (: " ^ string_of_typ t ^ ") with constraints:\n  " ^ (List.map (fun x -> let (l, r) = x in string_of_tyty l ^ " ~ " ^ string_of_tyty r) constraints |> String.concat "\n  ")) in *)
(*   (t, constraints) *)
let _ = print_endline ("Calling unify_constraints with constraints\n  " ^ (List.map (fun x -> let (l, r) = x in string_of_typ l ^ " ~ " ^ string_of_typ r) constraints |> String.concat "\n  ")) in
let substitutions = unify_constraints' constraints in
let _ = print_endline ("Exiting unify_constraints with substitutions\n  " ^ (List.map (fun x -> let (l, r) = x in "t" ^ string_of_int l ^ " > " ^ string_of_typ r) substitutions |> String.concat "\n  ")) in
  substitutions
and unify_constraints' (constraints: (typ * typ) list): (int * typ) list =
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
    | Polytype (j, t') -> if i = j then failwith "Illegal" else Polytype (j, recursive_replace i t t')
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
    | Polytype (j, t) -> i = j || occurs i t
  in let rec solve_constraint (c: typ * typ): solved_constraint =
    match c with
    | (Polytype (il, tl), Polytype (ir, tr)) -> let vl = next_type_var () in let vr = next_type_var () in NewConstraints [(recursive_replace il vl tl, recursive_replace ir vr tr)]
    | (Polytype (i, t), r) -> let v = next_type_var () in NewConstraints [(recursive_replace i v t, r)]
    | (l, Polytype (i, t)) -> let v = next_type_var () in NewConstraints [(l, recursive_replace i v t)]
    | (TypeVariable i, TypeVariable j) when i = j -> Identity
    | (TypeVariable i, TypeVariable j) when i <> j -> Mapping (i, TypeVariable j)
    | (TypeVariable i, t) | (t, TypeVariable i) -> if occurs i t then raise (TypecheckError "Infinite type") else Mapping (i, t)
    | (FunctionType (l, r), FunctionType (l', r')) -> NewConstraints [(l, l'); (r, r')]
    | (TupleType l1, TupleType l2) ->
      let subconstraints = (try
        List.combine
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
  in let rec unify (substitutions: (int * typ) list) (cs: (typ * typ) list): (int * typ) list =
    match cs with
    | [] -> substitutions
    | c :: tail ->
      (match solve_constraint c with
        | Identity -> unify substitutions tail
        | NewConstraints cs' -> unify substitutions (cs' @ tail)
        | Mapping (i, t) -> unify ((i, t) :: substitutions) (List.map (fun x -> let (l, r) = x in (recursive_replace i t l, recursive_replace i t r)) tail)
      )
  in
  unify [] constraints
and apply_substitutions (substitutions: (int * typ) list) (target: typ): typ =
  let _ = print_endline ("Calling apply_substitutions on " ^ string_of_typ target ^ " with substitutions\n  " ^ (List.map (fun x -> let (l, r) = x in "t" ^ string_of_int l ^ " > " ^ string_of_typ r) substitutions |> String.concat "\n  ")) in
  let result = apply_substitutions' substitutions target in
  let _ = print_endline ("Exiting apply_substitutions on " ^ string_of_typ target ^ " with " ^ string_of_typ result)  in
  result
and apply_substitutions' (substitutions: (int * typ) list) (target: typ): typ =
  (* let _ = print_endline ("  " ^ string_of_typ target) in *)
  match target with
    | FunctionType (l, r) -> FunctionType (apply_substitutions substitutions l, apply_substitutions substitutions r)
    | TupleType lst -> TupleType (List.map (apply_substitutions substitutions) lst)
    | IntType -> target
    | BoolType -> target
    | StringType -> target
    | UnitType -> target
    | UserDeclaredType _ -> target
    | TypeVariable j -> (match List.assoc_opt j substitutions with | None -> target | Some t -> apply_substitutions substitutions t)
    | Polytype (i, t) -> Polytype (i, apply_substitutions substitutions t)
and generalize (ctx: context) (target: typ): typ =
  let _ = print_endline ("Calling generalize on " ^ string_of_typ target ^ " with context:\n  " ^ (List.map (fun x -> let (name, ty) = x in name ^ ": " ^ string_of_typ ty) ctx |> String.concat "\n  ")) in
  let result = generalize' ctx target in
  let _ = print_endline ("Exiting generalize on " ^ string_of_typ target ^ " with " ^ string_of_typ result)  in
  result
and generalize' (ctx: context) (target: typ): typ =
  let rec extract_type_vars (t: typ): typ * int list * int list =
    let _ = print_endline ("Calling extract_type_vars on " ^ string_of_typ t) in
    let (new_ty, force_override, tvs) = extract_type_vars' t in
    let _ = print_endline ("Exiting extract_type_vars on " ^ string_of_typ t ^ " with new type " ^ string_of_typ new_ty ^ " forced vars: " ^ (List.map string_of_int force_override |> String.concat " ") ^ " tvs: " ^ (List.map string_of_int tvs |> String.concat " ")) in
    (new_ty, force_override, tvs)
  and extract_type_vars' (t: typ): typ * int list * int list =
    match t with
    | FunctionType (l, r) ->
      let (lt, f1, ltvs) = extract_type_vars l in
      let (rt, f2, rtvs) = extract_type_vars r in
      (FunctionType (lt, rt), f1 @ f2, ltvs @ rtvs)
    (* | TupleType lst -> let (acc, blist) = List.fold_left_map (fun (acc, a) -> let (t', tvs) = extract_type_vars a in (acc @ tvs, t')) [] lst in (TupleType blist, acc) *)
    | TupleType lst ->
      let tvs = List.concat_map (fun x -> let (_, _, tv) = extract_type_vars x in tv) lst in
      let forced = List.concat_map (fun x -> let (_, f, _) = extract_type_vars x in f) lst in
      let lst' = List.map (fun x -> let (t', _, _) = extract_type_vars x in t') lst in
      (TupleType lst', forced, tvs)
    | IntType -> (IntType, [], [])
    | BoolType -> (BoolType, [], [])
    | StringType -> (StringType, [], [])
    | UnitType -> (UnitType, [], [])
    | UserDeclaredType _ -> (t, [], [])
    | TypeVariable i -> (t, [], [i])
    | Polytype (i, t') -> let (t'', forced, tvs) = extract_type_vars t' in (t'', i :: forced, tvs)
  in
    let (target', force_override_polytypes, tvs) = extract_type_vars target in
    let _ = print_endline ("tvs: " ^ (List.map string_of_int tvs |> String.concat " ")) in
    let _ = print_endline ("forced: " ^ (List.map string_of_int force_override_polytypes |> String.concat " ")) in
      let preexisting_tvs = List.concat_map (fun x -> let (name, type') = x in let (_, _, tvs) = extract_type_vars type' in tvs) ctx in
    let _ = print_endline ("preexisting: " ^ (List.map string_of_int preexisting_tvs |> String.concat " ")) in
        let final_tvs' = List.fold_left (fun acc a -> List.filter (fun x -> x <> a) acc) tvs preexisting_tvs in
    let _ = print_endline ("final (pre-override): " ^ (List.map string_of_int final_tvs' |> String.concat " ")) in
          let final_tvs = force_override_polytypes @ final_tvs' in
    let _ = print_endline ("final (real): " ^ (List.map string_of_int final_tvs |> String.concat " ")) in
            let ftvs = List.sort_uniq compare final_tvs in
              List.fold_left (fun acc a -> Polytype (a, acc)) target' ftvs
(* and generalize (type_vars: int list) (target: typ): tyty = *)
(*   match type_vars with *)
(*   | [] -> Monotype target *)
(*   | head :: tail -> let rest = generalize tail target in *)
(*       Polytype (head, rest) *)
(* and generalize (type_vars: int list) (target: typ): tyty = List.fold_left (fun acc a -> Polytype (a, acc)) (Monotype target) type_vars *)
