open Ast

let next_var = ref 0
let next_type_var (_: unit): typ =
    let () = next_var := !next_var + 1 in
    TypeVariable !next_var

exception TypecheckError of string

let rec typecheck (p: program): (string * typ) list =
  let Program (bds) = p in
  (* let (ctx, constraints) = List.fold_left (fun ((ctx, constraints), acc) -> acc) ([], []) bds in *)
  (* let (ctx, constraints) = List.fold_left (fun acc a -> let (ctx, constraints) = acc in let (ctx', constraints') = typecheck_binding ) ([], []) bds in *)
  let (ctx, constraints) = 
    List.fold_left
      (fun acc a ->
        let (ctx, constraints) = acc in
          let (ctx', constraints') = typecheck_binding ctx constraints a in
            (ctx', constraints')
      )
      ([("string_of_int", FunctionType (IntType, StringType)); ("int_of_string", FunctionType (StringType, IntType)); ("print_string", FunctionType (StringType, UnitType))], [])
      bds
  in
  let _ = print_string (List.map (fun mapping -> let (name, ty) = mapping in name ^ ": " ^ string_of_typ ty) ctx |> String.concat "\n") in
  let _ = print_string (List.map (fun c -> let (first, second) = c in string_of_typ first ^ " = " ^ string_of_typ second) constraints |> String.concat "\n") in
  []
and typecheck_binding (ctx: (string * typ) list) (constraints: (typ * typ) list) (b: binding): ((string * typ) list * (typ * typ) list) =
  match b with
  | NonRecursiveBinding (name, params, ty, value) -> failwith "f"
  | RecursiveBinding (name, params, ty, value) -> failwith "f"
  | TypeDefBinding (name, constructors) ->
      ((List.map (fun (c, args) -> match args with | None -> (c, UserDeclaredType name) | Some(t) -> (c, FunctionType (t, UserDeclaredType name))) constructors) @ ctx, constraints)
and typecheck_expr (ctx: (string * typ) list) (constraints: (typ * typ) list) (e: expr): (typ * (typ * typ) list) =
  match e with
  | LetExpr (name, params, ty, value, body) -> failwith "letexpr"
  | LetRecExpr (name, params, ty, value, body) -> failwith "letrecexpr"
  | IfExpr (cond, iftrue, iffalse) ->
    let (cond_ty, c1) = typecheck_expr ctx constraints cond in
      let (iftrue_ty, c2) = typecheck_expr ctx constraints iftrue in
        let (iffalse_ty, c3) = typecheck_expr ctx constraints iffalse in
          (iftrue_ty, [(iftrue_ty, iffalse_ty); (cond_ty, BoolType)] @ c1 @ c2 @ c3 @ constraints)
  | FunDefExpr (params, ty, body) -> let param_ctx = List.map (fun p -> match p with | UntypedParam x -> (x, next_type_var ()) | TypedParam (x, t) -> (x, t)) params in
      let (body_ty, constraints') = typecheck_expr (param_ctx @ ctx) constraints body in
        let type' = List.fold_right (fun a acc -> FunctionType (a, acc)) (List.map (fun x -> let (_, t) = x in t) param_ctx) body_ty in
          (match ty with
            | None -> (type', constraints' @ constraints)
            | Some t -> (type', (t, body_ty) :: constraints' @ constraints))
  | FunAppExpr (l, r) -> let (l_ty, c1) = typecheck_expr ctx constraints l in let (r_ty, c2) = typecheck_expr ctx constraints r in
    let in' = next_type_var () in let out = next_type_var () in
      (out, [(l_ty, FunctionType (in', out)); (r_ty, in')] @ c1 @ c2 @ constraints)
  (* | TupleExpr (elements) -> TupleType (List.map typecheck_expr elements) *)
                                                                (* this assumes that typecheck_expr prepends to the passed constraints; if not, you need to return (c :: acc, t) *)
  | TupleExpr (elements) -> let (constraints', types) = List.fold_left_map (fun acc el -> let (t, c) = typecheck_expr ctx acc el in (c, t)) constraints elements in (TupleType types, constraints')
  | BinopExpr (l, op, r) -> let (l_ty, c1) = typecheck_expr ctx constraints l in let (r_ty, c2) = typecheck_expr ctx constraints r in
    (match op with
      | Plus -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2 @ constraints)
      | Minus -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2 @ constraints)
      | Times -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2 @ constraints)
      | Divide -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2 @ constraints)
      | Modulo -> (IntType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2 @ constraints)
      | LessThan -> (BoolType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2 @ constraints)
      | Equal -> (BoolType, [(l_ty, IntType); (l_ty, r_ty)] @ c1 @ c2 @ constraints)
      | Concat -> (StringType, [(l_ty, StringType); (l_ty, r_ty)] @ c1 @ c2 @ constraints)
      | And -> (BoolType, [(l_ty, BoolType); (l_ty, r_ty)] @ c1 @ c2 @ constraints)
      | Or -> (BoolType, [(l_ty, BoolType); (l_ty, r_ty)] @ c1 @ c2 @ constraints))
  | UnopExpr (op, arg) -> let (arg_ty, c1) = typecheck_expr ctx constraints arg in
    (match op with
      | NegateInt -> (IntType, (arg_ty, IntType) :: c1 @ constraints)
      | InvertBool -> (BoolType, (arg_ty, BoolType) :: c1 @ constraints)
    )
  | IntLiteralExpr _ -> (IntType, constraints)
  | BoolLiteralExpr _ -> (BoolType, constraints)
  | StringLiteralExpr _ -> (StringType, constraints)
  | VarExpr v -> 
    (match List.assoc_opt v ctx with
      | None -> raise (TypecheckError ("Variable " ^ v ^ " is not defined"))
      | Some t -> (t, constraints))
  | UnitExpr -> (UnitType, constraints)
  | MatchExpr (matchval, branches) -> failwith "stub"

(* let rec unify_constraints (constraints: (typ * typ) list): (int * typ) list = *)
(*   let rec recursive_expand (cs: (typ * typ) list): (typ * typ) list = *)
(*     List.concat_map *)
(*       (fun c -> *)
(*         let (l, r) = c in *)
(*         match (l, r) with *)
(*         | (IntType, IntType) -> [] *)
(*         | (BoolType, BoolType) -> [] *)
(*         | (StringType, StringType) -> [] *)
(*         | (UnitType, UnitType) -> [] *)
(*         | (FunctionType (a, b), FunctionType (c, d)) -> recursive_expand [(a, c); (b, d)] *)
(*         | (TupleType l1, TupleType l2) -> *)
(*           let subconstraints = (try *)
(*             List.map2 *)
(*               (fun a b -> *)
(*                 (a, b) *)
(*               ) *)
(*               l1 *)
(*               l2 *)
(*           with *)
(*             | Invalid_argument _ -> raise (TypecheckError "Got two TupleTypes with different lengths") *)
(*           ) *)
(*           in *)
(*           recursive_expand subconstraints *)
(*         | (UserDeclaredType s, UserDeclaredType r) -> if s = r then [] else raise (TypecheckError ("Type " ^ s ^ " cannot be the same as type " ^ r)) *)
(*         | (TypeVariable i, TypeVariable j) when i = j -> [] *)
(*         | (TypeVariable _, _) -> [c] *)
(*         | (_, TypeVariable _) -> [(r, l)] (* NOTE: this allows us to know that the only types of constraints making it out of this function are (type var, type) *) *)
(*         | (a, b) -> raise (TypecheckError ("Type " ^ string_of_typ a ^ " cannot be the same as type " ^ string_of_typ b)) *)
(*       ) *)
(*       cs *)
(*   in *)
(*   (* let _ = print_endline (List.map (fun x -> let (a, b) = x in string_of_typ a ^ " = " ^ string_of_typ b) (recursive_expand constraints) |> String.concat "\n") in *) *)
(*   let cs = recursive_expand constraints in *)
(*   let equalities = List.filter_map (fun x -> match x with (TypeVariable i, TypeVariable j) when i = j -> Some ((i,j)) | _ -> None) cs in *)
(*     List.map (fun x ->  *)
(*   (* List.filter (fun x -> match x with (TypeVariable i, TypeVariable j) when i = j -> true | _ -> false) cs *) *)
(*   let partial_result =  *)
(*   match cs with *)
(*   | [] -> [] *)
(*   (* | (TypeVariable i, TypeVariable j) :: tail -> *) *)
(*   (*     let replaced = List.map *) *)
(*   (*       (fun x -> match x with *) *)
(*   (*         | (TypeVariable c, TypeVariable d) when i = c && j = d -> (UnitType, UnitType) *) *)
(*   (*       ) *) *)
(*   (*       tail *) *)
(*   (*     in *) *)
(*          *)
(*   | (TypeVariable i, t) :: tail -> *)
(*       let replaced = List.map (fun x -> let (TypeVariable j, t2) = x in if i = j then (t, t2) else x) tail in *)
(*       unify_constraints replaced @ [(i, t)] *)
(*   in *)
(*     List.map (fun x -> let (i, t) = x in  *)
type solved_constraint =
  | Identity
  | NewConstraints of (typ * typ) list
  | Mapping of int * typ
let rec unify_constraints (constraints: (typ * typ) list): (int * typ) list =
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
  in let rec solve_constraint (c: typ * typ): solved_constraint =
    match c with
    | (TypeVariable i, TypeVariable j) when i = j -> Identity
    | (TypeVariable i, TypeVariable j) when i <> j -> Mapping (i, TypeVariable j)
    | (TypeVariable i, t) | (t, TypeVariable i) -> if occurs i t then raise (TypecheckError "Infinite type") else Mapping (i, t)
    | (FunctionType (l, r), FunctionType (l', r')) -> NewConstraints [(l, l'); (r, r')]
    | (TupleType l1, TupleType l2) ->
      let subconstraints = (try
        List.map2
          (fun a b ->
            (a, b)
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
