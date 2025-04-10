exception Variable_not_intialized
exception InvalidOperation
exception OperationNotSupported
exception InvalidBigStepAnswerClosure
exception ReturnEmpty



type exp = 
  | Int of int 
  | Bool of bool 
  | Var of string 
  | Abs of string * exp 
  | App of exp * exp 
  | Absolute of exp
  | Not of exp
  | Add of exp*exp | Sub of exp*exp | Div of exp*exp | Mul of exp*exp | Mod of exp*exp | Exp of exp*exp
  | And of exp*exp | Or of exp*exp | Imp of exp*exp
  | Equ of exp*exp | GtEq of exp*exp | LtEq of exp*exp | Gt of exp*exp | Lt of exp*exp
  | If_Then_Else of (exp*exp*exp)

type closure = CLtype of exp * environmentCLOS
and environmentCLOS = (string * closure) list
and stackCLOS = closure list
and program = exp list

type answer = I of int | B of bool | Nil

let rec power a b = if b = 0 then 1 else a * power a (b-1)
let imp_logic a b = match (a,b) with (true,false) -> false | _ -> true

let rec lookup (var_name, env) = match env with
  | [] -> raise Variable_not_intialized
  | (x, cl)::rest -> if x = var_name then cl else lookup (var_name, rest)

let absApplied (cl, s) = match (cl, s) with
  | (CLtype(Abs(x, e), env), c::c') -> (CLtype(e, (x, c)::env), c')
  | (_, []) -> raise InvalidOperation
  | _ -> raise InvalidOperation

let rec unload (CLtype(e, env)) =
  match e with
  | Int i -> Int i
  | Bool b -> Bool b
  | Var x -> 
      (try 
        let cl = lookup (x, env) in
        unload cl
      with Variable_not_intialized -> Var x)
  | Abs(x, e1) -> Abs(x, unload (CLtype(e1, env)))
  | App(e1, e2) -> App(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Add(e1, e2) -> Add(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Sub(e1, e2) -> Sub(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Mul(e1, e2) -> Mul(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Div(e1, e2) -> Div(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Mod(e1, e2) -> Mod(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Exp(e1, e2) -> Exp(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Absolute e1 -> Absolute(unload (CLtype(e1, env)))
  | Not e1 -> Not(unload (CLtype(e1, env)))
  | And(e1, e2) -> And(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Or(e1, e2) -> Or(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Imp(e1, e2) -> Imp(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Equ(e1, e2) -> Equ(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | GtEq(e1, e2) -> GtEq(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | LtEq(e1, e2) -> LtEq(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Gt(e1, e2) -> Gt(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | Lt(e1, e2) -> Lt(unload (CLtype(e1, env)), unload (CLtype(e2, env)))
  | If_Then_Else(e0, e1, e2) -> If_Then_Else(unload (CLtype(e0, env)), 
                                        unload (CLtype(e1, env)), 
                                        unload (CLtype(e2, env)))

let add (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Int (i1+i2), []) 
  | _ -> raise InvalidOperation

let sub (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Int (i1-i2), []) 
  | _ -> raise InvalidOperation

let mul (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Int (i1*i2), []) 
  | _ -> raise InvalidOperation

let div (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Int (i1/i2), []) 
  | _ -> raise InvalidOperation

let modulus (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Int (i1 mod i2), []) 
  | _ -> raise InvalidOperation

let exponential (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Int (power i1 i2), []) 
  | _ -> raise InvalidOperation

let absolute a1 = match a1 with 
  | CLtype(Int i1, _) -> CLtype(Int (abs i1), []) 
  | _ -> raise InvalidOperation

let andop (a1, a2) = match (a1, a2) with 
  | (CLtype(Bool b1, _), CLtype(Bool b2, _)) -> CLtype(Bool (b1 && b2), []) 
  | _ -> raise InvalidOperation

let orop (a1, a2) = match (a1, a2) with 
  | (CLtype(Bool b1, _), CLtype(Bool b2, _)) -> CLtype(Bool (b1 || b2), []) 
  | _ -> raise InvalidOperation

let imp (a1, a2) = match (a1, a2) with 
  | (CLtype(Bool b1, _), CLtype(Bool b2, _)) -> CLtype(Bool (imp_logic b1 b2), []) 
  | _ -> raise InvalidOperation

let notop a1 = match a1 with 
  | CLtype(Bool b1, _) -> CLtype(Bool (not b1), []) 
  | _ -> raise InvalidOperation

let equal (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Bool (i1 = i2), []) 
  | _ -> raise InvalidOperation

let greaterthanorequal (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Bool (i1 >= i2), []) 
  | _ -> raise InvalidOperation

let lessthanorequal (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Bool (i1 <= i2), []) 
  | _ -> raise InvalidOperation

let greaterthan (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Bool (i1 > i2), []) 
  | _ -> raise InvalidOperation

let lessthan (a1, a2) = match (a1, a2) with 
  | (CLtype(Int i1, _), CLtype(Int i2, _)) -> CLtype(Bool (i1 < i2), []) 
  | _ -> raise InvalidOperation

let rec krivinemachine cl (s:stackCLOS) = match cl with
  | CLtype (Int _, _) -> cl
  | CLtype (Bool _, _) -> cl
  | CLtype (Var v, env) -> 
      let cl' = lookup (v, env) in
      krivinemachine cl' s
  | CLtype (Abs(_, _), _) -> 
      (match s with
      | [] -> cl
      | _ -> 
          let (cl', s') = absApplied (cl, s) in
          krivinemachine cl' s')
  | CLtype (App(e1, e2), env) -> 
      krivinemachine (CLtype(e1, env)) (CLtype(e2, env)::s)
  
  | CLtype (Add(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      (match (v1, v2) with
      | (CLtype(Int _, _), CLtype(Int _, _)) -> 
          krivinemachine (add (v1, v2)) s
      | _ -> raise InvalidOperation)
  | CLtype (Sub(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (sub (v1, v2)) s
  | CLtype (Mul(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (mul (v1, v2)) s
  | CLtype (Div(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (div (v1, v2)) s
  | CLtype (Exp(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (exponential (v1, v2)) s
  | CLtype (Mod(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (modulus (v1, v2)) s
  | CLtype (Absolute e1, env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      krivinemachine (absolute v1) s
  | CLtype (And(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (andop (v1, v2)) s
  | CLtype (Or(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (orop (v1, v2)) s
  | CLtype (Imp(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (imp (v1, v2)) s
  | CLtype (Not e1, env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      krivinemachine (notop v1) s
  | CLtype (Equ(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (equal (v1, v2)) s
  | CLtype (GtEq(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (greaterthanorequal (v1, v2)) s
  | CLtype (LtEq(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (lessthanorequal (v1, v2)) s
  | CLtype (Gt(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (greaterthan (v1, v2)) s
  | CLtype (Lt(e1, e2), env) ->
      let v1 = krivinemachine (CLtype(e1, env)) [] in
      let v2 = krivinemachine (CLtype(e2, env)) [] in
      krivinemachine (lessthan (v1, v2)) s
  | CLtype (If_Then_Else(e0, e1, e2), env) ->
      let condition = krivinemachine (CLtype(e0, env)) [] in
      (match condition with
      | CLtype(Bool true, _) -> krivinemachine (CLtype(e1, env)) s
      | CLtype(Bool false, _) -> krivinemachine (CLtype(e2, env)) s
      | _ -> raise InvalidOperation)

let rec string_of_exp = function
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Var x -> x
  | Abs(x, e) -> "λ" ^ x ^ "." ^ string_of_exp e
  | App(e1, e2) -> "(" ^ string_of_exp e1 ^ " " ^ string_of_exp e2 ^ ")"
  | Add(e1, e2) -> "(" ^ string_of_exp e1 ^ " + " ^ string_of_exp e2 ^ ")"
  | Sub(e1, e2) -> "(" ^ string_of_exp e1 ^ " - " ^ string_of_exp e2 ^ ")"
  | Mul(e1, e2) -> "(" ^ string_of_exp e1 ^ " * " ^ string_of_exp e2 ^ ")"
  | Div(e1, e2) -> "(" ^ string_of_exp e1 ^ " / " ^ string_of_exp e2 ^ ")"
  | Mod(e1, e2) -> "(" ^ string_of_exp e1 ^ " mod " ^ string_of_exp e2 ^ ")"
  | Exp(e1, e2) -> "(" ^ string_of_exp e1 ^ " ^ " ^ string_of_exp e2 ^ ")"
  | Absolute e -> "| " ^ string_of_exp e ^ " |"
  | Not e -> "¬" ^ string_of_exp e
  | And(e1, e2) -> "(" ^ string_of_exp e1 ^ " ∧ " ^ string_of_exp e2 ^ ")"
  | Or(e1, e2) -> "(" ^ string_of_exp e1 ^ " v " ^ string_of_exp e2 ^ ")"
  | Imp(e1, e2) -> "(" ^ string_of_exp e1 ^ " ⇒ " ^ string_of_exp e2 ^ ")"
  | Equ(e1, e2) -> "(" ^ string_of_exp e1 ^ " = " ^ string_of_exp e2 ^ ")"
  | GtEq(e1, e2) -> "(" ^ string_of_exp e1 ^ " ≥ " ^ string_of_exp e2 ^ ")"
  | LtEq(e1, e2) -> "(" ^ string_of_exp e1 ^ " ≤ " ^ string_of_exp e2 ^ ")"
  | Gt(e1, e2) -> "(" ^ string_of_exp e1 ^ " > " ^ string_of_exp e2 ^ ")"
  | Lt(e1, e2) -> "(" ^ string_of_exp e1 ^ " < " ^ string_of_exp e2 ^ ")"
  | If_Then_Else(e0, e1, e2) -> "if " ^ string_of_exp e0 ^ " then " ^ string_of_exp e1 ^ " else " ^ string_of_exp e2

let rec executekrivine (prog: program) (env: environmentCLOS): answer = match prog with
  | p::prog' -> 
    let cl = krivinemachine (CLtype(p, env)) [] in
    (match cl with
      | CLtype (Int i, _) -> I i
      | CLtype (Bool b, _) -> B b
      | CLtype (Abs(x, e), env') -> 
          let lambda_term = unload cl in
          Printf.printf "Lambda term: %s\n" (string_of_exp lambda_term);
          Nil
      | CLtype (e, _) -> 
          Printf.printf "Unexpected expression: %s\n" (string_of_exp e);
          raise InvalidBigStepAnswerClosure)
  | [] -> raise ReturnEmpty



(*-----------------------------------------------------------------------------------------------*)
(*Testcases*)

let safe_print f =
  try f () with
  | Variable_not_intialized -> print_endline "Error: Variable not initialized"
  | InvalidOperation -> print_endline "Error: Invalid operation"
  | OperationNotSupported -> print_endline "Error: Operation not supported"
  | InvalidBigStepAnswerClosure -> print_endline "Error: Invalid closure"
  | ReturnEmpty -> print_endline "Error: Empty return"
  | e -> Printf.printf "Unexpected exception: %s\n" (Printexc.to_string e)
  
let print_answer = function
  | I i -> Printf.printf "Int: %d\n" i
  | B b -> Printf.printf "Bool: %b\n" b
  | Nil -> ()

let id = Abs("x", Var "x")         (* λx.x *)
let const_five = Abs("x", Int 5)   (* λx.5 *)
let apply_id_to_y = App(id, Var "y")  (* (λx.x) y *)
let add_example = Add(Int 3, Int 4)   (* 3 + 4 => 7*)
let nested = App(Abs("x", Add(Var "x", Int 1)), Int 2)  (* (λx.x+1) 2 => 3*)
let lazy_conditional =
  If_Then_Else(
    Bool true,
    Int 1,
    Div(Int 1, Int 0)  (* should NOT raise error if lazy => Int 1*)
  )
let bool_expr =
  And(
    Bool true,
    Or(Bool false, Bool true)
  ) (* should evaluate to Bool true *)
let curried_add =
  App(
    App(
      Abs("x", Abs("y", Add(Var "x", Var "y"))),
      Int 3
    ),
    Int 4
  ) (* Int 7 *)

let y_combinator =
  Abs("f",
    App(
      Abs("x", App(Var "f", App(Var "x", Var "x"))),
      Abs("x", App(Var "f", App(Var "x", Var "x")))
    )
  )

let fibonacci =
  Abs("f",
    Abs("n",
      If_Then_Else(
        LtEq(Var "n", Int 1),
        Var "n",
        Add(
          App(Var "f", Sub(Var "n", Int 1)),
          App(Var "f", Sub(Var "n", Int 2))
        )
      )
    )
  )
let fib_prog = App(App(y_combinator, fibonacci), Int 7) (* Fib(7) => 13*)

let factorial =
  Abs("f",
    Abs("n",
      If_Then_Else(
        Equ(Var "n", Int 0),
        Int 1,
        Mul(Var "n", App(Var "f", Sub(Var "n", Int 1)))
      )
    )
  )
let fact_prog = App(App(y_combinator, factorial), Int 5) (* 5! => 120 *)

(* Identity applied to itself *)
let self_apply = App(id, id) (* λx.x *)

(* Shadowing: λx.λx.x *)
let shadow = Abs("x", Abs("x", Var "x"))
(* Expected: Abs("x", Var "x") — inner binding should shadow outer *)

(* Nested application: ((λx.λy.x + y) 3) 4 *)
let nested_apply = App(App(Abs("x", Abs("y", Add(Var "x", Var "y"))), Int 3), Int 4)
(* Expected: Int 7 *)

(* Boolean NOT: if true then false else true *)
let not_true = If_Then_Else(Bool true, Bool false, Bool true)
(* Expected: Bool false *)

(* Logical expression: not (x > 5) *)
let logical_expr = Not(Gt(Var "x", Int 5))
(* Expected: Depends on value of x — symbolic unless bound *)

(* Chain of lambdas: λx.λy.λz.x + y + z *)
let triple_add = Abs("x", Abs("y", Abs("z", Add(Add(Var "x", Var "y"), Var "z"))))
let triple_apply = App(App(App(triple_add, Int 1), Int 2), Int 3)
(* Expected: Int 6 *)

(* Higher-order function: apply_twice = λf.λx.f(f x) *)
let apply_twice = Abs("f", Abs("x", App(Var "f", App(Var "f", Var "x"))))
let plus1 = Abs("n", Add(Var "n", Int 1))
let apply_twice_5 = App(App(apply_twice, plus1), Int 5)
(* Expected: Int 7 *)

(* Church pair and projection *)
let pair = Abs("x", Abs("y", Abs("f", App(App(Var "f", Var "x"), Var "y"))))
let fst = Abs("p", App(Var "p", Abs("x", Abs("y", Var "x"))))
let snd = Abs("p", App(Var "p", Abs("x", Abs("y", Var "y"))))
let test_pair = App(App(pair, Int 10), Int 20)
let test_fst = App(fst, test_pair)
let test_snd = App(snd, test_pair)
(* Expected: test_fst → Int 10, test_snd → Int 20 *)

(* Simulating let: let x = 5 in x + 1 → (λx.x + 1) 5 *)
let simulated_let = App(Abs("x", Add(Var "x", Int 1)), Int 5)
(* Expected: Int 6 *)

(* Boolean equality *)
let bool_eq = Equ(Bool true, Bool true)
(* Expected: Bool true *)

(* Deep nested application *)
let deep_nesting = App(Abs("x", App(Abs("y", Add(Var "x", Var "y")), Int 2)), Int 3)
(* Expected: Int 5 *)

let run_tests () =
  print_endline "Running Krivine Tests:";
  Printf.printf "id: ";
  safe_print (fun () -> print_answer (executekrivine [id] []));
  print_endline "Expected: λx.x\n";
  Printf.printf "const_five: ";
  safe_print (fun () -> print_answer (executekrivine [const_five] []));
  print_endline "Expected: λx.5\n";
  Printf.printf "apply_id_to_y: ";
  safe_print (fun () -> print_answer (executekrivine [apply_id_to_y] []));
  print_endline "Expected: y\n";
  Printf.printf "add_example: ";
  safe_print (fun () -> print_answer (executekrivine [add_example] []));
  print_endline "Expected: Int 7\n";
  Printf.printf "nested: ";
  safe_print (fun () -> print_answer (executekrivine [nested] []));
  print_endline "Expected: Int 3\n";
  Printf.printf "lazy_conditional: ";
  safe_print (fun () -> print_answer (executekrivine [lazy_conditional] []));
  print_endline "Expected: Int 1\n";
  Printf.printf "bool_expr: ";
  safe_print (fun () -> print_answer (executekrivine [bool_expr] []));
  print_endline "Expected: Bool true\n";
  Printf.printf "curried_add: ";
  safe_print (fun () -> print_answer (executekrivine [curried_add] []));
  print_endline "Expected: Int 7\n";
  Printf.printf "fib_prog: ";
  safe_print (fun () -> print_answer (executekrivine [fib_prog] []));
  print_endline "Expected: Int 13\n";
  Printf.printf "self_apply: ";
  safe_print (fun () -> print_answer (executekrivine [self_apply] []));
  print_endline "Expected: λx.x\n";
  Printf.printf "shadow: ";
  safe_print (fun () -> print_answer (executekrivine [shadow] []));
  print_endline "Expected: λx.x\n";
  Printf.printf "nested_apply: ";
  safe_print (fun () -> print_answer (executekrivine [nested_apply] []));
  print_endline "Expected: Int 7\n";
  Printf.printf "not_true: ";
  safe_print (fun () -> print_answer (executekrivine [not_true] []));
  print_endline "Expected: Bool false\n";
  Printf.printf "logical_expr: ";
  safe_print (fun () -> print_answer (executekrivine [logical_expr] []));
  print_endline "Expected: Depends on x\n";
  Printf.printf "triple_apply: ";
  safe_print (fun () -> print_answer (executekrivine [triple_apply] []));
  print_endline "Expected: Int 6\n";
  Printf.printf "apply_twice_5: ";
  safe_print (fun () -> print_answer (executekrivine [apply_twice_5] []));
  print_endline "Expected: Int 7\n"; 
  Printf.printf "test_fst: " ;
  safe_print (fun () -> print_answer (executekrivine [test_fst] []));
  print_endline "Expected: Int 10\n";
  Printf.printf "test_snd: ";
  safe_print (fun () -> print_answer (executekrivine [test_snd] []));
  print_endline "Expected: Int 20\n";
  Printf.printf "simulated_let: ";
  safe_print (fun () -> print_answer (executekrivine [simulated_let] []));
  print_endline "Expected: Int 6\n";
  Printf.printf "bool_eq: ";
  safe_print (fun () -> print_answer (executekrivine [bool_eq] []));
  print_endline "Expected: Bool true\n";
  Printf.printf "deep_nesting: ";
  safe_print (fun () -> print_answer (executekrivine [deep_nesting] []));
  print_endline "Expected: Int 5\n";
;;

run_tests ()