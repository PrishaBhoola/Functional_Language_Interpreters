exception Variable_not_intialized
exception InvalidOperation

type exp = 
  | Nil 
  | Int of int 
  | Bool of bool 
  | Var of string 
  | Abs of string * exp 
  | App of exp * exp 
  | Absolute of exp
  | Not of exp
  | Add of exp*exp | Sub of exp*exp | Div of exp*exp | Mul of exp*exp | Mod of exp*exp | Exp of exp*exp
  | And of exp*exp | Or of exp*exp | Imp of exp*exp
  | Equ of exp*exp | GTEqu of exp*exp | LTEqu of exp*exp | Grt of exp*exp | Lst of exp*exp
  | Ifthenelse of (exp*exp*exp)
  | LetRec of string * exp * exp
  
type opcode =
  | INT of int
  | BOOL of bool
  | VAR of string
  | CLOS of string * opcode list
  | APP
  | ADD | SUB | MUL | DIV | MOD | EXP
  | ABS
  | AND | OR | NOT | IMP
  | EQ | GT | LT | GTEQ | LTEQ
  | IF of opcode list * opcode list 
  | LETREC of string * opcode list
  | RET 
  
type value = I of int | B of bool | C of string * opcode list * environment | E of exp
and stack = value list
and environment = (string * value) list
and control = exp list
and dump = (stack * environment * control) list

let rec power a b = if b = 0 then 1 else a * power a (b-1)
let imp_logic a b = match (a,b) with (true,false) -> false | _ -> true

let rec lookup x env = match env with
  | [] -> raise Variable_not_intialized
  | (y, v)::tl -> if x = y then v else lookup x tl

let rec compile exp =
  match exp with
  | Int i -> [INT i]
  | Bool b -> [BOOL b]
  | Var x -> [VAR x]
  | Add (e1, e2) -> compile e1 @ compile e2 @ [ADD]
  | Sub (e1, e2) -> compile e1 @ compile e2 @ [SUB]
  | Mul (e1, e2) -> compile e1 @ compile e2 @ [MUL]
  | Div (e1, e2) -> compile e1 @ compile e2 @ [DIV]
  | Mod (e1, e2) -> compile e1 @ compile e2 @ [MOD]
  | Exp (e1, e2) -> compile e1 @ compile e2 @ [EXP]
  | Absolute e -> compile e @ [ABS]
  | And (e1, e2) -> compile e1 @ compile e2 @ [AND]
  | Or (e1, e2) -> compile e1 @ compile e2 @ [OR]
  | Not e -> compile e @ [NOT]
  | Imp (e1, e2) -> compile e1 @ compile e2 @ [IMP]
  | Equ (e1, e2) -> compile e1 @ compile e2 @ [EQ]
  | GTEqu (e1, e2) -> compile e1 @ compile e2 @ [GTEQ]
  | LTEqu (e1, e2) -> compile e1 @ compile e2 @ [LTEQ]
  | Grt (e1, e2) -> compile e1 @ compile e2 @ [GT]
  | Lst (e1, e2) -> compile e1 @ compile e2 @ [LT]
  | Abs (x, b) -> [CLOS (x, compile b @ [RET])] 
  | App (e1, e2) -> compile e1 @ compile e2 @ [APP]
  | Ifthenelse (e0, e1, e2) -> compile e0 @ [IF (compile e1, compile e2)]
  | LetRec (f, func_body, in_expr) ->
    [LETREC(f, compile func_body)] @ compile in_expr
  | Nil -> []

let rec string_of_opcode = function
  | INT i -> "INT " ^ string_of_int i
  | BOOL b -> "BOOL " ^ string_of_bool b
  | VAR x -> "VAR " ^ x
  | CLOS (x, code) -> "CLOS(" ^ x ^ ", [" ^ String.concat "; " (List.map string_of_opcode code) ^ "])"
  | APP -> "APP"
  | ADD -> "ADD"
  | SUB -> "SUB"
  | MUL -> "MUL"
  | DIV -> "DIV"
  | MOD -> "MOD"
  | EXP -> "EXP"
  | ABS -> "ABS"
  | RET -> "RET"
  | AND -> "AND"
  | OR -> "OR"
  | NOT -> "NOT"
  | IMP -> "IMP"
  | EQ -> "EQ"
  | GT -> "GT"
  | LT -> "LT"
  | GTEQ -> "GTEQ"
  | LTEQ -> "LTEQ"
  | IF (c1, c2) -> "IF([" ^ String.concat "; " (List.map string_of_opcode c1) ^ "], [" ^ 
                   String.concat "; " (List.map string_of_opcode c2) ^ "])"
  | LETREC (f, code) -> "LETREC(" ^ f ^ ", [" ^ String.concat "; " (List.map string_of_opcode code) ^ "])"

let rec secd s e c d = 
  match (s, e, c, d) with
  | (v::_, _, [], []) -> 
    v
  | (s, e, (INT i)::c, d) -> 
    secd (I i :: s) e c d
  | (s, e, (BOOL b)::c, d) -> secd (B b :: s) e c d
  | (s, e, (VAR x)::c, d) -> 
    secd ((lookup x e) :: s) e c d
  | (s, e, (CLOS (x, b))::c, d) -> 
    secd (C (x, b, e) :: s) e c d
  | (s, e, (RET)::c, d) -> 
    (match s, d with 
    | v :: _ , (s', e', c') :: d' -> 
      secd (v :: s') e' c' d'
    | _ -> raise InvalidOperation)
  | (v2 :: v1 :: s, e, APP :: c, d) ->
    (match v1 with
    | C (x, [CLOS(inner_x, inner_b)], env) ->
        let new_env = (x, v2) :: env in
        secd [] new_env inner_b ((s, e, c) :: d)
    | C (x, b, env) -> 
        let new_env = (x, v2) :: env in
        secd [] new_env b ((s, e, c) :: d)
    | _ -> 
        raise InvalidOperation)
  | (v :: s, e, [], (s1, e1, c1)::d) -> 
    secd (v :: s1) e1 c1 d

  (* Arithmetic and logical operations *)
  | (I i2 :: I i1 :: s, e, (ADD)::c, d) -> secd (I (i1 + i2) :: s) e c d
  | (I i2 :: I i1 :: s, e, (SUB)::c, d) -> secd (I (i1 - i2) :: s) e c d
  | (I i2 :: I i1 :: s, e, (MUL)::c, d) -> secd (I (i1 * i2) :: s) e c d
  | (I i2 :: I i1 :: s, e, (DIV)::c, d) -> secd (I (i1 / i2) :: s) e c d
  | (I i2 :: I i1 :: s, e, (MOD)::c, d) -> secd (I (i1 mod i2) :: s) e c d
  | (I i2 :: I i1 :: s, e, (EXP)::c, d) -> secd (I (power i1 i2) :: s) e c d
  | (I i :: s, e, (ABS)::c, d) -> secd (I (abs i) :: s) e c d

  | (B b2 :: B b1 :: s, e, (AND)::c, d) -> secd (B (b1 && b2) :: s) e c d
  | (B b2 :: B b1 :: s, e, (OR)::c, d) -> secd (B (b1 || b2) :: s) e c d
  | (B b2 :: B b1 :: s, e, (IMP)::c, d) -> secd (B (imp_logic b1 b2) :: s) e c d
  | (B b :: s, e, (NOT)::c, d) -> secd (B (not b) :: s) e c d

  (* Comparison operations *)
  | (I i2 :: I i1 :: s, e, (EQ)::c, d) -> secd (B (i1 = i2) :: s) e c d
  | (I i2 :: I i1 :: s, e, (GTEQ)::c, d) -> secd (B (i1 >= i2) :: s) e c d
  | (I i2 :: I i1 :: s, e, (LTEQ)::c, d) -> secd (B (i1 <= i2) :: s) e c d
  | (I i2 :: I i1 :: s, e, (GT)::c, d) -> secd (B (i1 > i2) :: s) e c d
  | (I i2 :: I i1 :: s, e, (LT)::c, d) -> secd (B (i1 < i2) :: s) e c d

  (* Conditional expression *)
  | (B b :: s, e, IF (c1, c2) :: c, d) ->
    let chosen = if b then c1 else c2 in
    secd s e (chosen @ c) d
  | (s, e, (LETREC(f, [CLOS(param, body)]))::c, d) ->
    let rec rec_closure = C(param, body, (f, rec_closure) :: e) in
    secd s ((f, rec_closure) :: e) c d

  | _ -> raise InvalidOperation

let execsecd exp =
  secd [] [] (compile exp) []

(*-----------------------------------------------------------------------------------------------------------------*)
(* Test cases and expected results *)

let print_secd_value = (
  function
  | I i -> Printf.printf "Int: %d\n" i
  | B b -> Printf.printf "Bool: %b\n" b
  | C (x, body, _) ->
    Printf.printf "Closure: param = %s, body = <opcode list of length %d>\n"
      x (List.length body)
  | E e ->
    Printf.printf "Exp: %s\n"
      (match e with
       | Var x -> x
       | _ -> "non-var expression")
)

let safe_print f =(
  try f () with
  | Variable_not_intialized -> print_endline "Error: Variable not initialized"
  | InvalidOperation -> print_endline "Error: Invalid operation"
  | e -> Printf.printf "Unexpected exception: %s\n" (Printexc.to_string e)
)

let rec string_of_exp = (
  function
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
  | GTEqu(e1, e2) -> "(" ^ string_of_exp e1 ^ " ≥ " ^ string_of_exp e2 ^ ")"
  | LTEqu(e1, e2) -> "(" ^ string_of_exp e1 ^ " ≤ " ^ string_of_exp e2 ^ ")"
  | Grt(e1, e2) -> "(" ^ string_of_exp e1 ^ " > " ^ string_of_exp e2 ^ ")"
  | Lst(e1, e2) -> "(" ^ string_of_exp e1 ^ " < " ^ string_of_exp e2 ^ ")"
  | Ifthenelse(e0, e1, e2) -> "if " ^ string_of_exp e0 ^ " then " ^ string_of_exp e1 ^ " else " ^ string_of_exp e2
  | LetRec (f, func_body, in_expr) -> "let rec " ^ f ^ " = " ^ string_of_exp func_body ^ " in " ^ string_of_exp in_expr
  | Nil -> "[]"
)

let id = Abs("x", Var "x")         (* λx.x *)
let test_id = App(id, Int 10)    (* (λx.x) 10 *)

let identity_chain =
  App(
    Abs("x", Var "x"),
    App(
      Abs("y", Var "y"),
      App(
        Abs("z", Var "z"),
        Int 42
      )
    )
  )  (* (λx.x) ((λy.y) ((λz.z) 42)) => 42 *)

let dynamic_apply =
  App(
    App(
      Abs("x", Abs("y", Var "y")),
      Int 3
    ),
    App(Abs("z", Add(Var "z", Int 10)), Int 4)
  ) (* ((λx.λy.y) 3) (λz.z+10) 4 => 4 + 10 = 14 *)

let curried_cmp =
  App(
    App(
      Abs("x", Abs("y", Lst(Var "x", Var "y"))),
      Int 2
    ),
    Int 5
  ) (* ((λx.λy.x<y) 2) 5 => 2 < 5 = true *)

let return_fn =
  App(
    App(
      Abs("x", Abs("y", Var "x")),
      Int 3
    ),
    Abs("z", Add(Var "z", Int 1))
  ) (* ((λx.λy.x) 3) (λz.z+1) => 3 *)

let const = Abs("x", Abs("y", Var "x"))  (* λx.λy.x *)
let test_const = App(App(const, Int 3), Int 99)  (* ((λx.λy.x) 3) 99 => 3 *)

let curried_add = Abs("x", Abs("y", Add(Var "x", Var "y"))) 
let test_curried_add = App(App(curried_add, Int 5), Int 7)  (* 5 + 7 = 12 *)

let y_combinator =
  Abs("f", App(
    Abs("x", App(Var "f", App(Var "x", Var "x"))),
    Abs("x", App(Var "f", App(Var "x", Var "x")))
  ))

let fact_prog = 
  LetRec("fact",
          Abs("n",
              Ifthenelse(
                Equ(Var "n", Int 0),
                Int 1,
                Mul(Var "n", App(Var "fact", Sub(Var "n", Int 1)))
              )
          ),
          App(Var "fact", Int 5)  (* 5! => 120 *)
  )

let fib_prog = 
  LetRec("fib",
          Abs("n",
              Ifthenelse(
                LTEqu(Var "n", Int 1),
                Var "n",
                Add(
                  App(Var "fib", Sub(Var "n", Int 1)),
                  App(Var "fib", Sub(Var "n", Int 2))
                )
              )
          ),
          App(Var "fib", Int 7)
  ) (* Fibonacci of 7 => 13*)

let nested_apply = App(App(Abs("f", Abs("x", App(Var "f", Add(Var "x", Int 1)))), Abs("y", Mul(Var "y", Int 2))), Int 3) (* ((λf.λx.f(x+1))(λy.y*2)) 3 => (λy.y*2)(3+1) => 4*2 = 8 *)

let deeply_nested_lambdas = App(App(App(Abs("x", Abs("y", Abs("z", Add(Mul(Var "x", Var "y"), Var "z")))), Int 2), Int 3), Int 4) (* (((λx.λy.λz.x*y+z) 2) 3) 4 => 2*3+4 = 10 *)

let apply_function_twice = App(App(Abs("f", Abs("x", App(Var "f", App(Var "f", Var "x")))), Abs("z", Add(Var "z", Int 1))), Int 5) (* ((λf.λx.f(f(x))) (λz.z+1)) 5 => (λz.z+1)(5+1) = 6 + 1 = 7 *)

let curried_composition = App(App(App(Abs("f", Abs("g", Abs("x", App(Var "f", App(Var "g", Var "x"))))), Abs("a", Mul(Var "a", Int 2))), Abs("b", Add(Var "b", Int 3))), Int 4) (* ((λf.λg.λx.f(g(x))) (λa.a*2)) (λb.b+3)) 4 => 14 *)

let scoped_variable_nesting = App(Abs("x", App(App(Abs("y", Abs("x", Add(Var "x", Var "y"))), Int 4), Var "x")), Int 6) (* ((λx.λy.x+y) 4) 6 => (λy.4+y) 6 => 4 + 6 = 10 *)

let lambda_let_binding = App(Abs("x", App(Abs("y", Add(Var "x", Var "y")), Int 20)), Int 10) (* ((λx.λy.x+y) 20) 10 => (λy.20+y) 10 => 20 + 10 = 30 *)

let function_returning_function = App(App(Abs("a", Abs("b", Mul(Var "a", Var "b"))), Int 7), Int 6) (* ((λa.λb.a*b) 7) 6 => (λb.7*b) 6 => 7 * 6 = 42 *)

let identity_arithmetic_chain = App(App(Abs("f", Abs("x", App(Var "f", App(Var "f", Var "x")))), Abs("z", Add(Var "z", Int 2))), Int 1) (* ((λf.λx.f(f(x))) (λz.z+2)) 1 => (λz.z+2)(1+2) = 3 + 2 = 5 *)

let pair_simulation_second = App(Abs("p", App(Var "p", Abs("x", Abs("y", Var "y")))), App(App(Abs("x", Abs("y", Abs("f", App(App(Var "f", Var "x"), Var "y")))), Int 9), Int 5)) (* ((λp.p(λx.λy.y)) (λx.λy.λf.f(x)(y))) 9 5 => (λx.λy.λf.f(x)(y))(9)(5) => λf.f(9)(5) => 5 *)

let church_numeral_plus1_twice = App(App(App(Abs("n", Abs("f", Abs("x", App(Var "f", App(App(Var "n", Var "f"), Var "x"))))), Abs("f", Abs("x", App(Var "f", App(Var "f", Var "x"))))), Abs("z", Add(Var "z", Int 1))), Int 0) (* ((λn.λf.λx.f(n(f)(x)))) (λz.z+1)) 0 => 3 *)


(* Test runner *)

let run_tests () =
  print_endline "\nRunning SECD Tests:"; 
  Printf.printf "test_id: ";
  safe_print (fun () -> print_secd_value (execsecd test_id));
  print_endline "Expected: Int 10\n";
  Printf.printf "identity_chain: ";
  safe_print (fun () -> print_secd_value (execsecd identity_chain));
  print_endline "Expected: Int 42\n";
  Printf.printf "dynamic_apply: ";
  safe_print (fun () -> print_secd_value (execsecd dynamic_apply));
  print_endline "Expected: Int 14\n";
  Printf.printf "curried_cmp: ";
  safe_print (fun () -> print_secd_value (execsecd curried_cmp));
  print_endline "Expected: Bool true\n";
  Printf.printf "return_fn: ";
  safe_print (fun () -> print_secd_value (execsecd return_fn));
  print_endline "Expected: Int 3\n";
  Printf.printf "test_const: ";
  safe_print (fun () -> print_secd_value (execsecd test_const));
  print_endline "Expected: Int 3\n";
  Printf.printf "test_curried_add: ";
  safe_print (fun () -> print_secd_value (execsecd test_curried_add));
  print_endline "Expected: Int 12\n";
  Printf.printf "fact_prog: ";
  safe_print (fun () -> print_secd_value (execsecd fact_prog));
  print_endline "Expected: Int 120\n";
  Printf.printf "fib_prog: ";
  safe_print (fun () -> print_secd_value (execsecd fib_prog));
  print_endline "Expected: Int 13\n";
  Printf.printf "nested_apply: ";
  safe_print (fun () -> print_secd_value (execsecd nested_apply));
  print_endline "Expected: Int 8\n";
  Printf.printf "deeply_nested_lambdas: ";
  safe_print (fun () -> print_secd_value (execsecd deeply_nested_lambdas));
  print_endline "Expected: Int 10\n";
  Printf.printf "apply_function_twice: ";
  safe_print (fun () -> print_secd_value (execsecd apply_function_twice));
  print_endline "Expected: Int 7\n";
  Printf.printf "curried_composition: ";
  safe_print (fun () -> print_secd_value (execsecd curried_composition));
  print_endline "Expected: Int 14\n";
  Printf.printf "scoped_variable_nesting: ";
  safe_print (fun () -> print_secd_value (execsecd scoped_variable_nesting));
  print_endline "Expected: Int 10\n";
  Printf.printf "lambda_let_binding: ";
  safe_print (fun () -> print_secd_value (execsecd lambda_let_binding));
  print_endline "Expected: Int 30\n";
  Printf.printf "function_returning_function: ";
  safe_print (fun () -> print_secd_value (execsecd function_returning_function));
  print_endline "Expected: Int 42\n";
  Printf.printf "identity_arithmetic_chain: ";
  safe_print (fun () -> print_secd_value (execsecd identity_arithmetic_chain));
  print_endline "Expected: Int 5\n";
  Printf.printf "pair_simulation_second: ";
  safe_print (fun () -> print_secd_value (execsecd pair_simulation_second));
  print_endline "Expected: Int 5\n";
  Printf.printf "church_numeral_plus1_twice: ";
  safe_print (fun () -> print_secd_value (execsecd church_numeral_plus1_twice));
  print_endline "Expected: Int 3\n";
  

  print_endline "All tests completed."
;;

run_tests ()