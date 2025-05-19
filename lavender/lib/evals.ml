open Evaluator
(* a relational layer *)

let var_eq (x1 : var) x2 = x1 = x2

(* supporting key functions *)
let rec occurs var exp (env : (var * value) list) =
  match exp with
  | VarExp var' -> var_eq var var'
  | ConstExp _ -> false
  | ListExp [] -> false
  | ListExp (exp1 :: exps_rst) ->
     if occurs var (find exp1 env) env then true
     else occurs var (ListExp exps_rst) env
  | Meta -> false
and find exp env =
  match exp with
  | VarExp v ->
     (match _find_opt env v with
      | Some val_found -> find (_val_to_exp val_found) env
      | None -> exp)
  | _ -> exp

let empty_subst = []
let subst_update name e env =
  if occurs name e env
  then env
  else (name, _exp_to_val e) :: env
let rec unify exp1 exp2 env =
  match exp1, exp2 with
  | VarExp var1, VarExp var2 ->
     if var_eq var1 var2 then Some env
     else Some (subst_update var1 exp2 env)
  | VarExp var1, _ -> Some (subst_update var1 exp2 env)
  | _, VarExp _ -> unify exp2 exp1 env
  | ListExp (exp1 :: exps_rst1), ListExp (exp2 :: exps_rst2) ->
     let env' = unify (find exp1 env) (find exp2 env) env in
     (match env' with
      | Some x -> unify (find (ListExp exps_rst1) x) (find (ListExp exps_rst2) x) x
      | None -> None)
  | _, _ -> None

(* functions exposed for programmers *)
type state = ((var * value) list) * int

type state_stream =
  | Delayed of (unit -> state_stream)
  | Stream_Head of state * state_stream
  | Empty
type goal = state -> state_stream

let kanren_eq (exp1 : exp) (exp2 : exp) : goal =
  fun (env, counter) ->
  let env' = unify (find exp1 env) (find exp2 env) env in
  match env' with
  | Some sub -> Stream_Head ((sub,counter),Empty)
  | None -> Empty
let call_fresh f : goal =
  fun (env, counter) ->
  f counter (env, 1 + counter)
let init_state = (empty_subst, 0)

let rec stream_app s1 s2 =
  match s1 with
  | Empty -> s2
  | Delayed s1' ->
     Delayed (fun () -> stream_app s2 (s1' ()))
  | Stream_Head (fst, rst) ->
     Stream_Head (fst, (stream_app rst s2))
let kanren_disj (g1 : goal) (g2 : goal) : state -> state_stream =
  fun st ->
  stream_app (g1 st) (g2 st)

let rec stream_app_map (g : goal) (s : state_stream) =
  match s with
  | Empty -> Empty
  | Delayed s' ->
     Delayed (fun () -> stream_app_map g (s' ()))
  | Stream_Head (fst, rst) ->
     stream_app (g fst) (stream_app_map g rst)
let kanren_conj (g1 : goal) (g2 : goal) : state -> state_stream =
  fun st ->
  stream_app_map g2 (g1 st)

(* User interface *)
let rec take n s =
  match s with
  | Empty -> []
  | Stream_Head (fst,rst) ->
     if 1 = n then [fst]
     else fst :: take (n - 1) rst
  | Delayed s' -> 
     take n (s' ())

let is_query _ = true
(* built in evaluator written in OCaml for convenience and testing *)
let rec rel_eval : eval_func =
  fun exp env cont tau ->
  match exp with
  | ListExp ((VarExp "define-relation") :: name :: body) ->
     if is_query body
     then
       let exp' = ListExp (Meta :: (VarExp "define") :: name :: body) in
       _eval exp' env cont rel_eval tau
     else err cont tau "_rel_eval" "not a relation to define" (_exp_to_val exp)  
  | ListExp _ ->
     let val_of_exp = _eval exp env cont default_eval tau in
     if is_query val_of_exp
     then val_of_exp (*run 5 (genfresh "x") val_of_exp*)
     else err cont tau "_rel_eval" "invalid logical expression" (_exp_to_val exp)
  | ConstExp _ -> cont (ListVal []) tau
  | VarExp _ -> cont (ListVal [ConstVal (NumConst 0)]) tau
  | _ -> err cont tau "_rel_eval" "invalid logical expression" (_exp_to_val exp)
 (* | ListExp (pred_exp :: args) ->
     let pred_goal_func = _eval pred_exp env cont rel_eval tau in (* can be just env lookup *)
     let args_goal = _eval args env cont rel_eval tau in (* can be just env lookup *)
     take 5 (pred_goal args env (* or just top of it *))
  *)
          (* just embed kanren like in scheme, so core micro kanren is in env. The main use of fexpr is to isolate out the run interface, so that queries are executed directly rather than inside a run; in some sense we just provide a wrapper.

defining new relations is just a normal define expression, but to make it more convenient
we can put it in the level specific evaluator as a sugar*)

          (*
the expression (query x (some-query))
should give a list of possible values of x, based on the query
running gives a list of answers
*)
