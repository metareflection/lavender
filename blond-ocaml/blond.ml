type exp =
  | Const of const
  | Var of var
  | App of applicable * exp list
type value =
  | NumVal of int
  | StringVal of string
  | VarVal of var
  | ListVal of value list
  | FunVal of applicable
type answer =
  | ValAns of value
  | PairAns (* {_|_} *)
type env = (var list * value list) list
type cont = value -> meta-cont -> answer
type meta_cont = (env * cont) list
type re_env =
  | UnitEnv of unit -> value
  | VarEnv of var -> value
  | VarValEnv of var -> value -> value
type lambdaAbs = (value list) -> cont -> meta_cont -> answer
type subr =
  | ThunkSubr of unit -> value
  | UnarySubr of value -> value
  | BinarySubr of value -> value -> value
  | TernarySubr of value -> value -> value -> value
type fsubr = (exp list) -> env -> cont -> meta-cont -> value
type delta_reifier = value -> value -> value -> env -> cont -> meta_cont -> answer
type gamma_reifier = value -> value -> value -> cont -> meta_cont -> answer
type applicable =
  | Abs of lambdaAbs
  | Subr of subr
  | FSubr of fsubr
  | ReifiedEnv of re_env
  | ReifiedCont of cont
  | Delta of delta_reifier
  | Gamma of gamma_reifier

(* reducing primitive functions *)
let _apply_subr (fo : subr) args env cont tau : value =
  match fo, args with
  | ThunkSubr func, [] ->
     cont (func ()) tau
  | UnarySubr func, arg1 :: [] ->
     let cont' = (fun a tau ->
         cont (func a) tau) in
     _eval arg1 env cont' tau
  | BinarySubr func, arg1 :: arg2 :: [] ->
     let cont' = (fun a1 a2 tau2 -> cont (func a1 a2) tau2) in
     let cont'' = (fun a1 tau1 -> _eval arg2 env (cont' a1) tau1) in
     _eval arg1 env cont'' tau
  | TernarySubr func, arg1 :: arg2 :: arg3 :: [] ->
     let cont' = (fun a1 a2 a3 tau ->
         cont (func a1 a2 a3) tau) in
     let cont'' = (fun a1 a2 tau ->
         _eval arg2 env (cont' a1 a2) tau) in
     let cont''' = (fun a1 tau ->
         _eval arg2 env (cont'' a1) tau) in
     _eval arg1 env cont''' tau
  | _,_ -> _wrong '_apply_subr "arity mismatch" args

let _apply_fsubr (fv : fsubr) args env cont tau : value =
  let arity = (_fetch-arity fv) in
  if arity = (List.length args) || arity = 0
  then fv args env cont tau
  else _wrong '_apply_fsubr "arity mismatch" args

let cons_list_val v vlst =
  match vlst with
  | ListVal lst -> ListVal (v :: vlst)
  | _ -> vlst
let _evlis args env cont tau : value =
  match args with
  | [] -> (cont (ListVal []) tau)
  | arg1 :: args_rst ->
     let cont' = (fun v lv tau -> cont (cons_list_val v lv) tau) in
     let cont'' = (fun v tau ->
         (_evlis args_rst env (cont' v) tau)) in
     _eval arg1 env cont'' tau
let _apply_procedure (p : fsubr) args env cont tau : value =
  if (_fetch-arity p) = (List.length args)
  then
    let cont' = (fun lv tau -> p lv k tau) in
    _evlis args env cont' tau
  else _wrong '_apply_procedure "arity mismatch" args
(*
in scheme implementation, reified env somehow is env,
the function turning reified env into env is just the identity function
 *)
let _apply_environment (f : re_env) args env cont tau : value =
  match f, args with
  | UnitEnv func, [] ->
     cont (func ()) tau
  | VarEnv func, arg1 :: [] ->
     let cont' =
       (fun i tau ->
         match i with
         | VarVal var -> cont (_R_lookup var (_env-down f)) tau
         | _ -> _wrong '_apply_environment "not an identifier" i) in
     _eval arg1 env cont' tau
  | VarValEnv func, arg1 :: arg2 :: [] ->
  | _,_ -> _wrong '_apply_environment "arity mismatch" args
let _apply (fo : applicable) args env cont tau =
  match fo with
  | Abs func -> _apply_procedure func args env cont tau
  | Subr func -> _apply_subr func args env cont tau
  | FSubr func -> _apply_fsubr func args env cont tau
  | ReifiedEnv func -> _apply_environment func args env cont tau
  | ReifiedCont func -> _apply_continuation func args env cont tau
  | Delta func -> _apply_delta func args env cont tau
  | Gamma func -> _apply_gamma func args env cont tau
 
let _lookup_common var cont tau =
  match _index var table-common-identifiers with
  | Some pos ->
     cont (_nth pos table-common-values) tau
  | None -> _wrong '_lookup_common "unbound identifier" var
(* 
_access (_nth position (cdar env))
to nth num lst

_index var lst: finds location of var in lst

in scheme implementation, environment has
at least one argument to start with, but by allowing env to be empty
we make it more concise
 *)
let _lookup var env cont tau : value =
  match env with
  | [] -> _lookup_common var cont tau
  | (vars,exps) :: env_rst ->
     let position = _index var vars in
     if position >= 0 then cont (_nth position exps) tau
     else _lookup var env_rst cont tau
let rec _eval (expr : exp) env cont tau = 
  match expr with
  | Const _ -> cont expr tau
  | Var var -> _lookup var env cont tau
  | App fun_exp args ->
     let cont' = (fun f tau ->
         (_apply f args env cont tau)) in
     _eval fun_exp env tau
