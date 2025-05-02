(******************************************************************************)
(***************************** Types ******************************************)
(******************************************************************************)
exception Error of string * string * value (* location, message, cause *)
type var = string

type const =
  | NumConst of int
  | StringConst of string
  | BoolConst of bool

type exp =
  | ConstExp of const
  | VarExp of var
  | ListExp of exp list

type value =
  | ConstVal of const
  | VarVal of var
  | FunVal of applicable
  | ListVal of value list

(* list of hash tables, mapping vars to refernces of vals *)
type local_env = (var * value) list ref
type env = local_env list
type cont = value -> meta_cont -> value
type meta_cont = (env * cont) list

type lambdaAbsBody = (value list) -> cont -> meta_cont -> value
type fsubrBody = (exp list) -> env -> cont -> meta_cont -> value
type lambdaAbs = int * lambdaAbsBody
type subr =
  | ThunkSubr of unit -> value
  | UnarySubr of value -> value
  | BinarySubr of value -> value -> value
  | TernarySubr of value -> value -> value -> value
type fsubr = int * fsubrBody

type delta_reifier = value -> value -> value -> env -> cont -> meta_cont -> value
type gamma_reifier = value -> value -> value -> cont -> meta_cont -> value
type applicable =
  | Abs of lambdaAbs
  | Subr of subr
  | FSubr of fsubr
  | ReifiedEnv of env
  | ReifiedCont of cont
  | Delta of delta_reifier
  | Gamma of gamma_reifier

let rec _exp_up_star (elst : exp list) : value list =
  List.map _exp_up elst
and _exp_up (e : exp) : value =
  match e with
  | ConstExp c -> ConstVal c
  | VarExp var -> VarVal var
  | ListExp elst -> ListVal (_exp_up_star elst)
let _env_up (env : env) : value = FunVal (ReifiedEnv env) 
let _cont_up (cont : cont) : value = FunVal (ReifiedCont cont)

let _exp_down_star (vlst : value list) : exp list =
  List.map _exp_down vlst
and _exp_down v : exp =
  match v with
  | ConstVal c -> Const c
  | VarVar var -> Var var
  | ListVal vlst -> ListExp elst
  | FunVal f -> ListExp [] (* undefined in Scheme impl *)
let _env_down v : env =
  match v with
  | FunVal (ReifiedEnv env) -> env
  | _ -> []
let _cont_down v : cont =
  match v with
  | FunVal (ReifiedCont cont) -> cont
  | _ -> (fun x _ -> x)

(******************************************************************************)
(*************************** Application Dispatches ***************************)
(******************************************************************************)

(******************* Primitive Functions & Special Forms **********************)
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
  | _,_ -> Error ("_apply_subr", "arity mismatch", ListVal args)

let _apply_fsubr (fv : fsubr) args env cont tau : value =
  let (arity,fv) = fv in
  if arity = (List.length args) || arity = 0
  then fv args env cont tau
  else Error ("_apply_fsubr", "arity mismatch", ListVal args)

(******************* Procedures/Lambda Abstractions **********************)
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
let _apply_procedure (p : lambdaAbs) args env cont tau : value =
  if (_fetch_arity p) = (List.length args)
  then
    let cont' = (fun lv tau -> p lv k tau) in
    _evlis args env cont' tau
  else Error ("_apply_procedure", "arity mismatch", ListVal args)

(******************* Applying Environment **********************)
let rec _find_opt (loc_env : (var * value) list) var : value option =
  match loc_env with
  | [] -> None
  | (some_var, some_val) :: loc_env_rst ->
     if var = some_var then Some some_val
     else _find_opt loc_env_rst var
let rec _replace (loc_env : (var * value) list) var value : (var * value) list =
  match loc_env with
  | [] -> []
  | (some_var, some_val) :: loc_env_rst ->
     if var = some_var then (some_var, value) :: loc_env_rst
     else (some_var, some_val) :: (_replace loc_env_rst var value)
let _L_lookup_common var env : (value * local_env) option =
  match env with
  | [] -> None (* undefined in scheme implementation *)
  | tbl :: env_rst ->
     match _find_opt (!table_common) var with
     | None -> None
     | Some com_val ->
        let tbl_val = !tbl in
        tbl := ((var, com_val) :: tbl_val);
        Some (com_val, tbl)
let _L_lookup var env : (value * local_env) option =
  match env with
  | [] -> _L_lookup_common var env
  | tbl :: env_rst ->
     match _find_opt (!tbl) var with
     | Some val_found -> Some (val_found, tbl)
     | None -> _L_lookup var env_rst
let _apply_environment_set (i : value) (v : value) (env_f : value) cont tau : value =
  match i with
  | VarVal var ->
     let env = _env_down env_f in
     (match _L_lookup var env with
      | None -> Error ("_apply_environment", "undefined variable", i)
      | Some (val_found, tbl) ->
         let tbl' = _replace (!tbl) var v in
         tbl := tbl';
         cont v tau) (* in scheme impl we would returned val_found because there's mutability *)
  | _ -> Error ("_apply_environment", "not an identifier", i)

let _R_lookup_common var : value option = _find_opt (!table_common) var

let _R_lookup var env : value option =
  match env with
  | [] -> _R_lookup_common var
  | tbl :: env_rst ->
     match _find_opt (!tbl) var with
     | Some val_found -> Some val_found
     | None -> _R_lookup var env_rst
let local_env_to_value (loc_env : local_env) : value =
  let loc_env_content = !loc_env in
  ListVal (List.map (fun (var,value) -> ListVal [VarVal var, value]) loc_env_content)
let env_to_value env : value =
  ListVal (List.map local_env_to_value env)
let _apply_environment (f : env) args env cont tau : value =
  match args with
  | [] -> cont (env_to_value f) tau
  | arg1 :: [] ->
     let cont' =
       (fun i tau ->
         match i with
         | VarVal var -> cont (_R_lookup var f) tau
         | _ -> Error ("_apply_environment", "not an identifier", i)) in
     _eval arg1 env cont' tau
  | arg1 :: arg2 :: [] ->
     let cont' = (fun var v tau ->
         _apply_environment_set var v f cont tau) in
     let cont'' = (fun var tau ->
         _eval arg2 env (cont' var) tau) in
     _eval arg1 env cont'' tau
  | _ -> Error ("_apply_environment", "arity mismatch", ListVal args)
(******************* Applying Continuations **********************)
let _apply_continuation_jumpy cont_r args env cont tau : value =
  match args with
  | arg1 :: [] ->
     _eval arg1 env (_cont_down cont_r) tau
  | _ -> Error ("_apply_continuation_jumpy", "arity mismatch" args)
let _apply_continuation_pushy cont_r args env cont tau : value =
  match args with
  | arg1 :: [] ->
     _eval arg1 env (_cont_down cont_r) (_meta_push env cont tau)
  | _ -> Error ("_apply_continuation_pushy", "arity mismatch" args)
val _apply_continuation = ref _apply_continuation_jumpy
(******************* Applying Reifiers **********************)

let _apply_delta (d : delta_reifier) args env cont tau =
  d (_exp_up_star args) (_env_up env) (_cont_up cont)
    (_top_env tau) (_top_cont tau) (_meta_pop tau)
let _apply_gamma (g : gamma_reifier) args env cont tau =
  g (_exp_up_star args) (_env_up env) (_cont_up cont)
    (_top_cont tau) (_meta_pop tau)

(******************************************************************************)
(********************* Helpers for Spawning New Levels ************************)
(******************************************************************************)

let _terminate_level (v : value) tau : value =
  (_top-cont tau) v (_meta-pop tau)
let _check_cont_spawn (exp_rfl : exp) (env_rfl : env)
      (cont_rfl : applicable) env cont tau : value =
  match cont_rfl with
  | Subr (UnarySubr func) ->
     let cont' = (fun a tau -> _terminate-level (func a) tau) in
     _eval exp_rfl env_rfl cont' (_meta-push env cont tau)
  | FSubr (1,func) ->
     func [exp_rfl] env_rfl _terminate-level (_meta-push env cont tau)
  | Abs (1,func) ->
     let cont' = (fun a tau ->
         func [a] (_top-cont tau) (_meta-pop tau)) in
     _eval exp_rfl env_rfl cont' (_meta-push env cont tau)
  | ReifiedEnv env_re ->
     let cont' =
       (fun i tau ->
         match i with
         | VarVal var -> _terminate-level (_R_lookup var (_env-down cont_rfl)) tau
         | _ -> Error ("environment", "not an identifier", i)) in
     _eval exp_rfl env_rfl cont' (_meta-push env cont tau)
  | ReifiedCont cont_re ->
     _eval exp_rfl env_rfl (_cont-down cont_re) (_meta-push env cont tau)
  | Delta d ->
     d (_exp-up exp_rfl) (_env-up env_rfl)
       (_cont-up _terminate-level) env cont tau
  | Gamma g ->
     g (_exp-up exp_rfl) (_env-up env_rfl)
       (_cont-up _terminate-level) cont tau
  | Abs _ -> Error ("_meaning", "pitfall lambda abs/proc", cont_rfl) 
  | Subr _ -> Error ("_meaning", "pitfall subr", cont_rfl) 
  | FSubr _ -> Error ("_meaning", "pitfall fsubr", cont_rfl) 
(* a1 has to be expressible to type check*)
let _check_and_spawn (a1 : value) (a2 : value) (a3 : value) env cont tau : value =
  match a2, a3 with
  | FunVal (ReifiedEnv a2_env), FunVal a3_f ->
     _check_cont_spawn (_exp-down a1) a2_env a3_f env cont tau
  | _ -> Error ("_meaning", "polluted environment or pitfall due to not fun", ListVal [a2, a3])
       
let _meaning args env cont tau : value =
  match args with
  | arg1 :: arg2 :: arg3 :: args_rst ->
     let cont' =  (fun a1 a2 a3 tau ->
         _check_and_spawn a1 a2 a3 r k tau) in
     let cont'' = (fun a1 a2 tau -> _eval arg3 env (cont' a1 a2) tau) in
     let cont''' = (fun a1 tau -> _eval arg2 env (cont'' a1) tau) in
     _eval arg1 env cont''' tau
  | _ -> ListVal [] (* undefined in Scheme impl *)
(******************* The Main Apply Function **********************)
let _apply_h (fo : applicable) args env cont tau =
  match fo with
  | Abs func -> _apply_procedure func args env cont tau
  | Subr func -> _apply_subr func args env cont tau
  | FSubr func -> _apply_fsubr func args env cont tau
  | ReifiedEnv func -> _apply_environment func args env cont tau
  | ReifiedCont func -> _apply_continuation func args env cont tau
  | Delta func -> _apply_delta func args env cont tau
  | Gamma func -> _apply_gamma func args env cont tau
let _apply (f_val : value) args env cont tau =
  match f_val with
  | FunVal fo -> _apply_h fo args env cont tau
  | _ -> Error ("_apply", "unapplicable form", fo)

let _lookup_common var cont tau : value =
  match _find_opt (!table_common) var with
  | Some some_val -> cont some_val tau
  | None -> Error ("_lookup_common", "unbound identifier", VarVal var)

let rec _lookup var env cont tau : value =
  match env with
  | [] -> _lookup_common var cont tau
  | env1 :: env_rst ->
     match _find_opt (!env1) var with
     | Some val_found -> cont val_found tau
     | None -> _lookup var env_rst cont tau
          
let rec _eval (expr : exp) env cont tau : value= 
  match expr with
  | VarExp var -> _lookup var env cont tau
  | ConstExp c -> cont (ConstVal c) tau
  | ListExp [] -> cont (ListVal []) tau
  | ListExp (fun_exp :: args) ->
     let cont' = (fun f_val tau ->
         (_apply f_val args env cont tau)) in
     _eval fun_exp env cont' tau
  
     
