#require "ppx_jane"

(******************************************************************************)
(********************* Types & Related Operations *****************************)
(******************************************************************************)

(********************* Types *****************************)
type var = string

type const =
  | NumConst of int
  | StringConst of string
  | BoolConst of bool
 
type exp =
  | ConstExp of const
  | VarExp of var
  | Meta
  | LeveLang
  | ListExp of exp list  [@@deriving sexp]


type value =
  | ConstVal of const
  | VarVal of var (* logic programming can be supported if vars can appear in env*)
  | FunVal of applicable
  | ListVal of value list
  | Error of string * string * value (* location, message, cause *)

(* list of mutable lists, mapping vars to refernces of vals *)
and local_env = (var * value) list ref
and env = local_env list
and cont = value -> meta_cont -> value
and eval_func = exp -> env -> cont -> meta_cont -> value
and meta_cont = Tower of (env * cont * eval_func) * (eval_func -> meta_cont)

and lambdaAbsBody = (value list) -> cont -> meta_cont -> value
and fsubrBody = (exp list) -> env -> cont -> eval_func -> meta_cont -> value
and lambdaAbs = int * lambdaAbsBody
and subr =
  | ThunkSubr of (unit -> value)
  | UnarySubr of (value -> value)
  | BinarySubr of (value -> value -> value)
  | TernarySubr of (value -> value -> value -> value)
and fsubr = int * fsubrBody
and delta_reifier = value -> value -> value -> value -> env -> cont -> meta_cont -> value
and gamma_reifier = value -> value -> value -> value -> cont -> meta_cont -> value

and applicable =
  | Abs of lambdaAbs
  | Subr of subr
  | FSubr of fsubr
  | ReifiedEnv of env
  | ReifiedCont of cont
  | ReifiedEval of eval_func
  | Delta of delta_reifier
  | Gamma of gamma_reifier


(********************* Operations on These Types *****************************)
(* Adding element to a list val *)
let cons_list_val v vlst =
  match vlst with
  | ListVal lst -> ListVal (v :: lst)
  | _ -> vlst

(* Up and Down Levels *)
let rec _exp_to_val_star (elst : exp list) : value list =
  List.map _exp_to_val elst
and _exp_to_val (e : exp) : value =
  match e with
  | ConstExp c -> ConstVal c
  | VarExp var -> VarVal var
  | ListExp elst -> ListVal (_exp_to_val_star elst)
let _env_to_val (env : env) : value = FunVal (ReifiedEnv env) 
let _cont_to_val (cont : cont) : value = FunVal (ReifiedCont cont)
let _eval_to_val (efun : eval_func) : value = FunVal (ReifiedEval efun)

let _exp_up = _exp_to_val
let _exp_up_star = _exp_to_val_star
let _env_up = _env_to_val
let _cont_up = _cont_to_val
let _eval_up = _eval_to_val

let rec _val_to_exp_star (vlst : value list) : exp list =
  List.map _val_to_exp vlst
and _val_to_exp v : exp =
  match v with
  | ConstVal c -> ConstExp c
  | VarVal var -> VarExp var
  | ListVal vlst -> ListExp (_val_to_exp_star vlst)
  | _ -> ListExp []
let _val_to_env v : env =
  match v with
  | FunVal (ReifiedEnv env) -> env
  | _ -> []
let _val_to_cont v : cont =
  match v with
  | FunVal (ReifiedCont cont) -> cont
  | _ -> (fun x _ -> x)
let _val_to_eval v : eval_func =
  match v with
  | FunVal (ReifiedEval efun) -> efun
  | _ -> (fun e _ _ _ -> _exp_to_val e)

let _exp_down = _val_to_exp
let _exp_down_star = _val_to_exp_star
let _env_down = _val_to_env
let _cont_down = _val_to_cont
let _eval_down = _val_to_eval

(* Operations on environment *)
let rec _find_opt (loc_env : (var * value) list) var : value option =
  match loc_env with
  | [] -> None
  | (some_var, some_val) :: loc_env_rst ->
     if var = some_var
     then Some some_val
     else _find_opt loc_env_rst var
let rec _replace (loc_env : (var * value) list) var value : (var * value) list =
  match loc_env with
  | [] -> []
  | (some_var, some_val) :: loc_env_rst ->
     if var = some_var then (some_var, value) :: loc_env_rst
     else (some_var, some_val) :: (_replace loc_env_rst var value)

(* operations on meta continuation *)
let _top_cont tau =
  match tau with
  | Tower ((_,cont,_), _) -> cont
let _top_env tau =
  match tau with
  | Tower ((env,_,_), _) -> env
let _top_eval tau =
  match tau with
  | Tower ((_,_,efun), _) -> efun

let _meta_pop efun tau : meta_cont =
  match tau with
  | Tower (_,tau') -> tau' efun
(* we can spawn a new level, then redecide what
   language the current level uses when we come back*)
let _meta_push env cont efun tau =
  match tau with
  | Tower ((old_env,old_cont,_), tau') ->
     let new_tau = fun new_f -> Tower ((old_env,old_cont,new_f), tau') in
     Tower ((env,cont,efun), new_tau)

let _terminate_level efun (v : value) tau : value =
  (_top_cont tau) v (_meta_pop efun tau)


(* Errors *)
let error location message value =
  Error (location, message, value)
let err (cont : cont) tau location message value =
  cont (error location message value) tau
(* Undefined Behaviour *)
let undef_err location = error location "Undefined in Scheme Implementation" (ListVal [])
let undef cont tau location =
  err cont tau location "Undefined in Scheme Implementation" (ListVal [])
let undef_impossible cont tau location =
  err cont tau location "Impossible to Reach This Place" (ListVal [])


(*************************** Mutable Values ***************************)
let table_common = ref []
let jumpy_cont = ref true
(******************************************************************************)
(************************* The Main Apply Function ****************************)
(******************************************************************************)
let _lookup_common var cont tau : value =
  let tbl_result = _find_opt (!table_common) var in
  (match tbl_result with
   | Some some_val ->
      cont some_val tau
   | None ->
      err cont tau "_lookup_common" "unbound identifier" (VarVal var))
let rec _lookup var env cont tau : value =
  match env with
  | [] -> _lookup_common var cont tau
  | env1 :: env_rst ->
     match _find_opt (!env1) var with
     | Some val_found -> cont val_found tau
     | None -> _lookup var env_rst cont tau

let rec _eval (expr : exp) env cont efun tau : value =
  match expr with
  | VarExp var ->
     _lookup var env cont tau
  | ConstExp c -> cont (ConstVal c) tau
  | ListExp [] -> cont (ListVal []) tau
  | ListExp (fun_exp :: args) ->
     let cont' = (fun f_val tau ->
         (_apply f_val args env cont efun tau)) in
     _eval fun_exp env cont' efun tau
  | LangExp _ ->
     efun expr env cont tau

and _apply (f_val : value) args env cont efun tau =
  match f_val with
  | FunVal fo -> _apply_h fo args env cont efun tau
  | _ -> err cont tau "_apply" "unapplicable form" f_val 
and _apply_h (fo : applicable) args env cont efun tau =
  match fo with
  | Abs func -> _apply_procedure func args env cont efun tau
  | Subr func -> _apply_subr func args env cont efun tau
  | FSubr func -> _apply_fsubr func args env cont efun tau
  | ReifiedEnv func -> _apply_environment func args env cont efun tau
  | ReifiedCont func -> _apply_continuation func args env cont efun tau
  | ReifiedEval func -> _apply_evaluator func args env cont efun tau
  | Delta func -> _apply_delta func args env cont efun tau
  | Gamma func -> _apply_gamma func args env cont efun tau
  

(******************************************************************************)
(*************************** Application Dispatches ***************************)
(******************************************************************************)

(******************* Primitive Functions & Special Forms **********************)
(* reducing primitive functions *)
and _apply_subr (fo : subr) args env cont efun tau : value =
  match fo, args with
  | ThunkSubr func, [] ->
     cont (func ()) tau
  | UnarySubr func, arg1 :: [] ->
     let cont' = (fun a tau ->
         cont (func a) tau) in
     _eval arg1 env cont' efun tau
  | BinarySubr func, arg1 :: arg2 :: [] ->
     let cont'' = (fun a1 a2 tau2 -> cont (func a1 a2) tau2) in
     let cont' = (fun a1 tau1 -> _eval arg2 env (cont'' a1) efun tau1) in
     _eval arg1 env cont' efun tau
  | TernarySubr func, arg1 :: arg2 :: arg3 :: [] ->
     let cont''' = (fun a1 a2 a3 tau ->
         cont (func a1 a2 a3) tau) in
     let cont'' = (fun a1 a2 tau ->
         _eval arg3 env (cont''' a1 a2) efun tau) in
     let cont' = (fun a1 tau ->
         _eval arg2 env (cont'' a1) efun tau) in
     _eval arg1 env cont' efun tau
  | _,_ ->
     err cont tau "_apply_subr" "arity mismatch" (ListVal (_exp_up_star args))

(* this is technically not mutually recursive *)
and _apply_fsubr (fv : fsubr) args env cont efun tau : value =
  let (arity,fv) = fv in
  if arity = (List.length args) || arity = 0
  then fv args env cont efun tau
  else
    err cont tau "_apply_fsubr" "arity mismatch" (ListVal (_exp_up_star args))

(******************* Procedures/Lambda Abstractions **********************)

and _evlis args env cont efun tau : value =
  match args with
  | [] -> (cont (ListVal []) tau)
  | arg1 :: args_rst ->
     let cont'' = (fun v lv tau -> cont (cons_list_val v lv) tau) in
     let cont' = (fun v tau ->
         (_evlis args_rst env (cont'' v) efun tau)) in
     _eval arg1 env cont' efun tau
and _apply_procedure (p : lambdaAbs) args env cont efun tau : value =
  let (arity, p_body) = p in
  if arity = (List.length args)
  then
    let cont' = (fun val_lst tau ->
        match val_lst with
        | ListVal lv -> p_body lv cont tau
        | _ -> ListVal [] (* impossible case *)) in
    _evlis args env cont' efun tau
  else
    err cont tau "_apply_procedure" "arity mismatch" (ListVal (_exp_up_star args))

(******************* Applying Environment **********************)
(* this section, except for _apply_environment, is technically not mutually recursive *)
and _L_lookup_common var env : (value * local_env) option =
  match env with
  | [] -> None (* undefined in scheme implementation *)
  | tbl :: _ ->
     match _find_opt (!table_common) var with
     | Some com_val ->
        let tbl_val = !tbl in
        tbl := ((var, com_val) :: tbl_val);
        Some (com_val, tbl)
     | None -> None
and _L_lookup var env : (value * local_env) option =
  match env with
  | [] -> _L_lookup_common var env
  | tbl :: env_rst ->
     match _find_opt (!tbl) var with
     | Some val_found -> Some (val_found, tbl)
     | None -> _L_lookup var env_rst

and _apply_environment_set (i : value) (v : value) (env : env) (cont : cont) tau : value =
  match i with
  | VarVal var ->
     (match _L_lookup var env with
      | Some (old_val, tbl) ->
         let tbl' = _replace (!tbl) var v in
         tbl := tbl';
         cont old_val tau
      | None -> (err cont tau "_apply_environment" "undefined variable" i))
  | _ ->
     err cont tau "_apply_environment" "not an identifier" i

and _R_lookup_common var : value option = _find_opt (!table_common) var

and _R_lookup var env : value option =
  match env with
  | [] -> _R_lookup_common var
  | tbl :: env_rst ->
     match _find_opt (!tbl) var with
     | Some val_found -> Some val_found
     | None -> _R_lookup var env_rst
and _R_lookup_then_cont (i : value) (env : env) cont tau place : value =
  match i with
  | VarVal var ->
     (match _R_lookup var env with
      | Some val_fetched -> cont val_fetched tau
      | None -> err cont tau place "undefined variable" i)
  | _ -> err cont tau place "not an identifier" i
and local_env_to_value (loc_env : local_env) : value =
  let loc_env_content = !loc_env in
  ListVal (List.map (fun (var,value) -> ListVal ((VarVal var) :: [value])) loc_env_content)
and env_to_value env : value =
  ListVal (List.map local_env_to_value env)
and _apply_environment (f : env) args env cont efun tau : value =
  match args with
  | [] -> cont (env_to_value f) tau
  | arg1 :: [] ->
     let cont' =
       (fun var tau -> _R_lookup_then_cont var f cont tau "_apply_environment") in
     _eval arg1 env cont' efun tau
  | arg1 :: arg2 :: [] ->
     let cont'' = (fun var v tau ->
         _apply_environment_set var v f cont efun tau) in
     let cont' = (fun var tau ->
         _eval arg2 env (cont'' var) efun tau) in
     _eval arg1 env cont' efun tau
  | _ ->
     err cont tau "_apply_environment" "arity mismatch" (ListVal (_exp_up_star args))
(******************* Applying Continuations **********************)
and _apply_continuation_jumpy cont_r args env (cont : cont) efun tau : value =
  match args with
  | arg1 :: [] ->
     _eval arg1 env cont_r efun tau
  | _ -> err cont tau "_apply_continuation_jumpy" "arity mismatch" (ListVal (_exp_up_star args))
and _apply_continuation_pushy cont_r args env cont efun tau : value =
  match args with
  | arg1 :: [] ->
     _eval arg1 env cont_r efun (_meta_push env cont tau)
  | _ -> err cont tau "_apply_continuation_pushy" "arity mismatch" (ListVal (_exp_up_star args))
and _apply_continuation cont_r args env cont efun tau : value =
  if !jumpy_cont then _apply_continuation_jumpy cont_r args env cont efun tau
  else _apply_continuation_pushy cont_r args env cont efun tau
(******************* Applying Evaluators **********************)
and _apply_evaluator (func : eval_func) args env cont (_ : eval_func) tau : value =
  func (ListExp args) env cont tau
                                                            
(******************* Applying Reifiers **********************)
and _apply_delta (d : delta_reifier) args env cont efun tau =
  match args with
  | [] ->
     d (ListVal []) (_env_up env) (_cont_up cont)
       (_eval_up efun) (_top_env tau) (_top_cont tau) (_meta_pop (make_init_eval ()) tau)
  | lang :: args_rst ->
     match _eval lang env cont efun tau with
     | FunVal (ReifiedEval lang_eval) ->
        d (ListVal (_exp_up_star args_rst)) (_env_up env) (_cont_up cont)
          (_eval_up efun) (_top_env tau) (_top_cont tau) (_meta_pop lang_eval tau)
     | _ ->
        d (ListVal (_exp_up_star args)) (_env_up env) (_cont_up cont)
          (_eval_up efun) (_top_env tau) (_top_cont tau) (_meta_pop (make_init_eval ()) tau)
and _apply_gamma (g : gamma_reifier) args env cont efun tau =
  match args with
  | [] ->
     g (ListVal []) (_env_up env) (_cont_up cont)
       (_eval_up efun) (_top_cont tau) (_meta_pop (make_init_eval ()) tau)
  | lang :: args_rst ->
     match _eval lang env cont efun tau with
     | FunVal (ReifiedEval lang_eval) ->
        g (ListVal (_exp_up_star args_rst)) (_env_up env) (_cont_up cont)
          (_eval_up efun) (_top_cont tau) (_meta_pop lang_eval tau)
     | _ ->
        g (ListVal (_exp_up_star args)) (_env_up env) (_cont_up cont)
          (_eval_up efun) (_top_cont tau) (_meta_pop (make_init_eval ()) tau)
