module type LavenderLeveLang =
  sig
    type var
    type const
    type exp 
    type value
    type env
    type cont
    
    val eval_func: exp -> env -> cont -> value
    
    val _exp_up: exp -> value
    val _env_up: env -> value
    val _cont_up: cont -> value
    val _eval_func_up: (exp -> env -> cont -> value) -> value
    
    val _exp_down: value -> exp
    val _env_down: value -> env
    val _cont_down: value -> cont
    val _eval_func_down: value -> (exp -> env -> cont -> value)

    val _lookup: var -> env -> cont -> value
    val _lookup_common: var -> cont -> value
  
  end

module LavenderEval =
  functor (Lang: LavenderLeveLang) ->
  struct
    (********************* Types & Related Operations *****************************)
    type var = Lang.var
    type const = Lang.const
    type exp = Lang.exp
    type value = Lang.value
    type env = Lang.env
    type cont = Lang.cont
    
    
    type meta_cont = Tower of (env * cont * eval_func) * (unit -> meta_cont)

    let eval_func = Lang.eval_func
    
    let _top_cont tau =
      match tau with
      | Tower ((_,cont,_), _) -> cont
    let _top_env tau =
      match tau with
      | Tower ((env,_,_), _) -> env
    let _top_eval_func tau =
      match tau with
      | Tower ((_,_,func), _) -> env
    let _meta_pop tau =
      match tau with
      | Tower (_,tau') -> tau' ()
    let _meta_push env cont func tau =
      Tower ((env,cont,func), fun () -> tau)
    let _terminate_level (v : value) tau : value =
      (_top_cont tau) v (_meta_pop tau)

    let table_common = ref []
    let jumpy_cont = ref true

    let rec _eval (expr : exp) env cont func tau : value =
      func expr env cont
  end



and _apply (f_val : value) args env cont tau =
  match f_val with
  | FunVal fo -> _apply_h fo args env cont tau
  | _ -> err cont tau "_apply" "unapplicable form" f_val 
and _apply_h (fo : applicable) args env cont tau =
  match fo with
  | Abs func -> _apply_procedure func args env cont tau
  | Subr func -> _apply_subr func args env cont tau
  | FSubr func -> _apply_fsubr func args env cont tau
  | ReifiedEnv func -> _apply_environment func args env cont tau
  | ReifiedCont func -> _apply_continuation func args env cont tau
  | Delta func -> _apply_delta func args env cont tau
  | Gamma func -> _apply_gamma func args env cont tau
  

(******************************************************************************)
(*************************** Application Dispatches ***************************)
(******************************************************************************)

(******************* Primitive Functions & Special Forms **********************)
(* reducing primitive functions *)
and _apply_subr (fo : subr) args env cont tau : value =
  match fo, args with
  | ThunkSubr func, [] ->
     cont (func ()) tau
  | UnarySubr func, arg1 :: [] ->
     let cont' = (fun a tau ->
         cont (func a) tau) in
     _eval arg1 env cont' tau
  | BinarySubr func, arg1 :: arg2 :: [] ->
     let cont'' = (fun a1 a2 tau2 -> cont (func a1 a2) tau2) in
     let cont' = (fun a1 tau1 -> _eval arg2 env (cont'' a1) tau1) in
     _eval arg1 env cont' tau
  | TernarySubr func, arg1 :: arg2 :: arg3 :: [] ->
     let cont''' = (fun a1 a2 a3 tau ->
         cont (func a1 a2 a3) tau) in
     let cont'' = (fun a1 a2 tau ->
         _eval arg3 env (cont''' a1 a2) tau) in
     let cont' = (fun a1 tau ->
         _eval arg2 env (cont'' a1) tau) in
     _eval arg1 env cont' tau
  | _,_ ->
     err cont tau "_apply_subr" "arity mismatch" (ListVal (_exp_up_star args))

(* this is technically not mutually recursive *)
and _apply_fsubr (fv : fsubr) args env cont tau : value =
  let (arity,fv) = fv in
  if arity = (List.length args) || arity = 0
  then fv args env cont tau
  else
    err cont tau "_apply_fsubr" "arity mismatch" (ListVal (_exp_up_star args))

(******************* Procedures/Lambda Abstractions **********************)

and _evlis args env cont tau : value =
  match args with
  | [] -> (cont (ListVal []) tau)
  | arg1 :: args_rst ->
     let cont'' = (fun v lv tau -> cont (cons_list_val v lv) tau) in
     let cont' = (fun v tau ->
         (_evlis args_rst env (cont'' v) tau)) in
     _eval arg1 env cont' tau
and _apply_procedure (p : lambdaAbs) args env cont tau : value =
  match p with
  | (arity, p_body) ->
     if arity = (List.length args)
     then
       let cont' = (fun val_lst tau ->
           match val_lst with
           | ListVal lv -> p_body lv cont tau
           | _ -> ListVal [] (* impossible case *)) in
       _evlis args env cont' tau
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
and _apply_environment (f : env) args env cont tau : value =
  match args with
  | [] -> cont (env_to_value f) tau
  | arg1 :: [] ->
     let cont' =
       (fun var tau -> _R_lookup_then_cont var f cont tau "_apply_environment") in
     _eval arg1 env cont' tau
  | arg1 :: arg2 :: [] ->
     let cont'' = (fun var v tau ->
         _apply_environment_set var v f cont tau) in
     let cont' = (fun var tau ->
         _eval arg2 env (cont'' var) tau) in
     _eval arg1 env cont' tau
  | _ ->
     err cont tau "_apply_environment" "arity mismatch" (ListVal (_exp_up_star args))
(******************* Applying Continuations **********************)
and _apply_continuation_jumpy cont_r args env (cont : cont) tau : value =
  match args with
  | arg1 :: [] ->
     _eval arg1 env cont_r tau
  | _ -> err cont tau "_apply_continuation_jumpy" "arity mismatch" (ListVal (_exp_up_star args))
and _apply_continuation_pushy cont_r args env cont tau : value =
  match args with
  | arg1 :: [] ->
     _eval arg1 env cont_r (_meta_push env cont tau)
  | _ -> err cont tau "_apply_continuation_pushy" "arity mismatch" (ListVal (_exp_up_star args))
and _apply_continuation cont_r args env cont tau : value =
  if !jumpy_cont then _apply_continuation_jumpy cont_r args env cont tau
  else _apply_continuation_pushy cont_r args env cont tau
(******************* Applying Reifiers **********************)
and _apply_delta (d : delta_reifier) args env cont tau =
  d (ListVal (_exp_up_star args)) (_env_up env) (_cont_up cont)
    (_top_env tau) (_top_cont tau) (_meta_pop tau)
and _apply_gamma (g : gamma_reifier) args env cont tau =
  g (ListVal (_exp_up_star args)) (_env_up env) (_cont_up cont)
    (_top_cont tau) (_meta_pop tau)

(******************************************************************************)
(********************* Helpers for Spawning New Levels ************************)
(******************************************************************************)

      
           
and _check_cont_spawn (exp_rfl : exp) (env_rfl : env)
      (cont_rfl : applicable) env cont tau : value =
  match cont_rfl with
  | Subr (UnarySubr func) ->
     let cont' = (fun a tau -> _terminate_level (func a) tau) in
     _eval exp_rfl env_rfl cont' (_meta_push env cont tau)
  | FSubr (1,func) ->
     func [exp_rfl] env_rfl _terminate_level (_meta_push env cont tau)
  | Abs (1,func) ->
     let cont' = (fun a tau ->
         func [a] (_top_cont tau) (_meta_pop tau)) in
     _eval exp_rfl env_rfl cont' (_meta_push env cont tau)
  | ReifiedEnv env_re ->
     let cont' =
       (fun i tau ->
         _R_lookup_then_cont i env_re _terminate_level tau "environment") in
     _eval exp_rfl env_rfl cont' (_meta_push env cont tau)
  | ReifiedCont cont_re ->
     _eval exp_rfl env_rfl cont_re (_meta_push env cont tau)
  | Delta d ->
     d (_exp_up exp_rfl) (_env_up env_rfl)
       (_cont_up _terminate_level) env cont tau
  | Gamma g ->
     g (_exp_up exp_rfl) (_env_up env_rfl)
       (_cont_up _terminate_level) cont tau
  | Abs _ -> err cont tau "_meaning" "pitfall lambda abs/proc" (FunVal cont_rfl) 
  | Subr _ -> err cont tau "_meaning" "pitfall subr" (FunVal cont_rfl) 
  | FSubr _ -> err cont tau "_meaning" "pitfall fsubr" (FunVal cont_rfl) 
(* a1 has to be expressible to type check*)
and _check_and_spawn (a1 : value) (a2 : value) (a3 : value) env cont tau : value =
  match a2, a3 with
  | FunVal (ReifiedEnv a2_env), FunVal a3_f ->
     _check_cont_spawn (_exp_down a1) a2_env a3_f env cont tau
  | _ -> err cont tau "_meaning" "polluted environment or pitfall due to not fun"
           (ListVal (a2 :: [a3]))
       
and _meaning args env cont tau : value =
  match args with
  | arg1 :: arg2 :: arg3 :: _ ->
     let cont''' =  (fun a1 a2 a3 tau ->
         _check_and_spawn a1 a2 a3 env cont tau) in
     let cont'' = (fun a1 a2 tau -> _eval arg3 env (cont''' a1 a2) tau) in
     let cont' = (fun a1 tau -> _eval arg2 env (cont'' a1) tau) in
     _eval arg1 env cont' tau
  | _ -> undef cont tau "_meaning"

