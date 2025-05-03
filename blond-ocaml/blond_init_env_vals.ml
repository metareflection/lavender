open Blond
(*
type applicable =
  | Abs of lambdaAbs
  | Subr of subr
  | FSubr of fsubr
  | ReifiedEnv of env
  | ReifiedCont of cont
  | Delta of delta_reifier
  | Gamma of gamma_reifier
 *)

(********************* some helpers ***********************************)
let make_init_env =
  fun () -> _extend_env [] [] []
let zip_lst lst1 lst2 =
  match lst1, lst2 with
  | [], [] -> []
  | name1 :: lst1_rst, val1 :: lst2_rst ->
     (name1,val1) :: zip_lst lst1_rst lst2_rst
let _extend_env paras vals env =
  (zip_lst paras vals) :: env
let blond_banner =
  ConstVal (StringConst "starting-up")
(**************** Build in Functions of Blond in Common Environment **************)
let _quote : fsubrBody =
  fun args env cont tau ->
  cont (List.fst args) tau

let _if : fsubrBody =
  fun args env cont tau ->
  match args with
  | arg :: arg_t :: arg_f :: [] ->
     let cont' = (fun bval tau ->
         match bval with
         | ConstVal (BoolConst b) ->
            if b then _eval arg_t env cont tau
            else _eval arg_f env cont tau
         | ListVal [] -> _eval arg_f env cont tau
         | _ -> _eval arg_t env cont tau) in
     _eval arg env cont' tau
  | _ -> ListVal [] (* undefined case *)

let _lambda : fsubrBody =
  fun args env cont tau ->
  match args with
  | (ListExp paras) :: body :: [] ->
     let bd = (fun val_lst cont tau ->
         _eval body (_extend_env paras val_lst env) cont tau) in
     let lbd = FunVal (Abs (List.length paras,bd)) in
     cont lbd tau
  | _ -> ListVal [] (* undefined *)
let _delta : fsubrBody =
  fun args env cont tau ->
  match args with
  | (ListExp [para_exp, para_env, para_cont]) :: body :: [] ->
     let paras = [para_exp, para_env, para_cont] in
     let d = (fun val_exp val_env val_cont env' cont' tau ->
         _eval body (_extend_env paras [val_exp, val_env, val_cont] env') cont' tau) in
     let dt = FunVal (Delta d) in
     cont dt tau
  | _ -> Error ("_delta", "wrong para shape", (List.fst args))
let _gamma : fsubrBody =
  fun args env cont stau ->
  match args with
  | (ListExp [para_exp, para_env, para_cont]) :: body :: [] ->
     let paras = [para_exp, para_env, para_cont] in
     let d = (fun val_exp val_env val_cont cont' tau ->
         _eval body (_extend_env paras [val_exp, val_env, val_cont]
                       (_top_env stau)) cont' tau) in
     let dt = FunVal (Delta d) in
     cont dt stau
  | _ -> Error ("_gamma", "wrong para shape", (List.fst args))
let _update_env (var : var) (value : value) (env : local_env) =
  let tbl = !env in
  let new_tbl = 
    match _find_opt tbl var with
    | None -> (var, value) :: tbl
    | Some some_val -> 
       _replace tbl var value in
  env := new_tbl
let _common_define : fsubrBody =
  fun args env cont tau ->
  match args with
  | (VarExp name) :: body :: [] ->
     let cont' = (fun a tau ->
         _update_env name a table_common;
         cont (VarVal name) tau) in
     _eval body env cont' tau
  | _ -> Error ("_common_define", "undefineable", (List.fst args))
let _define : fsubrBody =
  fun args env cont tau ->
  match args, env with
  | (VarExp name) :: body :: [], global_env :: _ ->
     let cont' = (fun a tau ->
         _update_env name a global_env;
         cont (VarVal name) tau) in
     _eval body env cont' tau
  | _, _ -> Error ("_define", "undefineable", (List.fst args))

let _L_set_h var new_val env1 env_rst cont tau =
  let env_cur_lv = !env1 in
  ifOption (_find_opt env_cur_lv var)
    (fun old_val ->
      env1 := _replace env_cur_lv var new_val;
      cont old_val tau)
    match env_rst with
    | [] ->
       ifOption (_find_opt table_common var)
         (fun com_val ->
           env1 := (var, new_val) :: env_cur_lv;
           cont com_val tau)
         (Error ("_L_set", "undefineable variable", VarVal var))
    | env1' :: env_rst' -> _L_set_h var new_val env1' env_rst' cont tau
let _L_set var new_val env cont tau =
  match env with
  | env1 :: env_rst ->
     _L_set_h var new_val env1 env_rst cont tau

let _set : fsubrBody =
  fun args env cont tau ->
  match args with
  | (VarExp name) :: body :: [] ->
     let cont' = (fun a tau ->
         _L_set name a env cont tau) in
     _eval body env cont' tau
  | _ -> Error ("_set", "undefineable", (List.fst args))

let _ef : subr =
  TernarySubr
    (fun p at af ->
      match p with
      | ConstVal (BoolConst pred) ->
         if pred then at else af
      | ListVal [] -> af
      | _ -> at)
let rec val_member_exp_lst v elst =
  match elst with
  | [] -> false
  | e1 :: elst_rst ->
     if v = (_exp_to_val e) then true
     else val_member_exp_lst v elst_rst 
let val_member_or_eq_exp v e =
  if v = (_exp_to_val e) then true
  else
    match e with
    | ListExp elst -> val_member_exp_lst v elst
    | _ -> false
let rec _case_loop val_pred args env cont tau =
  match args with
  | [] -> Error ("_case_loop", "unmatched", a)
  | ListExp (case1_form :: [case1_body]) :: cases_rst ->
     if case1_form = ConstExp (StringConst "else")
     then _eval case1_body env cont tau
     else
       if val_member_or_eq_exp a cases1_form in
       then _eval case1_body env cont tau
       else _case_loop val_pred cases_rst env cont tau
let _case : fsubrBody =
  fun args env cont tau ->
  match args with
  | pred :: args_rst ->
     _eval pred env (fun a tau ->
         _case_loop a args_rst env cont tau) tau
let rec _and_loop args env cont tau =
  match args with
  | pred :: [] -> _eval pred env cont tau
  | pred1 :: preds_rst ->
     let cont' = (fun a tau ->
         if a = ListVal [] || a = ConstVal (BoolConst false)
         then cont false tau
         else _and_loop preds_rst env cont tau) in
     _eval pred1 env cont' tau
let _and : fsubrBody =
  fun args env cont tau ->
  match args with
  | [] -> cont (ConstVal (BoolConst true)) tau 
  | args_rst ->
     _and_loop args env cont tau
let rec _or_loop args env cont tau =
  match args with
  | pred :: [] -> _eval pred env cont tau
  | pred1 :: preds_rst ->
     let cont' = (fun a tau ->
         if a = ListVal [] || a = ConstVal (BoolConst false)
         then _or_loop preds_rst env cont tau
         else cont a tau) in
     _eval pred1 env cont' tau
let _or : fsubrBody =
  fun args env cont tau ->
  match args with
  | [] -> cont (ConstVal (BoolConst false)) tau 
  | args_rst ->
     _or_loop args env cont tau

let rec _begin : fsubrBody =
  fun args env cont tau ->
  match args with
  | stmt :: [] -> _eval stmt env cont tau
  | stmt1 :: stmts_rst ->
     let cont' = (fun a tau -> _begin stmts_rst env cont tau) in
     _eval stmt1 env cont' tau

let rec read_file_as_str_h channel content =
  try
    let line = input_line channel in
    read_file_as_str_h channel (String.concat line content)
  with End_of_file ->
        close_in channel;
        content
let read_file_as_str channel = read_file_as_str_h channel ""
let _read_file (file_name : value) =
  match file_name with
  | VarVal name ->
     let in_channel = open_in name in
     read_file_as_str in_channel
let _read : fsubrBody =
  fun args env cont tau ->
  match args with
  | [] ->
     let ln = read_line () in
     cont ln tau
  | file :: [] ->
     let cont' = (fun file_name tau ->
         cont (_read_file file_name) tau) in
     _eval file env cont' tau
  | _ -> Error ("_read", "arity mismatch", ListVal (_exp_to_val args))
let _gen_metalevel new_level new_lv_env env cont tau =
  let new_level_cont = _gen_toplv_cont new_level new_lv_env in
  new_level_cont blond_banner (_meta_push env cont tau)
let _openloop : fsubrBody =
  fun args env cont tau ->
  match args with
  | arg1 :: [] ->
     let cont' = (fun new_level tau ->
         _gen_metalevel new_level (make_init_env ()) env cont tau) in
     _eval arg1 env cont' tau
  | arg1 :: arg2 :: [] ->
     let cont'' = (fun new_env_val tau ->
         match new_env with
         | FunVal (ReifiedEnv new_env) ->
            _gen_metalevel new_level new_env env cont tau
         | -> Error ("_openloop", "not a reified environment", new_env_val)) in
     let cont' = (fun new_level tau -> _eval arg2 env cont'' tau) in
     _eval arg1 env cont' tau
  | _ -> Error ("_openloop", "wrong arity", ListVal (_exp_to_val args))

let _extend lsvar lsval env_re cont tau =
  match lsvar, lsval, env_re with
  | (ListVal var_lst), (ListVal val_lst), (FunVal (ReifiedEnv env)) ->
     if List.length var_lst = List.length val_lst
     then cont (_env_up (_extend_env var_lst val_lst env)) tau
     else Error ("_extend_reified_env", "var list and val list length mismatch",
                 ListVal (lsvar :: [lsval]))
  | _ -> Error ("_extend_reified_env", "not a vars, vals, env triple",
                ListVal (lsvar :: lsval :: [env_re]))
let _extend_reified_env : fsubrBody =
  fun args env cont tau ->
  match args with
  | var_lst :: val_lst :: env_re :: [] ->
     let cont''' = (fun a1 a2 a3 tau ->
         _extend a1 a2 a3 cont tau) in
     let cont'' = (fun a1 a2 tau ->
         _eval env_re env (cont''' a1 a2) tau) in
     let cont' = (fun a1 tau ->
         _eval val_lst env (cont'' a1) tau) in
     _eval var_lst env tau
let _let_idlis bindings =
  match bindings with
  | [] -> []
  | (ListVal (name :: _)) :: rst_bds ->
     name :: _let_idlis rst_bds
let _let_evlis bindings env cont tau =
  match bindings with
  | (ListVal (_ :: [body1])) :: rst_bds ->
     let cont' = (fun v tau ->
         match rst_bds with
         | [] -> cont (ListVal [v]) tau
         | _ ->
            _let_evlis rst_bds env
              (fun lv tau -> cont (cons_lst_val v lv) tau)
              tau) in
     _eval body1 env cont' tau
let _let : fsubrBody =
  fun args env cont tau ->
  match args with
  | (ListVal []) :: body :: [] ->
     _eval body env cont tau
  | bindings :: body :: [] ->
     let cont' = (fun vals tau ->
         _eval body (_extend_env (_let_idlis bindings) vals env) cont tau) in
     _let_evlis bindings env cont' tau
let rec one_env_update_vals env vals =
  match env, vals with
  | (var,value) :: env_rst, new_val :: vals_rst ->
     (var,new_val) :: (one_env_update_vals env_rst vals_rst)
let env_update_vals env vals =
  match env, vals with
  | env1 :: _, ListVal val_lst ->
     let env1_content = !env1 in
     let env1_new_content = one_env_update_vals env val_lst in
     env1 := env1_new_content
let _letrec : fsubrBody =
  fun args env cont tau ->
  match args with
  | (ListVal []) :: body :: [] ->
     _eval body env cont tau
  | bindings :: body :: [] ->
     let env = _extend_env (_let_idlis bindings) [] env in
     let cont' = (fun vals tau ->
         env_update_vals env vals;
         _eval body env cont tau) in
     _let_evlis bindings env cont' tau
let _rec : fsubrBody =
  fun args env cont tau ->
  match args with
  | bindings :: body :: [] ->
     let env = _extend_env [bindings] [] env in
     let cont' = (fun a tau ->
         env_update_vals env (ListVal [a]);
         cont a tau) in
     _eval body env cont' tau
let rec _let_star_evlis bindings body env cont tau =
  match bindings with
  | [] -> _eval body env cont tau
  | (ListVal (VarVal name1 :: [body1])) :: rst_bds ->
     let cont' = (fun a tau ->
         _let*_evlis rst_bds body
                (_extend_env [name1] [a] env)
                cont tau) in
     _eval body1 env tau
let _let_star : fsubrBody =
  fun args env cont tau ->
  match args with
  | bindings :: body :: [] ->
     _let_star_evlis bindings body env cont tau
let rec _case_loop val_pred args env cont tau =
  match args with
  | [] -> Error ("_case_loop", "unmatched", a)
  | ListExp (case1_form :: [case1_body]) :: cases_rst ->
     if case1_form = ConstExp (StringConst "else")
     then _eval case1_body env cont tau
     else
       if val_member_or_eq_exp a cases1_form in
       then _eval case1_body env cont tau
       else _case_loop val_pred cases_rst env cont tau
let _cond : fsubrBody =
  fun args env cont tau ->
  match args with
  | [] -> cont (ConstVal (StringConst "unmatched cond")) tau
  | (ListExp (cond1 :: [body1])) :: conds_rst ->
     match cond1 with
     | ConstExp (StringConst "else") ->
        _eval body1 env cont tau
     | _ ->
        let cont' = (fun a tau ->
            match a with
            | ConstVal (BoolConst false) ->
               _cond conds_rst env cont tau
            | ListVal [] ->
               _cond conds_rst env cont tau
            | _ -> _eval body1 env cont tau) in
        _eval cond1 env cont' tau
let _reify_new_cont : fsubrBody =
  fun args env cont tau ->
  match args with
  | arg1 :: [] ->
     let cont' = (fun level tau ->
         let new_cont = _gen_toplv_cont level (make_init_env ()) in
         cont (_cont_up new_cont) tau) in
     _eval arg1 env cont' tau
  | arg1 :: arg2 :: [] ->
     let cont'' = (fun env_re tau ->
         match env_re with
         | FunVal (ReifiedEnv env_r) ->
            cont (_cont_up (_gen_toplv_cont level env_r)) tau
         | _ -> Error ("_reify_new_cont",
                       "not a reified environment",
                       env_re)) in
     let cont' = (fun level tau ->
         _eval arg2 env cont'' tau) in
     _eval arg1 env cont' tau
  | _ -> Error ("_reify_new_cont", "arity mismatch",
                ListVal (_exp_to_val args))
let _reify_new_env : subr =
 ThunkSubr
   (fun () ->
     _env_up (make_init_env ()))
let _cont_mode : subr =
 ThunkSubr
   (fun () ->
     if !jumpy_cont then ConstVal (StringConst "jumpy")
     else ConstVal (StringConst "pushy"))
let _switch_cont_mode : subr =
 ThunkSubr
   (fun () ->
     if !jumpy_cont
     then
       (jumpy_cont := false;
        ConstVal (StringConst "set to pushy"))
     else
       (jumpy_cont := true;
        ConstVal (StringConst "set to jumpy")))
let _blond_exit : fsubrBody =
  fun args env cont tau ->
  ConstVal (StringConst "farvel!")

let fsubr_table_0_h =
  [_case,
   _and,
   _or,
   _begin,
   _read,
   _openloop,
   _cond,
   _blond_exit
  ]
let fsubr_table_1_h =
  [_quote,
  ]
let fsubr_table_2_h =
  [_lambda,
   _delta,
   _gamma,
   _common_define,
   _define,
   _set,
   _let,
   _letrec,
   _rec,
   _let_star,
  ]
let fsubr_table_3_h =
  [_if,
   _extend_reified_env
  ]
let fsubr_table_0 = List.map (fun x -> 0,x) fsubr_table_0_h
let fsubr_table_1 = List.map (fun x -> 1,x) fsubr_table_1_h
let fsubr_table_2 = List.map (fun x -> 2,x) fsubr_table_2_h
let fsubr_table_3 = List.map (fun x -> 3,x) fsubr_table_3_h
let fsubr_table_h =
  List.append fsubr_table_0
    (List.append fsubr_table_1
       (List.append fsubr_table_2 fsubr_table_3))

let subr_table_3_h =
  [_ef
  ]
let subr_table = List.map Subr subr_table_h
let fsubr_table = List.map FSubr fsubr_table_h
(*********)    
    (_inSubr 1 car) (_inSubr 1 cdr)
        (_inSubr 1 caar) (_inSubr 1 cadr)
        (_inSubr 1 cdar) (_inSubr 1 cddr)
        (_inSubr 1 caddr) (_inSubr 1 cdddr)
        (_inSubr 1 last-pair)
        (_inSubr 1 null?) (_inSubr 1 atom?) (_inSubr 1 pair?)
        (_inSubr 1 number?) (_inSubr 1 string?) (_inSubr 1 symbol?)
        (_inSubr 1 zero?) (_inSubr 1 add1) (_inSubr 1 sub1)
        (_inSubr 2 +) (_inSubr 2 -) (_inSubr 2 *)
        (_inSubr 2 <) (_inSubr 2 <=) (_inSubr 2 >) (_inSubr 2 >=)
        (_inSubr 2 cons) (_inSubr 2 equal?)
        (_inSubr 2 =) (_inSubr 1 boolean?)
        (_inSubr 1 negative?) (_inSubr 1 positive?)
        (_inSubr 1 _applicable?)

                         (_inFsubr 3 _meaning) 
         (_inSubr 3 _ef)
        
        (_inFsubr 0 _case)
        (_inFsubr 0 _and) (_inFsubr 0 _or)
        (_inFsubr 0 _evlis)
        (_inSubr 2 set-car!) (_inSubr 2 set-cdr!)
        (_inFsubr 0 _begin)
        (_inSubr 1 display) (_inSubr 1 pretty-print)
        (_inSubr 1 pretty-print) (_inSubr 0 newline)
        (_inSubr 1 not) (_inSubr 1 length)
        (_inFsubr 1 _load) (_inFsubr 1 _mute-load) (_inFsubr 0 _read)
        (_inSubr 1 open-input-file) (_inSubr 1 eof-object?)
        (_inSubr 1 close-input-port)
        (_inSubr 0 flush-output-port)
        (_inFsubr 2 _let) (_inFsubr 2 _letrec)
        (_inFsubr 2 _rec) (_inFsubr 2 _let*)
        (_inFsubr 0 _cond)
        (_inFsubr 0 _blond-exit)
        (_inSubr 0 _reify-new-environment)
        (_inFsubr 0 _reify-new-continuation)
        (_inSubr 0 _continuation-mode)
        (_inSubr 0 _switch-continuation-mode)

(******************************************************************************)
(***************************** Types ******************************************)
(******************************************************************************)
