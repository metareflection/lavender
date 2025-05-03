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
                       (_top-env stau)) cont' tau) in
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
               
let fsubr_table_0_h =
  [_case,
   _and,
   _or,
   _begin,
   _read
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
  ]
let fsubr_table_3_h =
  [_if
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
        (_inFsubr 0 _openloop)
        (_inFsubr 3 _extend-reified-environment)
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
