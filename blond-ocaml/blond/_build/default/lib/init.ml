open Evaluator

(********************* some helpers ***********************************)
let val_to_var v =
  match v with
  | VarVal var -> var
  | _ -> "(Not a Var)"
let exp_to_var e =
  match e with
  | VarExp var -> var
  | _ -> "(Not a Var)"

let rec zip_lst lst1 lst2 =
  match lst1, lst2 with
  | [], [] -> []
  | name1 :: lst1_rst, val1 :: lst2_rst ->
     (name1,val1) :: zip_lst lst1_rst lst2_rst
  | _ -> []

let _extend_env paras vals (env : env) : env =
  (ref (zip_lst paras vals)) :: env

let make_init_env =
  fun () -> _extend_env [] [] []

let parse (s : string) : exp =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast
let read_inp_exp : unit -> exp =
  fun () ->
  let ln = read_line () in
  parse ln


let blond_banner =
  ConstVal (StringConst "starting-up")
(***************************************************************************************)
(***************** Built in Special Forms of Blond in Common Environment ***************)
(***************************************************************************************)
let _quote : fsubrBody =
  fun args _ cont tau ->
  match args with
  | arg1 :: _ ->
     cont (_exp_to_val arg1) tau
  | _ -> undef "_quote"
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
  | _ -> undef "_if"

let _lambda : fsubrBody =
  fun args env cont tau ->
  match args with
  | (ListExp paras) :: body :: [] ->
     let para_vars = List.map exp_to_var paras in
     let bd = (fun val_lst cont tau ->
         _eval body (_extend_env para_vars val_lst env) cont tau) in
     let lbd = FunVal (Abs (List.length paras,bd)) in
     cont lbd tau
  | _ -> undef "_lambda"
let _delta : fsubrBody =
  fun args _ cont tau ->
  match args with
  | (ListExp (para_exp :: para_env :: [para_cont])) :: body :: [] ->
     let paras = para_exp :: para_env :: [para_cont] in
     let para_vars = List.map exp_to_var paras in
     let d = (fun val_exp val_env val_cont env' cont' tau ->
         _eval body (_extend_env para_vars (val_exp :: val_env :: [val_cont]) env') cont' tau) in
     let dt = FunVal (Delta d) in
     cont dt tau
  | arg :: _ -> Error ("_delta", "wrong para shape", (_exp_to_val arg))
  | _ -> undef "_delta"
let _gamma : fsubrBody =
  fun args _ cont stau ->
  match args with
  | (ListExp (para_exp :: para_env :: [para_cont])) :: body :: [] ->
     let paras = para_exp :: para_env :: [para_cont] in
     let para_vars = List.map exp_to_var paras in
     let g = (fun val_exp val_env val_cont cont' tau ->
         _eval body (_extend_env para_vars (val_exp :: val_env :: [val_cont])
                       (_top_env stau)) cont' tau) in
     let gm = FunVal (Gamma g) in
     cont gm stau
  | arg :: _ -> Error ("_gamma", "wrong para shape", (_exp_to_val arg))
  | _ -> undef "_gamma"
let _update_env (var : var) (value : value) (env : local_env) =
  let tbl = !env in
  let new_tbl = 
    match _find_opt tbl var with
    | None -> (var, value) :: tbl
    | Some _ -> 
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
  | arg :: _ -> Error ("_common_define", "undefineable", (_exp_to_val arg))
  | _ -> undef "_common_define"
let _define : fsubrBody =
  fun args env cont tau ->
  match args, env with
  | (VarExp name) :: body :: [], global_env :: _ ->
     let cont' = (fun a tau ->
         _update_env name a global_env;
         cont (VarVal name) tau) in
     _eval body env cont' tau
  | arg :: _, _ -> Error ("_define", "undefineable", (_exp_to_val arg))
  | _,_ -> undef "_define"
let rec _L_set_h var new_val env1 env_rst cont tau =
  let env_cur_lv = !env1 in
  ifOption (_find_opt env_cur_lv var)
    (fun old_val ->
      env1 := _replace env_cur_lv var new_val;
      cont old_val tau)
    (match env_rst with
     | [] ->
        ifOption (_find_opt (!table_common) var)
          (fun com_val ->
            env1 := (var, new_val) :: env_cur_lv;
            cont com_val tau)
          (Error ("_L_set", "undefineable variable", VarVal var))
     | env1' :: env_rst' -> _L_set_h var new_val env1' env_rst' cont tau)
let _L_set var new_val env cont tau =
  match env with
  | env1 :: env_rst ->
     _L_set_h var new_val env1 env_rst cont tau
  | _ -> undef "_L_set"
let _set : fsubrBody =
  fun args env cont tau ->
  match args with
  | (VarExp name) :: body :: [] ->
     let cont' = (fun a tau ->
         _L_set name a env cont tau) in
     _eval body env cont' tau
  | arg :: _ -> Error ("_set", "undefineable", (_exp_to_val arg))
  | _ -> undef "_set"
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
     if v = (_exp_to_val e1) then true
     else val_member_exp_lst v elst_rst 
let val_member_or_eq_exp v e =
  if v = (_exp_to_val e) then true
  else
    match e with
    | ListExp elst -> val_member_exp_lst v elst
    | _ -> false
let rec _case_loop val_pred args env cont tau =
  match args with
  | [] -> Error ("_case_loop", "unmatched", val_pred)
  | ListExp (case1_form :: [case1_body]) :: cases_rst ->
     if case1_form = ConstExp (StringConst "else")
     then _eval case1_body env cont tau
     else
       if val_member_or_eq_exp val_pred case1_form
       then _eval case1_body env cont tau
       else _case_loop val_pred cases_rst env cont tau
  | _ -> undef "_case_loop"
let _case : fsubrBody =
  fun args env cont tau ->
  match args with
  | pred :: args_rst ->
     _eval pred env (fun a tau ->
         _case_loop a args_rst env cont tau) tau
  | _ -> undef "_case"
let rec _and_loop args env cont tau =
  match args with
  | pred :: [] -> _eval pred env cont tau
  | pred1 :: preds_rst ->
     let cont' = (fun a tau ->
         if a = ListVal [] || a = ConstVal (BoolConst false)
         then cont (ConstVal (BoolConst false)) tau
         else _and_loop preds_rst env cont tau) in
     _eval pred1 env cont' tau
  | _ -> undef "_and_loop"
let _and : fsubrBody =
  fun args env cont tau ->
  match args with
  | [] -> cont (ConstVal (BoolConst true)) tau 
  | _ :: _ ->
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
  | _ -> undef "_or_loop"
let _or : fsubrBody =
  fun args env cont tau ->
  match args with
  | [] -> cont (ConstVal (BoolConst false)) tau 
  | _ :: _ ->
     _or_loop args env cont tau

let rec _begin : fsubrBody =
  fun args env cont tau ->
  match args with
  | stmt :: [] -> _eval stmt env cont tau
  | stmt1 :: stmts_rst ->
     let cont' = (fun _ tau -> _begin stmts_rst env cont tau) in
     _eval stmt1 env cont' tau
  | _ -> undef "_begin"

let rec read_file_as_str_h channel (content : string) =
  try
    let line = input_line channel in
    read_file_as_str_h channel (line ^ content)
  with End_of_file ->
        close_in channel;
        content
let read_file_as_str channel = read_file_as_str_h channel ""
let _read_file (file_name : value) =
  match file_name with
  | VarVal name ->
     let in_channel = open_in name in
     read_file_as_str in_channel
  | _ -> "File Names Must Be Strings!"

let _read : fsubrBody =
  fun args env cont tau ->
  match args with
  | [] ->
     let ln = read_inp_exp () in
     cont (_exp_to_val ln) tau
  | file :: [] ->
     let cont' = (fun file_name tau ->
         let content = _read_file file_name in
         cont (ConstVal (StringConst content)) tau) in
     _eval file env cont' tau
  | _ -> Error ("_read", "arity mismatch", ListVal (_exp_to_val_star args))

let _show_const c : string =
  match c with
  | NumConst i -> string_of_int i
  | StringConst str -> str
  | BoolConst true -> "true"
  | BoolConst false -> "false"
let rec _show_value value : string =
  match value with
  | ConstVal c -> _show_const c
  | VarVal var -> var
  | FunVal _ -> "An Applicable"
  | ListVal vlst ->
     let str_lst = List.map _show_value vlst in
     "[" ^
       (String.concat ", " str_lst) ^
         "]"
  | Error (str1, str2, v) ->
     "Blond Error: " ^ str1 ^ " " ^ str2 ^
       (_show_value v)
let next_iter iteration = 1 + iteration
let _print (level : int) (iteration : int) (value : value) =
  print_int level;
  print_string "-";
  print_int iteration;
  print_string ":";
  print_string (_show_value value);
  print_newline ();
  print_int level;
  print_string "-";
  print_int (next_iter iteration);
  print_string ">"

let first_iteration = 0
let _gen_toplv_cont my_lv my_env : cont =
  let rec elementary_loop iteration =
    fun value tau ->
    _print my_lv iteration value;
    _eval (read_inp_exp ()) my_env (elementary_loop (next_iter iteration)) tau in
  elementary_loop first_iteration

let _gen_metalevel new_level new_lv_env env cont tau =
  let new_level_cont = _gen_toplv_cont new_level new_lv_env in
  new_level_cont blond_banner (_meta_push env cont tau)
let _openloop : fsubrBody =
  fun args env cont tau ->
  match args with
  | arg1 :: [] ->
     let cont' = (fun new_level tau ->
         match new_level with
         | ConstVal (NumConst n) ->
            _gen_metalevel n (make_init_env ()) env cont tau
         | _ -> undef "_openloop") in
     _eval arg1 env cont' tau
  | arg1 :: arg2 :: [] ->
     let cont'' = (fun new_lv new_env_val tau ->
         match new_lv, new_env_val with
         | ConstVal (NumConst n), FunVal (ReifiedEnv new_env) ->
            _gen_metalevel n new_env env cont tau
         | _ -> Error ("_openloop", "not a reified environment", new_env_val)) in
     let cont' = (fun new_lv tau -> _eval arg2 env (cont'' new_lv) tau) in
     _eval arg1 env cont' tau
  | _ -> Error ("_openloop", "wrong arity", ListVal (_exp_to_val_star args))

let _extend lsvar lsval env_re cont tau =
  match lsvar, lsval, env_re with
  | (ListVal var_lst), (ListVal val_lst), (FunVal (ReifiedEnv env)) ->
     let vars = List.map val_to_var var_lst in
     if List.length vars = List.length val_lst
     then cont (_env_up (_extend_env vars val_lst env)) tau
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
     _eval var_lst env cont' tau
  | _ -> undef "_extend_reified_env"
let rec _let_idlis bindings =
  match bindings with
  | [] -> []
  | (ListExp (VarExp name :: _)) :: rst_bds ->
     name :: _let_idlis rst_bds
  | _ -> [] (* undefined in scheme impl *)

let rec _let_evlis bindings env cont tau =
  match bindings with
  | (ListExp (_ :: [body1])) :: rst_bds ->
     let cont' = (fun v tau ->
         match rst_bds with
         | [] -> cont (ListVal [v]) tau
         | _ ->
            _let_evlis rst_bds env
              (fun lv tau -> cont (cons_list_val v lv) tau)
              tau) in
     _eval body1 env cont' tau
  | _ -> undef "_let_evlis"

let _let : fsubrBody =
  fun args env cont tau ->
  match args with
  | (ListExp []) :: body :: [] ->
     _eval body env cont tau
  | (ListExp bindings) :: body :: [] ->
     let cont' = (fun vals tau ->
         match vals with
         | ListVal val_lst ->
            _eval body (_extend_env (_let_idlis bindings) val_lst env) cont tau
         | _ -> undef "_let" ) in
     _let_evlis bindings env cont' tau
  | _ -> undef "_let"

let rec one_env_update_vals env vals =
  match env, vals with
  | (var,_) :: env_rst, new_val :: vals_rst ->
     (var,new_val) :: (one_env_update_vals env_rst vals_rst)
  | _, _ -> env
let env_update_vals (env : env) vals =
  match env, vals with
  | env1 :: _, ListVal val_lst ->
     let env1_content = !env1 in
     let env1_new_content = one_env_update_vals env1_content val_lst in
     env1 := env1_new_content
  | _, _ -> ()

let _letrec : fsubrBody =
  fun args env cont tau ->
  match args with
  | (ListExp []) :: body :: [] ->
     _eval body env cont tau
  | (ListExp bindings) :: body :: [] ->
     let env = _extend_env (_let_idlis bindings) [] env in
     let cont' = (fun vals tau ->
         env_update_vals env vals;
         _eval body env cont tau) in
     _let_evlis bindings env cont' tau
  | _ -> undef "_letrec"

let _rec : fsubrBody =
  fun args env cont tau ->
  match args with
  | VarExp name :: body :: [] ->
     let env = _extend_env [name] [] env in
     let cont' = (fun a tau ->
         env_update_vals env (ListVal [a]);
         cont a tau) in
     _eval body env cont' tau
  | _ -> undef "_rec"

let rec _let_star_evlis bindings body env cont tau =
  match bindings with
  | [] -> _eval body env cont tau
  | (ListExp (VarExp name1 :: [body1])) :: rst_bds ->
     let cont' = (fun a tau ->
         _let_star_evlis rst_bds body
                (_extend_env [name1] [a] env)
                cont tau) in
     _eval body1 env cont' tau
  | _ -> undef "_let_star_evlis"

let _let_star : fsubrBody =
  fun args env cont tau ->
  match args with
  | (ListExp bindings) :: body :: [] ->
     _let_star_evlis bindings body env cont tau
  | _ -> undef "_let_star"

let rec _cond : fsubrBody =
  fun args env cont tau ->
  match args with
  | [] -> cont (ConstVal (StringConst "unmatched cond")) tau
  | (ListExp (cond1 :: [body1])) :: conds_rst ->
     (match cond1 with
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
         _eval cond1 env cont' tau)
  | _ -> undef "_cond"

let _reify_new_cont : fsubrBody =
  fun args env cont tau ->
  match args with
  | arg1 :: [] ->
     let cont' = (fun level tau ->
         match level with
         | ConstVal (NumConst lv) ->
            let new_cont = _gen_toplv_cont lv (make_init_env ()) in
            cont (_cont_up new_cont) tau
         | _ -> undef "_reify_new_cont") in
     _eval arg1 env cont' tau
  | arg1 :: arg2 :: [] ->
     let cont'' = (fun level env_re tau ->
         match level, env_re with
         | ConstVal (NumConst lv), FunVal (ReifiedEnv env_r) ->
            cont (_cont_up (_gen_toplv_cont lv env_r)) tau
         | _ -> Error ("_reify_new_cont",
                       "not a reified environment",
                       env_re)) in
     let cont' = (fun level tau ->
         _eval arg2 env (cont'' level) tau) in
     _eval arg1 env cont' tau
  | _ -> Error ("_reify_new_cont", "arity mismatch",
                ListVal (_exp_to_val_star args))
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
  fun _ _ _ _ ->
  ConstVal (StringConst "farvel!")

(***************************************************************************************)
(*********************** Table for Built in Special Forms of Blond *********************)
(***************************************************************************************)

let fsubr_table_0_h =
  [_case;
   _and;
   _or;
   _begin;
   _read;
   _openloop;
   _cond;
   _blond_exit;
   _reify_new_cont
  ]
let fsubr_table_1_h =
  [_quote
  ]
let fsubr_table_2_h =
  [_lambda;
   _delta;
   _gamma;
   _common_define;
   _define;
   _set;
   _let;
   _letrec;
   _rec;
   _let_star
  ]
let fsubr_table_3_h =
  [_if;
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
let fsubr_table = List.map (fun x -> FSubr x) fsubr_table_h

(***************************************************************************************)
(*************** Scheme Built in Functions that I need to define for Ocaml *************)
(***************************************************************************************)

(*************** Predicates & Boolean Operations *************)
let _is_zero : subr =
 UnarySubr
   (fun v ->
     match v with
     | ConstVal (NumConst 0) -> ConstVal (BoolConst true)
     | _ -> ConstVal (BoolConst false))
let _is_positive : subr =
 UnarySubr
   (fun v ->
     match v with
     | ConstVal (NumConst n) ->
        if n > 0 then ConstVal (BoolConst true)
        else ConstVal (BoolConst false)
     | _ -> ConstVal (BoolConst false))
let _is_negative : subr =
 UnarySubr
   (fun v ->
     match v with
     | ConstVal (NumConst n) ->
        if n < 0 then ConstVal (BoolConst true)
        else ConstVal (BoolConst false)
     | _ -> ConstVal (BoolConst false))
let _is_number : subr =
 UnarySubr
   (fun v ->
     match v with
     | ConstVal (NumConst _) -> ConstVal (BoolConst true)
     | _ -> ConstVal (BoolConst false))

let _is_string : subr =
 UnarySubr
   (fun v ->
     match v with
     | ConstVal (StringConst _) -> ConstVal (BoolConst true)
     | _ -> ConstVal (BoolConst false))
let _is_boolean : subr =
 UnarySubr
   (fun v ->
     match v with
     | ConstVal (BoolConst _) -> ConstVal (BoolConst true)
     | _ -> ConstVal (BoolConst false))

let _is_pair : subr =
 UnarySubr
   (fun v ->
     match v with
     | ListVal _ -> ConstVal (BoolConst true)
     | _ -> ConstVal (BoolConst false))
let _is_null : subr =
 UnarySubr
   (fun lst ->
     match lst with
     | ListVal [] -> ConstVal (BoolConst true)
     | _ -> ConstVal (BoolConst false))
let _is_applicable : subr =
 UnarySubr
   (fun v ->
     match v with
     | FunVal _ -> ConstVal (BoolConst true)
     | _ -> ConstVal (BoolConst false))
let _not : subr =
 UnarySubr
   (fun b ->
     match b with
     | ConstVal (BoolConst false) -> ConstVal (BoolConst true)
     | ListVal [] -> ConstVal (BoolConst true)
     | _ -> ConstVal (BoolConst false))
(*************** List Operations *************)
let _cons : subr =
 BinarySubr
   (fun v lst ->
     cons_list_val v lst)
let _length : subr =
 UnarySubr
   (fun lst ->
     match lst with
     | ListVal vlst ->
        ConstVal (NumConst (List.length vlst))
     | _ -> undef "_length")
let _car : subr =
 UnarySubr
   (fun lst ->
     match lst with
     | ListVal (hd :: _) -> hd
     | _ -> undef "_car")
let _cdr : subr =
 UnarySubr
   (fun lst ->
     match lst with
     | ListVal (_ :: tl) -> ListVal tl
     | _ -> undef "_cdr")     
let _cadr : subr =
 UnarySubr
   (fun lst ->
     match lst with
     | ListVal (_ :: v :: _) -> v
     | _ -> undef "_cadr")
let _caddr : subr =
 UnarySubr
   (fun lst ->
     match lst with
     | ListVal (_ :: _ :: v :: _) -> v
     | _ -> undef "_caddr")
(*************** Number Operations *************)
let _add : subr =
 BinarySubr
   (fun n1 n2 ->
     match n1, n2 with
     | ConstVal (NumConst n1'), ConstVal (NumConst n2') ->
        ConstVal (NumConst (n1' + n2'))
     | _ -> undef "_add")
let _sub : subr =
 BinarySubr
   (fun n1 n2 ->
     match n1, n2 with
     | ConstVal (NumConst n1'), ConstVal (NumConst n2') ->
        ConstVal (NumConst (n1' - n2'))
     | _ -> undef "_sub")
let _mult : subr =
 BinarySubr
   (fun n1 n2 ->
     match n1, n2 with
     | ConstVal (NumConst n1'), ConstVal (NumConst n2') ->
        ConstVal (NumConst (n1' * n2'))
     | _ -> undef "_mult")
let _lt : subr =
 BinarySubr
   (fun n1 n2 ->
     match n1, n2 with
     | ConstVal (NumConst n1'), ConstVal (NumConst n2') ->
        if n1' < n2' then ConstVal (BoolConst true)
        else ConstVal (BoolConst false)
     | _ -> undef "_lt")
let _gt : subr =
 BinarySubr
   (fun n1 n2 ->
     match n1, n2 with
     | ConstVal (NumConst n1'), ConstVal (NumConst n2') ->
        if n1' > n2' then ConstVal (BoolConst true)
        else ConstVal (BoolConst false)
     | _ -> undef "_gt")
let _equal : subr =
 BinarySubr
   (fun v1 v2 ->
     if v1 = v2 then ConstVal (BoolConst true)
     else ConstVal (BoolConst false))

(***************************************************************************************)
(************************* Table for Built in Functions of Blond ***********************)
(***************************************************************************************)


let subr_table_h : subr list =
  [_car;
   _cdr;
   _cadr;
   _caddr;

   _cons;
   _length;

   _is_null;
   _is_pair;

   _is_string;
   _is_boolean;
   _is_applicable;
   
   _is_zero;
   _is_negative;
   _is_positive; 
   _is_number;

   _add;
   _sub;
   _mult;
   _lt;
   _gt;
   _equal;
   
   _not;
   _ef;
   _reify_new_env;
   _cont_mode;
   _switch_cont_mode]
let subr_table = List.map (fun x -> Subr x) subr_table_h

(***************************************************************************************)
(************************* Complete Common Environment of Blond ************************)
(***************************************************************************************)
let table_common_subr_ids =
  ["car"; "cdr";
   "cadr"; "caddr";
   "cons"; "length";

   "null?"; "pair?";
   "string?";"boolean?";
   "procedure?";
   "zero?";"negative?"; "positive?";"number?";
      
   "+"; "-"; "*";
   "<"; ">";
   "equal?";
   
   "not"; "ef";

   "reify-new-environment";
   "continuation-mode";
   "switch-continuation-mode"
  ]
let table_common_fsubr_ids =
  [
    (* nullary *)
    "case";
    "and"; "or";
    "begin";
    "read";
    "openloop";
    "cond";
    "blond-exit";
    "reify-new-continuation";
    
    (* unary *)
    "quote";
    (* binary *)
    "lambda";
    "delta"; "gamma"; "meaning";
    "common-define"; "define";
    "set!";
    
    "let"; "letrec";
    "rec"; "let*";
    
    (* ternary *)
    "if";
    "extend-reified-environment"
  ]
    
let table_common_ids =
  List.append table_common_subr_ids table_common_fsubr_ids
let table_common_values =
  List.map (fun x -> FunVal x) (List.append subr_table fsubr_table)

let table_common_initial =
  zip_lst table_common_ids table_common_values

