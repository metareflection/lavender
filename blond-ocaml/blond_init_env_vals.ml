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
let fsubr_table_0_h =
  [
  ]
let fsubr_table_1_h =
  [_quote,
  ]
let fsubr_table_2_h =
  [_lambda,
   _delta,
   _gamma,
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

let subr_table_h =
  [
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
        (_inFsubr 2 _common-define) (_inFsubr 2 _define)
        (_inFsubr 2 _set!)
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
