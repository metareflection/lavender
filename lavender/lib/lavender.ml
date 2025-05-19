open Evaluator
open Init

let level_above level =
  match level with
  | ConstVal (NumConst n) -> ConstVal (NumConst (1 + n))
  | _ -> error "level_above" "impossible level" level
let rec init_meta_cont level efun =
  let an_init_env = make_init_env () in 
  let an_init_cont = _gen_toplv_cont (level_above level) an_init_env efun in
  Tower ((an_init_env, an_init_cont, efun),
         (fun new_eval -> init_meta_cont (level_above level) new_eval))
            
let lavender =
  fun () ->
  table_common := table_common_initial;
  let initial_level = ConstVal (NumConst 0) in
  let initial_eval = make_init_eval () in
  let cont = _gen_toplv_cont initial_level (make_init_env ()) initial_eval in
  cont lavender_banner (init_meta_cont initial_level initial_eval)
