open Evaluator
open Init

let level_above level = 1 + level
let rec init_meta_cont level =
  let an_init_env = make_init_env () in
  let an_init_cont = _gen_toplv_cont (level_above level) an_init_env in
  Tower ((an_init_env, an_init_cont),
         (fun () -> init_meta_cont (level_above level)))
              
let lavender =
  fun () ->
  table_common := table_common_initial;
  let initial_level = 0 in
  let cont = _gen_toplv_cont initial_level (make_init_env ()) in
  cont lavender_banner (init_meta_cont initial_level)

