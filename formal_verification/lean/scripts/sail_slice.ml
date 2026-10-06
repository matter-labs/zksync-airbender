(* A generation adapter, not an instruction implementation. The upstream Lean
   backend performs its unmodified rewrites; upstream callgraph pruning keeps
   the requested execution cases and their transitive dependencies; the original
   Lean emitter serializes those unchanged definitions. *)
open Libsail
open Ast_compare
open Ast_util
open Interactive.State

let lean = Option.get (Target.get ~name:"lean")

let action out state =
  let ctx, ast, effect_info, env =
    Rewrites.rewrite state.ctx state.effect_info state.env (Target.rewrites lean) state.ast
  in
  let roots = IdSet.of_list [mk_id "execute_RTYPE"; mk_id "execute_ITYPE";
    mk_id "execute_UTYPE"; mk_id "get_arch_pc"; mk_id "get_next_pc"; mk_id "tick_pc"] in
  let ast = Callgraph.filter_ast_ids roots IdSet.empty ast in
  Target.action lean out {state with ctx; ast; effect_info; env}

let _ =
  Target.register ~name:"lean-slice"
    ~pre_parse_hook:(fun () -> Preprocess.add_default_symbol "LEAN")
    ~asserts_termination:true action
