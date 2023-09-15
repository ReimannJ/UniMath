
# 17 "plugins/ltac/g_eqdecide.mlg"
 

open Eqdecide
open Stdarg



let __coq_plugin_name = "coq-core.plugins.ltac"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "decide_equality" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("decide", Tacentries.TyIdent ("equality", 
                                                          Tacentries.TyNil)), 
           (fun ist -> 
# 27 "plugins/ltac/g_eqdecide.mlg"
                               decideEqualityGoal 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "compare" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("compare", Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                           Tacentries.TyNil))), 
           (fun c1 c2 ist -> 
# 31 "plugins/ltac/g_eqdecide.mlg"
                                           compare c1 c2 
           )))]

