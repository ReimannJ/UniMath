
# 11 "plugins/nsatz/g_nsatz.mlg"
 

open Ltac_plugin
open Stdarg



let __coq_plugin_name = "coq-core.plugins.nsatz"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "nsatz_compute" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("nsatz_compute", Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                 Tacentries.TyNil)), 
           (fun lt ist -> 
# 21 "plugins/nsatz/g_nsatz.mlg"
                                       Nsatz.nsatz_compute (EConstr.Unsafe.to_constr lt) 
           )))]

