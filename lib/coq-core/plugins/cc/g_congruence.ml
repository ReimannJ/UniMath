
# 11 "plugins/cc/g_congruence.mlg"
 

open Ltac_plugin
open Cctac
open Stdarg



let __coq_plugin_name = "coq-core.plugins.cc"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "cc" ~level:0 [(Tacentries.TyML (
                                                                    Tacentries.TyIdent ("congruence", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUopt (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_natural)), 
                                                                    Tacentries.TyNil)), 
                                                                    (fun n
                                                                    ist -> 
                                                                    
# 25 "plugins/cc/g_congruence.mlg"
     congruence_tac (Option.default 1000 n) [] 
                                                                    )));
                                                                  (Tacentries.TyML (
                                                                   Tacentries.TyIdent ("congruence", 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUopt (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_natural)), 
                                                                   Tacentries.TyIdent ("with", 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                                                   Tacentries.TyNil)))), 
                                                                   (fun n l
                                                                   ist -> 
                                                                   
# 27 "plugins/cc/g_congruence.mlg"
     congruence_tac (Option.default 1000 n) l 
                                                                   )));
                                                                  (Tacentries.TyML (
                                                                   Tacentries.TyIdent ("simple", 
                                                                   Tacentries.TyIdent ("congruence", 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUopt (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_natural)), 
                                                                   Tacentries.TyNil))), 
                                                                   (fun n ist
                                                                   -> 
                                                                   
# 29 "plugins/cc/g_congruence.mlg"
     simple_congruence_tac (Option.default 1000 n) [] 
                                                                   )));
                                                                  (Tacentries.TyML (
                                                                   Tacentries.TyIdent ("simple", 
                                                                   Tacentries.TyIdent ("congruence", 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUopt (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_natural)), 
                                                                   Tacentries.TyIdent ("with", 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                                                   Tacentries.TyNil))))), 
                                                                   (fun n l
                                                                   ist -> 
                                                                   
# 31 "plugins/cc/g_congruence.mlg"
     simple_congruence_tac (Option.default 1000 n) l 
                                                                   )))]

let () = Tacentries.tactic_extend __coq_plugin_name "f_equal" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("f_equal", Tacentries.TyNil), 
           (fun ist -> 
# 35 "plugins/cc/g_congruence.mlg"
                     f_equal 
           )))]

