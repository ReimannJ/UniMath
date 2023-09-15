
# 19 "plugins/micromega/g_micromega.mlg"
 

open Ltac_plugin
open Stdarg
open Tacarg



let __coq_plugin_name = "coq-core.plugins.micromega"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "Lra_Q" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xlra_Q", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                          Tacentries.TyNil)), 
           (fun t ist -> 
# 30 "plugins/micromega/g_micromega.mlg"
                               Coq_micromega.xlra_Q (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Lra_wit_Q" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wlra_Q", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil))), 
           (fun w t ist -> 
# 34 "plugins/micromega/g_micromega.mlg"
                                       Coq_micromega.wlra_Q w t 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Lra_R" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xlra_R", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                          Tacentries.TyNil)), 
           (fun t ist -> 
# 38 "plugins/micromega/g_micromega.mlg"
                              Coq_micromega.xlra_R (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Lia" ~level:0 [(
                                                                   Tacentries.TyML (
                                                                   Tacentries.TyIdent ("xlia", 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                   Tacentries.TyNil)), 
                                                                   (fun t ist
                                                                   -> 
                                                                   
# 42 "plugins/micromega/g_micromega.mlg"
                            Coq_micromega.xlia (Tacinterp.tactic_of_value ist t) 
                                                                   )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Lia_wit" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wlia", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                        Tacentries.TyNil))), 
           (fun w t ist -> 
# 46 "plugins/micromega/g_micromega.mlg"
                                     Coq_micromega.wlia w t 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Nra_Q" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xnra_Q", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                          Tacentries.TyNil)), 
           (fun t ist -> 
# 50 "plugins/micromega/g_micromega.mlg"
                              Coq_micromega.xnra_Q (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Nra_wit_Q" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wnra_Q", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil))), 
           (fun w t ist -> 
# 54 "plugins/micromega/g_micromega.mlg"
                                       Coq_micromega.wnra_Q w t 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Nra_R" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xnra_R", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                          Tacentries.TyNil)), 
           (fun t ist -> 
# 58 "plugins/micromega/g_micromega.mlg"
                              Coq_micromega.xnra_R (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Nia" ~level:0 [(
                                                                   Tacentries.TyML (
                                                                   Tacentries.TyIdent ("xnia", 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                   Tacentries.TyNil)), 
                                                                   (fun t ist
                                                                   -> 
                                                                   
# 62 "plugins/micromega/g_micromega.mlg"
                            Coq_micromega.xnia (Tacinterp.tactic_of_value ist t) 
                                                                   )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Nia_wit" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wnia", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                        Tacentries.TyNil))), 
           (fun w t ist -> 
# 66 "plugins/micromega/g_micromega.mlg"
                                     Coq_micromega.wnia w t 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Sos_Z" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xsos_Z", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                          Tacentries.TyNil)), 
           (fun t ist -> 
# 70 "plugins/micromega/g_micromega.mlg"
                              Coq_micromega.xsos_Z (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Sos_wit_Z" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wsos_Z", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil))), 
           (fun w t ist -> 
# 74 "plugins/micromega/g_micromega.mlg"
                                       Coq_micromega.wsos_Z w t 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Sos_Q" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xsos_Q", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                          Tacentries.TyNil)), 
           (fun t ist -> 
# 78 "plugins/micromega/g_micromega.mlg"
                              Coq_micromega.xsos_Q (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Sos_wit_Q" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wsos_Q", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil))), 
           (fun w t ist -> 
# 82 "plugins/micromega/g_micromega.mlg"
                                       Coq_micromega.wsos_Q w t 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Sos_R" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xsos_R", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                          Tacentries.TyNil)), 
           (fun t ist -> 
# 86 "plugins/micromega/g_micromega.mlg"
                              Coq_micromega.xsos_R (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Psatz_Z" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xpsatz_Z", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                            Tacentries.TyNil))), 
           (fun i t ist -> 
# 91 "plugins/micromega/g_micromega.mlg"
    Coq_micromega.xpsatz_Z i (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Psatz_wit_Z" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wpsatz_Z", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyNil)))), 
           (fun i w t ist -> 
# 95 "plugins/micromega/g_micromega.mlg"
                                                       Coq_micromega.wpsatz_Z i w t 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Psatz_Q" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xpsatz_Q", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                            Tacentries.TyNil))), 
           (fun i t ist -> 
# 100 "plugins/micromega/g_micromega.mlg"
    Coq_micromega.xpsatz_Q i (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Psatz_wit_Q" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wpsatz_Q", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyNil)))), 
           (fun i w t ist -> 
# 104 "plugins/micromega/g_micromega.mlg"
                                                       Coq_micromega.wpsatz_Q i w t 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "Psatz_R" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("xpsatz_R", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                            Tacentries.TyNil))), 
           (fun i t ist -> 
# 109 "plugins/micromega/g_micromega.mlg"
    Coq_micromega.xpsatz_R i (Tacinterp.tactic_of_value ist t) 
           )))]

let () = Vernacextend.vernac_extend ~command:"ShowLiaProfile" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                     Vernacextend.TyTerminal ("Lia", 
                                     Vernacextend.TyTerminal ("Profile", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 113 "plugins/micromega/g_micromega.mlg"
                                  Coq_micromega.print_lia_profile () 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

