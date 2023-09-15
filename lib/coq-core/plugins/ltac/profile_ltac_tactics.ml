
# 11 "plugins/ltac/profile_ltac_tactics.mlg"
 

(** Ltac profiling entrypoints *)

open Profile_ltac
open Stdarg



let __coq_plugin_name = "coq-core.plugins.ltac"
let _ = Mltop.add_known_module __coq_plugin_name

# 22 "plugins/ltac/profile_ltac_tactics.mlg"
 

let tclSET_PROFILING b =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> set_profiling b))

let tclRESET_PROFILE =
   Proofview.tclLIFT (Proofview.NonLogical.make reset_profile)

let tclSHOW_PROFILE ~cutoff =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> print_results ~cutoff))

let tclSHOW_PROFILE_TACTIC s =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> print_results_tactic s))

let tclRESTART_TIMER s =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> restart_timer s))

let tclFINISH_TIMING ?(prefix="Timer") (s : string option) =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> finish_timing ~prefix s))



let () = Tacentries.tactic_extend __coq_plugin_name "start_ltac_profiling" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("start", Tacentries.TyIdent ("ltac", 
                                                         Tacentries.TyIdent ("profiling", 
                                                         Tacentries.TyNil))), 
           (fun ist -> 
# 45 "plugins/ltac/profile_ltac_tactics.mlg"
                                      tclSET_PROFILING true 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "stop_ltac_profiling" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("stop", Tacentries.TyIdent ("ltac", 
                                                        Tacentries.TyIdent ("profiling", 
                                                        Tacentries.TyNil))), 
           (fun ist -> 
# 49 "plugins/ltac/profile_ltac_tactics.mlg"
                                     tclSET_PROFILING false 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "reset_ltac_profile" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("reset", Tacentries.TyIdent ("ltac", 
                                                         Tacentries.TyIdent ("profile", 
                                                         Tacentries.TyNil))), 
           (fun ist -> 
# 53 "plugins/ltac/profile_ltac_tactics.mlg"
                                    tclRESET_PROFILE 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "show_ltac_profile" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("show", Tacentries.TyIdent ("ltac", 
                                                        Tacentries.TyIdent ("profile", 
                                                        Tacentries.TyNil))), 
           (fun ist -> 
# 57 "plugins/ltac/profile_ltac_tactics.mlg"
                                   tclSHOW_PROFILE ~cutoff:!Flags.profile_ltac_cutoff 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("show", Tacentries.TyIdent ("ltac", 
                                                       Tacentries.TyIdent ("profile", 
                                                       Tacentries.TyIdent ("cutoff", 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_integer), 
                                                       Tacentries.TyNil))))), 
          (fun n ist -> 
# 58 "plugins/ltac/profile_ltac_tactics.mlg"
                                                       tclSHOW_PROFILE ~cutoff:(float_of_int n) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("show", Tacentries.TyIdent ("ltac", 
                                                       Tacentries.TyIdent ("profile", 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_string), 
                                                       Tacentries.TyNil)))), 
          (fun s ist -> 
# 59 "plugins/ltac/profile_ltac_tactics.mlg"
                                             tclSHOW_PROFILE_TACTIC s 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "restart_timer" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("restart_timer", Tacentries.TyArg (
                                                                 Extend.TUopt (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                 Tacentries.TyNil)), 
           (fun s ist -> 
# 63 "plugins/ltac/profile_ltac_tactics.mlg"
                                         tclRESTART_TIMER s 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "finish_timing" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("finish_timing", Tacentries.TyArg (
                                                                 Extend.TUopt (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                 Tacentries.TyNil)), 
           (fun s ist -> 
# 67 "plugins/ltac/profile_ltac_tactics.mlg"
                                         tclFINISH_TIMING ~prefix:"Timer" s 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("finish_timing", Tacentries.TyIdent ("(", 
                                                                Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_string), 
                                                                Tacentries.TyIdent (")", 
                                                                Tacentries.TyArg (
                                                                Extend.TUopt (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                Tacentries.TyNil))))), 
          (fun prefix s ist -> 
# 68 "plugins/ltac/profile_ltac_tactics.mlg"
                                                                tclFINISH_TIMING ~prefix s 
          )))]

let () = Vernacextend.vernac_extend ~command:"ResetLtacProfiling" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Reset", 
                                     Vernacextend.TyTerminal ("Ltac", 
                                     Vernacextend.TyTerminal ("Profile", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 72 "plugins/ltac/profile_ltac_tactics.mlg"
                                    reset_profile () 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ShowLtacProfile" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                     Vernacextend.TyTerminal ("Ltac", 
                                     Vernacextend.TyTerminal ("Profile", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 76 "plugins/ltac/profile_ltac_tactics.mlg"
                                   print_results ~cutoff:!Flags.profile_ltac_cutoff 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("Ltac", 
                                    Vernacextend.TyTerminal ("Profile", 
                                    Vernacextend.TyTerminal ("CutOff", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_integer), 
                                    Vernacextend.TyNil))))), (let coqpp_body n
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 77 "plugins/ltac/profile_ltac_tactics.mlg"
                                                       print_results ~cutoff:(float_of_int n) 
                                                                  ) in fun n
                                                             ?loc ~atts ()
                                                             -> coqpp_body n
                                                             (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ShowLtacProfileTactic" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                     Vernacextend.TyTerminal ("Ltac", 
                                     Vernacextend.TyTerminal ("Profile", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_string), 
                                     Vernacextend.TyNil)))), (let coqpp_body s
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 81 "plugins/ltac/profile_ltac_tactics.mlg"
                                             print_results_tactic s 
                                                                  ) in fun s
                                                             ?loc ~atts ()
                                                             -> coqpp_body s
                                                             (Attributes.unsupported_attributes atts)), None))]

