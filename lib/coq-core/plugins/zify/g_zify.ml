
# 11 "plugins/micromega/g_zify.mlg"
 

open Ltac_plugin
open Stdarg
open Tacarg



let __coq_plugin_name = "coq-core.plugins.zify"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Vernacextend.vernac_extend ~command:"DECLAREINJECTION" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Zify", 
                                     Vernacextend.TyTerminal ("InjTyp", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNil)))), (let coqpp_body t
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 22 "plugins/micromega/g_zify.mlg"
                                               Zify.InjTable.register t 
                                                                  ) in fun t
                                                             ?loc ~atts ()
                                                             -> coqpp_body t
                                                             (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("BinOp", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 23 "plugins/micromega/g_zify.mlg"
                                                Zify.BinOp.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("UnOp", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 24 "plugins/micromega/g_zify.mlg"
                                                Zify.UnOp.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("CstOp", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 25 "plugins/micromega/g_zify.mlg"
                                                Zify.CstOp.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("BinRel", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 26 "plugins/micromega/g_zify.mlg"
                                                Zify.BinRel.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("PropOp", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 27 "plugins/micromega/g_zify.mlg"
                                                Zify.PropBinOp.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("PropBinOp", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 28 "plugins/micromega/g_zify.mlg"
                                                   Zify.PropBinOp.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("PropUOp", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 29 "plugins/micromega/g_zify.mlg"
                                                Zify.PropUnOp.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("BinOpSpec", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 30 "plugins/micromega/g_zify.mlg"
                                                Zify.BinOpSpec.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("UnOpSpec", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 31 "plugins/micromega/g_zify.mlg"
                                                Zify.UnOpSpec.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Zify", 
                                                                    Vernacextend.TyTerminal ("Saturate", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t () = Vernacextend.vtdefault (fun () -> 
# 32 "plugins/micromega/g_zify.mlg"
                                                Zify.Saturate.register t 
                                ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "ITER" ~level:0 [(
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("zify_iter_specs", 
                                                                    Tacentries.TyNil), 
                                                                    (fun ist
                                                                    -> 
                                                                    
# 36 "plugins/micromega/g_zify.mlg"
                            Zify.iter_specs
                                                                    )))]

let () = Tacentries.tactic_extend __coq_plugin_name "TRANS" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("zify_op", Tacentries.TyNil), 
           (fun ist -> 
# 40 "plugins/micromega/g_zify.mlg"
                      Zify.zify_tac 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("zify_saturate", Tacentries.TyNil), 
          (fun ist -> 
# 41 "plugins/micromega/g_zify.mlg"
                            Zify.saturate 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("zify_iter_let", Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                Tacentries.TyNil)), 
          (fun t ist -> 
# 42 "plugins/micromega/g_zify.mlg"
                                    Zify.iter_let t 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("zify_elim_let", Tacentries.TyNil), 
          (fun ist -> 
# 43 "plugins/micromega/g_zify.mlg"
                           Zify.elim_let 
          )))]

let () = Vernacextend.vernac_extend ~command:"ZifyPrint" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                     Vernacextend.TyTerminal ("Zify", 
                                     Vernacextend.TyTerminal ("InjTyp", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 47 "plugins/micromega/g_zify.mlg"
                                 Zify.InjTable.print () 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("Zify", 
                                    Vernacextend.TyTerminal ("BinOp", 
                                    Vernacextend.TyNil))), (let coqpp_body () = 
                                                           Vernacextend.vtdefault (fun () -> 
                                                           
# 48 "plugins/micromega/g_zify.mlg"
                                 Zify.BinOp.print () 
                                                           ) in fun ?loc ~atts ()
                                                           -> coqpp_body (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("Zify", 
                                    Vernacextend.TyTerminal ("UnOp", 
                                    Vernacextend.TyNil))), (let coqpp_body () = 
                                                           Vernacextend.vtdefault (fun () -> 
                                                           
# 49 "plugins/micromega/g_zify.mlg"
                                 Zify.UnOp.print () 
                                                           ) in fun ?loc ~atts ()
                                                           -> coqpp_body (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("Zify", 
                                    Vernacextend.TyTerminal ("CstOp", 
                                    Vernacextend.TyNil))), (let coqpp_body () = 
                                                           Vernacextend.vtdefault (fun () -> 
                                                           
# 50 "plugins/micromega/g_zify.mlg"
                                 Zify.CstOp.print () 
                                                           ) in fun ?loc ~atts ()
                                                           -> coqpp_body (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("Zify", 
                                    Vernacextend.TyTerminal ("BinRel", 
                                    Vernacextend.TyNil))), (let coqpp_body () = 
                                                           Vernacextend.vtdefault (fun () -> 
                                                           
# 51 "plugins/micromega/g_zify.mlg"
                                 Zify.BinRel.print () 
                                                           ) in fun ?loc ~atts ()
                                                           -> coqpp_body (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("Zify", 
                                    Vernacextend.TyTerminal ("UnOpSpec", 
                                    Vernacextend.TyNil))), (let coqpp_body () = 
                                                           Vernacextend.vtdefault (fun () -> 
                                                           
# 52 "plugins/micromega/g_zify.mlg"
                                  Zify.UnOpSpec.print() 
                                                           ) in fun ?loc ~atts ()
                                                           -> coqpp_body (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                    Vernacextend.TyTerminal ("Zify", 
                                    Vernacextend.TyTerminal ("BinOpSpec", 
                                    Vernacextend.TyNil))), (let coqpp_body () = 
                                                           Vernacextend.vtdefault (fun () -> 
                                                           
# 53 "plugins/micromega/g_zify.mlg"
                                   Zify.BinOpSpec.print() 
                                                           ) in fun ?loc ~atts ()
                                                           -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

