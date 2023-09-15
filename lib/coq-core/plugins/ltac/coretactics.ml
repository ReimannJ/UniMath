
# 11 "plugins/ltac/coretactics.mlg"
 

open Util
open Locus
open Tactypes
open Genredexpr
open Stdarg
open Extraargs
open Tacarg
open Names
open Logic



let __coq_plugin_name = "coq-core.plugins.ltac"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "reflexivity" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("reflexivity", Tacentries.TyNil), 
           (fun ist -> 
# 30 "plugins/ltac/coretactics.mlg"
                         Tactics.intros_reflexivity 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "exact" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("exact", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                         Tacentries.TyNil)), 
           (fun c ist -> 
# 34 "plugins/ltac/coretactics.mlg"
                              Internals.exact ist c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "assumption" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("assumption", Tacentries.TyNil), 
           (fun ist -> 
# 38 "plugins/ltac/coretactics.mlg"
                        Tactics.assumption 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "etransitivity" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("etransitivity", Tacentries.TyNil), 
           (fun ist -> 
# 42 "plugins/ltac/coretactics.mlg"
                           Tactics.intros_transitivity None 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "cut" ~level:0 [(
                                                                   Tacentries.TyML (
                                                                   Tacentries.TyIdent ("cut", 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Tacentries.TyNil)), 
                                                                   (fun c ist
                                                                   -> 
                                                                   
# 46 "plugins/ltac/coretactics.mlg"
                           Tactics.cut c 
                                                                   )))]

let () = Tacentries.tactic_extend __coq_plugin_name "exact_no_check" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("exact_no_check", Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                  Tacentries.TyNil)), 
           (fun c ist -> 
# 50 "plugins/ltac/coretactics.mlg"
                                      Tactics.exact_no_check c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "vm_cast_no_check" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("vm_cast_no_check", Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Tacentries.TyNil)), 
           (fun c ist -> 
# 54 "plugins/ltac/coretactics.mlg"
                                        Tactics.vm_cast_no_check c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "native_cast_no_check" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("native_cast_no_check", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                            Tacentries.TyNil)), (fun c ist -> 
# 58 "plugins/ltac/coretactics.mlg"
                                            Tactics.native_cast_no_check c 
                                                )))]

let () = Tacentries.tactic_extend __coq_plugin_name "casetype" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("casetype", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyNil)), 
           (fun c ist -> 
# 62 "plugins/ltac/coretactics.mlg"
                                Tactics.case_type c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "elimtype" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("elimtype", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyNil)), 
           (fun c ist -> 
# 66 "plugins/ltac/coretactics.mlg"
                                Tactics.elim_type c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "lapply" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("lapply", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil)), 
           (fun c ist -> 
# 70 "plugins/ltac/coretactics.mlg"
                              Tactics.cut_and_apply c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "transitivity" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("transitivity", Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                Tacentries.TyNil)), 
           (fun c ist -> 
# 74 "plugins/ltac/coretactics.mlg"
                                    Tactics.intros_transitivity (Some c) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "left" ~level:0 [(
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("left", 
                                                                    Tacentries.TyNil), 
                                                                    (fun ist
                                                                    -> 
                                                                    
# 80 "plugins/ltac/coretactics.mlg"
                  Tactics.left_with_bindings false NoBindings 
                                                                    )))]

let () = Tacentries.tactic_extend __coq_plugin_name "eleft" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("eleft", Tacentries.TyNil), 
           (fun ist -> 
# 84 "plugins/ltac/coretactics.mlg"
                   Tactics.left_with_bindings true NoBindings 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "left_with" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("left", Tacentries.TyIdent ("with", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_bindings), 
                                                        Tacentries.TyNil))), 
           (fun bl ist -> 
# 88 "plugins/ltac/coretactics.mlg"
                                     
    Tacticals.tclDELAYEDWITHHOLES false bl (fun bl -> Tactics.left_with_bindings false bl)
  
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "eleft_with" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("eleft", Tacentries.TyIdent ("with", 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_bindings), 
                                                         Tacentries.TyNil))), 
           (fun bl ist -> 
# 94 "plugins/ltac/coretactics.mlg"
                                      
    Tacticals.tclDELAYEDWITHHOLES true bl (fun bl -> Tactics.left_with_bindings true bl)
  
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "right" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("right", Tacentries.TyNil), 
           (fun ist -> 
# 102 "plugins/ltac/coretactics.mlg"
                   Tactics.right_with_bindings false NoBindings 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "eright" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("eright", Tacentries.TyNil), 
           (fun ist -> 
# 106 "plugins/ltac/coretactics.mlg"
                    Tactics.right_with_bindings true NoBindings 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "right_with" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("right", Tacentries.TyIdent ("with", 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_bindings), 
                                                         Tacentries.TyNil))), 
           (fun bl ist -> 
# 110 "plugins/ltac/coretactics.mlg"
                                      
    Tacticals.tclDELAYEDWITHHOLES false bl (fun bl -> Tactics.right_with_bindings false bl)
  
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "eright_with" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("eright", Tacentries.TyIdent ("with", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_bindings), 
                                                          Tacentries.TyNil))), 
           (fun bl ist -> 
# 116 "plugins/ltac/coretactics.mlg"
                                       
    Tacticals.tclDELAYEDWITHHOLES true bl (fun bl -> Tactics.right_with_bindings true bl)
  
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "constructor" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("constructor", Tacentries.TyNil), 
           (fun ist -> 
# 124 "plugins/ltac/coretactics.mlg"
                         Tactics.any_constructor false None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("constructor", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                              Tacentries.TyNil)), 
          (fun i ist -> 
# 125 "plugins/ltac/coretactics.mlg"
                                      
    Tactics.constructor_tac false None i NoBindings
  
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("constructor", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                              Tacentries.TyIdent ("with", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_bindings), 
                                                              Tacentries.TyNil)))), 
          (fun i bl ist -> 
# 128 "plugins/ltac/coretactics.mlg"
                                                          
    let tac bl = Tactics.constructor_tac false None i bl in
    Tacticals.tclDELAYEDWITHHOLES false bl tac
  
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "econstructor" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("econstructor", Tacentries.TyNil), 
           (fun ist -> 
# 135 "plugins/ltac/coretactics.mlg"
                          Tactics.any_constructor true None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("econstructor", Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                               Tacentries.TyNil)), 
          (fun i ist -> 
# 136 "plugins/ltac/coretactics.mlg"
                                       
    Tactics.constructor_tac true None i NoBindings
  
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("econstructor", Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                               Tacentries.TyIdent ("with", 
                                                               Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_bindings), 
                                                               Tacentries.TyNil)))), 
          (fun i bl ist -> 
# 139 "plugins/ltac/coretactics.mlg"
                                                           
    let tac bl = Tactics.constructor_tac true None i bl in
    Tacticals.tclDELAYEDWITHHOLES true bl tac
  
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "specialize" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("specialize", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_constr_with_bindings), 
                                                              Tacentries.TyNil)), 
           (fun c ist -> 
# 148 "plugins/ltac/coretactics.mlg"
                                               
    Tacticals.tclDELAYEDWITHHOLES false c (fun c -> Tactics.specialize c None)
  
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("specialize", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr_with_bindings), 
                                                             Tacentries.TyIdent ("as", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_simple_intropattern), 
                                                             Tacentries.TyNil)))), 
          (fun c ipat ist -> 
# 151 "plugins/ltac/coretactics.mlg"
                                                                              
    Tacticals.tclDELAYEDWITHHOLES false c (fun c -> Tactics.specialize c (Some ipat))
  
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "symmetry" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("symmetry", Tacentries.TyNil), 
           (fun ist -> 
# 157 "plugins/ltac/coretactics.mlg"
                      Tactics.intros_symmetry {onhyps=Some[];concl_occs=AllOccurrences} 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "symmetry_in" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("symmetry", Tacentries.TyIdent ("in", 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_in_clause), 
                                                            Tacentries.TyNil))), 
           (fun cl ist -> 
# 161 "plugins/ltac/coretactics.mlg"
                                         Tactics.intros_symmetry cl 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "split" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("split", Tacentries.TyNil), 
           (fun ist -> 
# 167 "plugins/ltac/coretactics.mlg"
                   Tactics.split_with_bindings false [NoBindings] 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "esplit" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("esplit", Tacentries.TyNil), 
           (fun ist -> 
# 171 "plugins/ltac/coretactics.mlg"
                    Tactics.split_with_bindings true [NoBindings] 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "split_with" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("split", Tacentries.TyIdent ("with", 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_bindings), 
                                                         Tacentries.TyNil))), 
           (fun bl ist -> 
# 175 "plugins/ltac/coretactics.mlg"
                                      
    Tacticals.tclDELAYEDWITHHOLES false bl (fun bl -> Tactics.split_with_bindings false [bl])
  
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "esplit_with" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("esplit", Tacentries.TyIdent ("with", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_bindings), 
                                                          Tacentries.TyNil))), 
           (fun bl ist -> 
# 181 "plugins/ltac/coretactics.mlg"
                                       
    Tacticals.tclDELAYEDWITHHOLES true bl (fun bl -> Tactics.split_with_bindings true [bl])
  
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "exists" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("exists", Tacentries.TyNil), 
           (fun ist -> 
# 187 "plugins/ltac/coretactics.mlg"
                    Tactics.split_with_bindings false [NoBindings] 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("exists", Tacentries.TyArg (
                                                         Extend.TUlist1sep (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_bindings), ","), 
                                                         Tacentries.TyNil)), 
          (fun bll ist -> 
# 188 "plugins/ltac/coretactics.mlg"
                                                   Tactics.split_with_delayed_bindings false bll 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "eexists" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("eexists", Tacentries.TyNil), 
           (fun ist -> 
# 192 "plugins/ltac/coretactics.mlg"
                     Tactics.split_with_bindings true [NoBindings] 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("eexists", Tacentries.TyArg (
                                                          Extend.TUlist1sep (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_bindings), ","), 
                                                          Tacentries.TyNil)), 
          (fun bll ist -> 
# 193 "plugins/ltac/coretactics.mlg"
                                                    Tactics.split_with_delayed_bindings true bll 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "intros_until" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("intros", Tacentries.TyIdent ("until", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_quantified_hypothesis), 
                                                          Tacentries.TyNil))), 
           (fun h ist -> 
# 199 "plugins/ltac/coretactics.mlg"
                                                     Tactics.intros_until h 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "intro" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyNil), 
           (fun ist -> 
# 203 "plugins/ltac/coretactics.mlg"
                   Tactics.intro_move None MoveLast 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                        Tacentries.TyNil)), 
          (fun id ist -> 
# 204 "plugins/ltac/coretactics.mlg"
                             Tactics.intro_move (Some id) MoveLast 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                        Tacentries.TyIdent ("at", 
                                                        Tacentries.TyIdent ("top", 
                                                        Tacentries.TyNil)))), 
          (fun id ist -> 
# 205 "plugins/ltac/coretactics.mlg"
                                        Tactics.intro_move (Some id) MoveFirst 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                        Tacentries.TyIdent ("at", 
                                                        Tacentries.TyIdent ("bottom", 
                                                        Tacentries.TyNil)))), 
          (fun id ist -> 
# 206 "plugins/ltac/coretactics.mlg"
                                           Tactics.intro_move (Some id) MoveLast 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                        Tacentries.TyIdent ("after", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                        Tacentries.TyNil)))), 
          (fun id h ist -> 
# 207 "plugins/ltac/coretactics.mlg"
                                            Tactics.intro_move (Some id) (MoveAfter h) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                        Tacentries.TyIdent ("before", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                        Tacentries.TyNil)))), 
          (fun id h ist -> 
# 208 "plugins/ltac/coretactics.mlg"
                                             Tactics.intro_move (Some id) (MoveBefore h) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyIdent ("at", 
                                                        Tacentries.TyIdent ("top", 
                                                        Tacentries.TyNil))), 
          (fun ist -> 
# 209 "plugins/ltac/coretactics.mlg"
                              Tactics.intro_move None MoveFirst 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyIdent ("at", 
                                                        Tacentries.TyIdent ("bottom", 
                                                        Tacentries.TyNil))), 
          (fun ist -> 
# 210 "plugins/ltac/coretactics.mlg"
                                 Tactics.intro_move None MoveLast 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyIdent ("after", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                        Tacentries.TyNil))), 
          (fun h ist -> 
# 211 "plugins/ltac/coretactics.mlg"
                                  Tactics.intro_move None (MoveAfter h) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("intro", Tacentries.TyIdent ("before", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                        Tacentries.TyNil))), 
          (fun h ist -> 
# 212 "plugins/ltac/coretactics.mlg"
                                   Tactics.intro_move None (MoveBefore h) 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "move" ~level:0 [(
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("move", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                    Tacentries.TyIdent ("at", 
                                                                    Tacentries.TyIdent ("top", 
                                                                    Tacentries.TyNil)))), 
                                                                    (fun id
                                                                    ist -> 
                                                                    
# 218 "plugins/ltac/coretactics.mlg"
                                     Tactics.move_hyp id MoveFirst 
                                                                    )));
                                                                    (
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("move", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                    Tacentries.TyIdent ("at", 
                                                                    Tacentries.TyIdent ("bottom", 
                                                                    Tacentries.TyNil)))), 
                                                                    (fun id
                                                                    ist -> 
                                                                    
# 219 "plugins/ltac/coretactics.mlg"
                                        Tactics.move_hyp id MoveLast 
                                                                    )));
                                                                    (
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("move", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                    Tacentries.TyIdent ("after", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                    Tacentries.TyNil)))), 
                                                                    (fun id h
                                                                    ist -> 
                                                                    
# 220 "plugins/ltac/coretactics.mlg"
                                         Tactics.move_hyp id (MoveAfter h) 
                                                                    )));
                                                                    (
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("move", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                    Tacentries.TyIdent ("before", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                    Tacentries.TyNil)))), 
                                                                    (fun id h
                                                                    ist -> 
                                                                    
# 221 "plugins/ltac/coretactics.mlg"
                                          Tactics.move_hyp id (MoveBefore h) 
                                                                    )))]

let () = Tacentries.tactic_extend __coq_plugin_name "rename" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("rename", Tacentries.TyArg (
                                                          Extend.TUlist1sep (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_rename), ","), 
                                                          Tacentries.TyNil)), 
           (fun ids ist -> 
# 227 "plugins/ltac/coretactics.mlg"
                                                 Tactics.rename_hyp ids 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "revert" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("revert", Tacentries.TyArg (
                                                          Extend.TUlist1 (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_hyp)), 
                                                          Tacentries.TyNil)), 
           (fun hl ist -> 
# 233 "plugins/ltac/coretactics.mlg"
                                    Tactics.revert hl 
           )))]


# 238 "plugins/ltac/coretactics.mlg"
 

let simple_induct h =
  Tacticals.tclTHEN (Tactics.intros_until h)
    (Tacticals.onLastHyp Tactics.simplest_elim)



let () = Tacentries.tactic_extend __coq_plugin_name "simple_induction" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("simple", Tacentries.TyIdent ("induction", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_quantified_hypothesis), 
                                                          Tacentries.TyNil))), 
           (fun h ist -> 
# 247 "plugins/ltac/coretactics.mlg"
                                                         simple_induct h 
           )))]


# 250 "plugins/ltac/coretactics.mlg"
 

let simple_destruct h =
  Tacticals.tclTHEN (Tactics.intros_until h)
    (Tacticals.onLastHyp Tactics.simplest_case)



let () = Tacentries.tactic_extend __coq_plugin_name "simple_destruct" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("simple", Tacentries.TyIdent ("destruct", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_quantified_hypothesis), 
                                                          Tacentries.TyNil))), 
           (fun h ist -> 
# 259 "plugins/ltac/coretactics.mlg"
                                                        simple_destruct h 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "admit" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("admit", Tacentries.TyNil), 
           (fun ist -> 
# 265 "plugins/ltac/coretactics.mlg"
                  Proofview.give_up 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "fix" ~level:0 [(
                                                                   Tacentries.TyML (
                                                                   Tacentries.TyIdent ("fix", 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Tacentries.TyArg (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_natural), 
                                                                   Tacentries.TyNil))), 
                                                                   (fun id n
                                                                   ist -> 
                                                                   
# 271 "plugins/ltac/coretactics.mlg"
                                      Tactics.fix id n 
                                                                   )))]

let () = Tacentries.tactic_extend __coq_plugin_name "cofix" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("cofix", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                         Tacentries.TyNil)), 
           (fun id ist -> 
# 277 "plugins/ltac/coretactics.mlg"
                             Tactics.cofix id 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "clear" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("clear", Tacentries.TyArg (
                                                         Extend.TUlist0 (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_hyp)), 
                                                         Tacentries.TyNil)), 
           (fun ids ist -> 
# 283 "plugins/ltac/coretactics.mlg"
                                
    if List.is_empty ids then Tactics.keep []
    else Tactics.clear ids
  
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("clear", Tacentries.TyIdent ("-", 
                                                        Tacentries.TyArg (
                                                        Extend.TUlist1 (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_hyp)), 
                                                        Tacentries.TyNil))), 
          (fun ids ist -> 
# 287 "plugins/ltac/coretactics.mlg"
                                        Tactics.keep ids 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "clearbody" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("clearbody", Tacentries.TyArg (
                                                             Extend.TUlist1 (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_hyp)), 
                                                             Tacentries.TyNil)), 
           (fun ids ist -> 
# 293 "plugins/ltac/coretactics.mlg"
                                        Tactics.clear_body ids 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "generalize_dependent" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("generalize", Tacentries.TyIdent ("dependent", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                              Tacentries.TyNil))), 
           (fun c ist -> 
# 299 "plugins/ltac/coretactics.mlg"
                                              Tactics.generalize_dep c 
           )))]


# 304 "plugins/ltac/coretactics.mlg"
 

open Tacexpr

let initial_atomic () =
  let nocl = {onhyps=Some[];concl_occs=AllOccurrences} in
  let iter (s, t) =
    let body = CAst.make (TacAtom t) in
    Tacenv.register_ltac false false (Names.Id.of_string s) body
  in
  let () = List.iter iter
      [ "red", TacReduce(Red false,nocl);
        "hnf", TacReduce(Hnf,nocl);
        "simpl", TacReduce(Simpl (Redops.all_flags,None),nocl);
        "compute", TacReduce(Cbv Redops.all_flags,nocl);
        "intros", TacIntroPattern (false,[]);
      ]
  in
  let iter (s, t) = Tacenv.register_ltac false false (Names.Id.of_string s) t in
  List.iter iter
      [ "idtac", CAst.make (TacId []);
        "fail", CAst.make (TacFail (TacLocal,ArgArg 0,[]));
        "fresh", CAst.make @@ TacArg(TacFreshId [])
      ]

let () = Mltop.declare_cache_obj initial_atomic "coq-core.plugins.ltac"

(* First-class Ltac access to primitive blocks *)

let initial_name s = { mltac_plugin = "coq-core.plugins.ltac"; mltac_tactic = s; }
let initial_entry s = { mltac_name = initial_name s; mltac_index = 0; }

let register_list_tactical name f =
  let tac args ist = match args with
  | [v] ->
    begin match Tacinterp.Value.to_list v with
    | None -> Tacticals.tclZEROMSG (Pp.str "Expected a list")
    | Some tacs ->
      let tacs = List.map (fun tac -> Tacinterp.tactic_of_value ist tac) tacs in
      f tacs
    end
  | _ -> assert false
  in
  Tacenv.register_ml_tactic (initial_name name) [|tac|]

let () = register_list_tactical "first" Tacticals.tclFIRST
let () = register_list_tactical "solve" Tacticals.tclSOLVE

let initial_tacticals () =
  let idn n = Id.of_string (Printf.sprintf "_%i" n) in
  let varn n = Reference (ArgVar (CAst.make (idn n))) in
  let iter (s, t) = Tacenv.register_ltac false false (Id.of_string s) t in
  List.iter iter [
    "first", CAst.make (TacFun
        ([Name (idn 0)], CAst.make (TacML (initial_entry "first", [varn 0]))));
    "solve", CAst.make (TacFun
        ([Name (idn 0)], CAst.make (TacML (initial_entry "solve", [varn 0]))));
  ]

let () = Mltop.declare_cache_obj initial_tacticals "coq-core.plugins.ltac"



