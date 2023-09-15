
# 11 "plugins/ltac/g_class.mlg"
 

open Class_tactics
open Stdarg
open Tacarg
open Classes



let __coq_plugin_name = "coq-core.plugins.ltac"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Vernacextend.vernac_extend ~command:"Typeclasses_Unfold_Settings" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Typeclasses", 
                                     Vernacextend.TyTerminal ("Transparent", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                     Vernacextend.TyNil))), (let coqpp_body cl
                                                            locality = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 26 "plugins/ltac/g_class.mlg"
                                                            
    set_typeclass_transparency_com ~locality cl true
  
                                                            ) in fun cl
                                                            ?loc ~atts ()
                                                            -> coqpp_body cl
                                                            (Attributes.parse tc_transparency_locality atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Typeclasses_Rigid_Settings" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Typeclasses", 
                                     Vernacextend.TyTerminal ("Opaque", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                     Vernacextend.TyNil))), (let coqpp_body cl
                                                            locality = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 33 "plugins/ltac/g_class.mlg"
                                                       
    set_typeclass_transparency_com ~locality cl false
  
                                                            ) in fun cl
                                                            ?loc ~atts ()
                                                            -> coqpp_body cl
                                                            (Attributes.parse tc_transparency_locality atts)), None))]


# 38 "plugins/ltac/g_class.mlg"
 

let pr_debug _prc _prlc _prt b =
  if b then Pp.str "debug" else Pp.mt()



let (wit_debug, debug) = Tacentries.argument_extend ~name:"debug" {
                                                                  Tacentries.arg_parsing = 
                                                                  Vernacextend.Arg_rules (
                                                                  [(Pcoq.Production.make
                                                                    (Pcoq.Rule.stop)
                                                                    (fun
                                                                    loc -> 
                                                                    
# 47 "plugins/ltac/g_class.mlg"
           false 
                                                                    ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "debug"))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 46 "plugins/ltac/g_class.mlg"
                   true 
                                                                   ))]);
                                                                  Tacentries.arg_tag = 
                                                                  Some
                                                                  (Geninterp.val_tag (Genarg.topwit wit_bool));
                                                                  Tacentries.arg_intern = 
                                                                  Tacentries.ArgInternWit (wit_bool);
                                                                  Tacentries.arg_subst = 
                                                                  Tacentries.ArgSubstWit (wit_bool);
                                                                  Tacentries.arg_interp = 
                                                                  Tacentries.ArgInterpWit (wit_bool);
                                                                  Tacentries.arg_printer = 
                                                                  ((fun env sigma -> 
                                                                  
# 45 "plugins/ltac/g_class.mlg"
                                                 pr_debug 
                                                                  ), (fun env sigma -> 
                                                                  
# 45 "plugins/ltac/g_class.mlg"
                                                 pr_debug 
                                                                  ), (fun env sigma -> 
                                                                  
# 45 "plugins/ltac/g_class.mlg"
                                                 pr_debug 
                                                                  ));
                                                                  }
let _ = (wit_debug, debug)


# 50 "plugins/ltac/g_class.mlg"
 

let pr_search_strategy_name _prc _prlc _prt = function
  | Dfs -> Pp.str "dfs"
  | Bfs -> Pp.str "bfs"

let pr_search_strategy _prc _prlc _prt = function
  | Some s -> pr_search_strategy_name _prc _prlc _prt s
  | None -> Pp.mt ()



let (wit_eauto_search_strategy_name, eauto_search_strategy_name) = Tacentries.argument_extend ~name:"eauto_search_strategy_name" 
                                                                   {
                                                                   Tacentries.arg_parsing = 
                                                                   Vernacextend.Arg_rules (
                                                                   [(
                                                                   Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "dfs"))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 64 "plugins/ltac/g_class.mlg"
                 Dfs 
                                                                   ));
                                                                   (Pcoq.Production.make
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.token (CLexer.terminal "bfs"))))
                                                                    (fun _
                                                                    loc -> 
                                                                    
# 63 "plugins/ltac/g_class.mlg"
                 Bfs 
                                                                    ))]);
                                                                   Tacentries.arg_tag = 
                                                                   None;
                                                                   Tacentries.arg_intern = 
                                                                   Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                                                   Tacentries.arg_subst = 
                                                                   Tacentries.ArgSubstFun (fun s v -> v);
                                                                   Tacentries.arg_interp = 
                                                                   Tacentries.ArgInterpRet;
                                                                   Tacentries.arg_printer = 
                                                                   ((fun env sigma -> 
                                                                   
# 62 "plugins/ltac/g_class.mlg"
                                                        pr_search_strategy_name 
                                                                   ), (fun env sigma -> 
                                                                   
# 62 "plugins/ltac/g_class.mlg"
                                                        pr_search_strategy_name 
                                                                   ), (fun env sigma -> 
                                                                   
# 62 "plugins/ltac/g_class.mlg"
                                                        pr_search_strategy_name 
                                                                   ));
                                                                   }
let _ = (wit_eauto_search_strategy_name, eauto_search_strategy_name)

let (wit_eauto_search_strategy, eauto_search_strategy) = Tacentries.argument_extend ~name:"eauto_search_strategy" 
                                                         {
                                                         Tacentries.arg_parsing = 
                                                         Vernacextend.Arg_rules (
                                                         [(Pcoq.Production.make
                                                           (Pcoq.Rule.stop)
                                                           (fun loc -> 
# 69 "plugins/ltac/g_class.mlg"
           None 
                                                                    ));
                                                         (Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                          ((Pcoq.Symbol.nterm eauto_search_strategy_name)))
                                                          ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                          (fun _ s _ loc -> 
# 68 "plugins/ltac/g_class.mlg"
                                                 Some s 
                                                                    ))]);
                                                         Tacentries.arg_tag = 
                                                         None;
                                                         Tacentries.arg_intern = 
                                                         Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                                         Tacentries.arg_subst = 
                                                         Tacentries.ArgSubstFun (fun s v -> v);
                                                         Tacentries.arg_interp = 
                                                         Tacentries.ArgInterpRet;
                                                         Tacentries.arg_printer = 
                                                         ((fun env sigma -> 
                                                         
# 67 "plugins/ltac/g_class.mlg"
                                                   pr_search_strategy 
                                                         ), (fun env sigma -> 
                                                         
# 67 "plugins/ltac/g_class.mlg"
                                                   pr_search_strategy 
                                                         ), (fun env sigma -> 
                                                         
# 67 "plugins/ltac/g_class.mlg"
                                                   pr_search_strategy 
                                                         ));
                                                         }
let _ = (wit_eauto_search_strategy, eauto_search_strategy)

let () = Vernacextend.vernac_extend ~command:"Typeclasses_Settings" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Typeclasses", 
                                     Vernacextend.TyTerminal ("eauto", 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_debug), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_eauto_search_strategy), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUopt (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_natural)), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body d s depth
         () = Vernacextend.vtdefault (fun () -> 
# 75 "plugins/ltac/g_class.mlg"
                                                                                           
     set_typeclasses_debug d;
     Option.iter set_typeclasses_strategy s;
     set_typeclasses_depth depth
   
              ) in fun d
         s depth ?loc ~atts () -> coqpp_body d s depth
         (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "typeclasses_eauto" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("typeclasses", Tacentries.TyIdent ("eauto", 
                                                               Tacentries.TyIdent ("dfs", 
                                                               Tacentries.TyArg (
                                                               Extend.TUopt (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                               Tacentries.TyIdent ("with", 
                                                               Tacentries.TyArg (
                                                               Extend.TUlist1 (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                               Tacentries.TyNil)))))), 
           (fun d l ist -> 
# 84 "plugins/ltac/g_class.mlg"
      typeclasses_eauto ~depth:d ~strategy:Dfs l 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("typeclasses", Tacentries.TyIdent ("eauto", 
                                                              Tacentries.TyIdent ("bfs", 
                                                              Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                              Tacentries.TyIdent ("with", 
                                                              Tacentries.TyArg (
                                                              Extend.TUlist1 (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                              Tacentries.TyNil)))))), 
          (fun d l ist -> 
# 86 "plugins/ltac/g_class.mlg"
      typeclasses_eauto ~depth:d ~strategy:Bfs l 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("typeclasses", Tacentries.TyIdent ("eauto", 
                                                              Tacentries.TyIdent ("best_effort", 
                                                              Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                              Tacentries.TyIdent ("with", 
                                                              Tacentries.TyArg (
                                                              Extend.TUlist1 (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                              Tacentries.TyNil)))))), 
          (fun d l ist -> 
# 88 "plugins/ltac/g_class.mlg"
      typeclasses_eauto ~depth:d ~best_effort:true l 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("typeclasses", Tacentries.TyIdent ("eauto", 
                                                              Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                              Tacentries.TyIdent ("with", 
                                                              Tacentries.TyArg (
                                                              Extend.TUlist1 (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                              Tacentries.TyNil))))), 
          (fun d l ist -> 
# 90 "plugins/ltac/g_class.mlg"
      typeclasses_eauto ~depth:d l 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("typeclasses", Tacentries.TyIdent ("eauto", 
                                                              Tacentries.TyIdent ("bfs", 
                                                              Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                              Tacentries.TyNil)))), 
          (fun d ist -> 
# 91 "plugins/ltac/g_class.mlg"
                                                         
     typeclasses_eauto ~depth:d ~strategy:Bfs ~only_classes:true [Class_tactics.typeclasses_db] 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("typeclasses", Tacentries.TyIdent ("eauto", 
                                                              Tacentries.TyIdent ("dfs", 
                                                              Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                              Tacentries.TyNil)))), 
          (fun d ist -> 
# 93 "plugins/ltac/g_class.mlg"
                                                         
     typeclasses_eauto ~depth:d ~strategy:Dfs ~only_classes:true [Class_tactics.typeclasses_db] 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("typeclasses", Tacentries.TyIdent ("eauto", 
                                                              Tacentries.TyIdent ("best_effort", 
                                                              Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                              Tacentries.TyNil)))), 
          (fun d ist -> 
# 95 "plugins/ltac/g_class.mlg"
                                                                 
      typeclasses_eauto ~depth:d ~only_classes:true ~best_effort:true [Class_tactics.typeclasses_db] 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("typeclasses", Tacentries.TyIdent ("eauto", 
                                                              Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                              Tacentries.TyNil))), 
          (fun d ist -> 
# 97 "plugins/ltac/g_class.mlg"
                                                   
     typeclasses_eauto ~depth:d ~only_classes:true [Class_tactics.typeclasses_db] 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "head_of_constr" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("head_of_constr", Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                  Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                  Tacentries.TyNil))), 
           (fun h c ist -> 
# 102 "plugins/ltac/g_class.mlg"
                                               head_of_constr h c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "not_evar" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("not_evar", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyNil)), 
           (fun ty ist -> 
# 106 "plugins/ltac/g_class.mlg"
                                 not_evar ty 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "is_ground" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("is_ground", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyNil)), 
           (fun ty ist -> 
# 110 "plugins/ltac/g_class.mlg"
                                  is_ground ty 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "autoapply" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("autoapply", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyIdent ("with", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_preident), 
                                                             Tacentries.TyNil)))), 
           (fun c i ist -> 
# 114 "plugins/ltac/g_class.mlg"
                                                    autoapply c i 
           )))]


# 117 "plugins/ltac/g_class.mlg"
 

(** TODO: DEPRECATE *)
(* A progress test that allows to see if the evars have changed *)
open Constr
open Proofview.Notations

let rec eq_constr_mod_evars sigma x y =
  let open EConstr in
  match EConstr.kind sigma x, EConstr.kind sigma y with
  | Evar (e1, l1), Evar (e2, l2) when not (Evar.equal e1 e2) -> true
  | _, _ -> compare_constr sigma (fun x y -> eq_constr_mod_evars sigma x y) x y

let progress_evars t =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let check =
      Proofview.Goal.enter begin fun gl' ->
        let sigma = Tacmach.project gl' in
        let newconcl = Proofview.Goal.concl gl' in
        if eq_constr_mod_evars sigma concl newconcl
        then
          let info = Exninfo.reify () in
          Tacticals.tclFAIL ~info (Pp.str"No progress made (modulo evars)")
        else Proofview.tclUNIT ()
      end
    in t <*> check
  end



let () = Tacentries.tactic_extend __coq_plugin_name "progress_evars" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("progress_evars", Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                  Tacentries.TyNil)), 
           (fun t ist -> 
# 149 "plugins/ltac/g_class.mlg"
                                      progress_evars (Tacinterp.tactic_of_value ist t) 
           )))]

