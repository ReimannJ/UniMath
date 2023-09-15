
# 11 "plugins/ltac/g_auto.mlg"
 

open Pp
open Stdarg
open Pcoq.Prim
open Pcoq.Constr
open Pltac
open Hints



let __coq_plugin_name = "coq-core.plugins.ltac"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "eassumption" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("eassumption", Tacentries.TyNil), 
           (fun ist -> 
# 28 "plugins/ltac/g_auto.mlg"
                         Eauto.e_assumption 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "eexact" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("eexact", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil)), 
           (fun c ist -> 
# 32 "plugins/ltac/g_auto.mlg"
                              Eauto.e_give_exact c 
           )))]


# 35 "plugins/ltac/g_auto.mlg"
 

let pr_hintbases _prc _prlc _prt = Pptactic.pr_hintbases



let (wit_hintbases, hintbases) = Tacentries.argument_extend ~name:"hintbases" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.stop)
                                                            (fun loc -> 
# 46 "plugins/ltac/g_auto.mlg"
           Some [] 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "with"))))
                                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm preident)))))
                                                           (fun l _ loc -> 
# 45 "plugins/ltac/g_auto.mlg"
                                      Some l 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "with"))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "*"))))
                                                           (fun _ _ loc -> 
# 44 "plugins/ltac/g_auto.mlg"
                      None 
                                                                    ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.Val.Opt 
                                                      (Geninterp.Val.List 
                                                      (Geninterp.val_tag (Genarg.topwit wit_preident))));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.OptArg 
                                                         (Genarg.ListArg 
                                                         (wit_preident)));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.OptArg 
                                                        (Genarg.ListArg 
                                                        (wit_preident)));
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.OptArg 
                                                         (Genarg.ListArg 
                                                         (wit_preident)));
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 43 "plugins/ltac/g_auto.mlg"
               pr_hintbases 
                                                          ), (fun env sigma -> 
                                                          
# 43 "plugins/ltac/g_auto.mlg"
               pr_hintbases 
                                                          ), (fun env sigma -> 
                                                          
# 43 "plugins/ltac/g_auto.mlg"
               pr_hintbases 
                                                          ));
                                 }
let _ = (wit_hintbases, hintbases)


# 49 "plugins/ltac/g_auto.mlg"
 

let eval_uconstrs ist cs =
  let flags = Pretyping.{
    use_coercions = true;
    use_typeclasses = NoUseTC;
    solve_unification_constraints = true;
    fail_evar = false;
    expand_evars = true;
    program_mode = false;
    polymorphic = false;
  } in
  let map c env sigma = c env sigma in
  List.map (fun c -> map (Tacinterp.type_uconstr ~flags ist c)) cs

let pr_auto_using_raw env sigma _ _ _  = Pptactic.pr_auto_using @@ Ppconstr.pr_constr_expr env sigma
let pr_auto_using_glob env sigma _ _ _ = Pptactic.pr_auto_using (fun (c,_) ->
    Printer.pr_glob_constr_env env sigma c)
let pr_auto_using env sigma _ _ _ = Pptactic.pr_auto_using @@
     Printer.pr_closed_glob_env env sigma



let (wit_auto_using, auto_using) = Tacentries.argument_extend ~name:"auto_using" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.stop)
                                                              (fun loc -> 
# 78 "plugins/ltac/g_auto.mlg"
           [] 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "using"))))
                                                             ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm uconstr)) ((Pcoq.Symbol.rules 
                                                             [Pcoq.Rules.make 
                                                             (Pcoq.Rule.next_norec 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal ","))))
                                                             (fun _ loc -> 
                                                             
# 0 ""
()
                                                             )])) false)))
                                                             (fun l _ loc ->
                                                             
# 77 "plugins/ltac/g_auto.mlg"
                                               l 
                                                             ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.List 
                                                        (Geninterp.val_tag (Genarg.topwit wit_uconstr)));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                           (wit_uconstr));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                          (wit_uconstr));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                           (wit_uconstr));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 75 "plugins/ltac/g_auto.mlg"
                   pr_auto_using_raw env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 76 "plugins/ltac/g_auto.mlg"
                    pr_auto_using_glob env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 74 "plugins/ltac/g_auto.mlg"
               pr_auto_using env sigma 
                                                            ));
                                   }
let _ = (wit_auto_using, auto_using)

let () = Tacentries.tactic_extend __coq_plugin_name "trivial" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("trivial", Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                           Tacentries.TyNil))), 
           (fun lems db ist -> 
# 85 "plugins/ltac/g_auto.mlg"
      Auto.h_trivial (eval_uconstrs ist lems) db 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "info_trivial" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("info_trivial", Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                                Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                                Tacentries.TyNil))), 
           (fun lems db ist -> 
# 90 "plugins/ltac/g_auto.mlg"
      Auto.h_trivial ~debug:Info (eval_uconstrs ist lems) db 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "debug_trivial" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("debug", Tacentries.TyIdent ("trivial", 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                         Tacentries.TyNil)))), 
           (fun lems db ist -> 
# 95 "plugins/ltac/g_auto.mlg"
      Auto.h_trivial ~debug:Debug (eval_uconstrs ist lems) db 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "auto" ~level:0 [(
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("auto", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUopt (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                                    Tacentries.TyNil)))), 
                                                                    (fun n
                                                                    lems db
                                                                    ist -> 
                                                                    
# 100 "plugins/ltac/g_auto.mlg"
      Auto.h_auto n (eval_uconstrs ist lems) db 
                                                                    )))]

let () = Tacentries.tactic_extend __coq_plugin_name "info_auto" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("info_auto", Tacentries.TyArg (
                                                             Extend.TUopt (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                             Tacentries.TyNil)))), 
           (fun n lems db ist -> 
# 105 "plugins/ltac/g_auto.mlg"
      Auto.h_auto ~debug:Info n (eval_uconstrs ist lems) db 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "debug_auto" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("debug", Tacentries.TyIdent ("auto", 
                                                         Tacentries.TyArg (
                                                         Extend.TUopt (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                         Tacentries.TyNil))))), 
           (fun n lems db ist -> 
# 110 "plugins/ltac/g_auto.mlg"
      Auto.h_auto ~debug:Debug n (eval_uconstrs ist lems) db 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "eauto" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("eauto", Tacentries.TyArg (
                                                         Extend.TUopt (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                         Tacentries.TyNil)))), 
           (fun depth lems db ist -> 
# 117 "plugins/ltac/g_auto.mlg"
    Eauto.gen_eauto ?depth (eval_uconstrs ist lems) db 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "debug_eauto" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("debug", Tacentries.TyIdent ("eauto", 
                                                         Tacentries.TyArg (
                                                         Extend.TUopt (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                         Tacentries.TyNil))))), 
           (fun depth lems db ist -> 
# 122 "plugins/ltac/g_auto.mlg"
    Eauto.gen_eauto ~debug:Debug ?depth (eval_uconstrs ist lems) db 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "info_eauto" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("info_eauto", Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                              Tacentries.TyNil)))), 
           (fun depth lems db ist -> 
# 127 "plugins/ltac/g_auto.mlg"
    Eauto.gen_eauto ~debug:Info ?depth (eval_uconstrs ist lems) db 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "dfs_eauto" ~level:0 ~deprecation:( Deprecation.make ~since:"8.16" ~note:"Use [eauto] instead." () ) 
         [(Tacentries.TyML (Tacentries.TyIdent ("dfs", Tacentries.TyIdent ("eauto", 
                                                       Tacentries.TyArg (
                                                       Extend.TUopt (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var)), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_auto_using), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                       Tacentries.TyNil))))), 
           (fun depth lems db ist -> 
# 132 "plugins/ltac/g_auto.mlg"
    Eauto.gen_eauto ?depth (eval_uconstrs ist lems) db 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "autounfold" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("autounfold", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_clause_dft_concl), 
                                                              Tacentries.TyNil))), 
           (fun db cl ist -> 
# 136 "plugins/ltac/g_auto.mlg"
                                                           Eauto.autounfold_tac db cl 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "autounfold_one" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("autounfold_one", Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                                  Tacentries.TyIdent ("in", 
                                                                  Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                  Tacentries.TyNil)))), 
           (fun db id ist -> 
# 141 "plugins/ltac/g_auto.mlg"
      Eauto.autounfold_one (match db with None -> ["core"] | Some x -> "core"::x) (Some (id, Locus.InHyp)) 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("autounfold_one", Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_hintbases), 
                                                                 Tacentries.TyNil)), 
          (fun db ist -> 
# 143 "plugins/ltac/g_auto.mlg"
      Eauto.autounfold_one (match db with None -> ["core"] | Some x -> "core"::x) None 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "unify" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("unify", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                         Tacentries.TyNil))), 
           (fun x y ist -> 
# 147 "plugins/ltac/g_auto.mlg"
                                      Tactics.unify x y 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("unify", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                        Tacentries.TyIdent ("with", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_preident), 
                                                        Tacentries.TyNil))))), 
          (fun x y base ist -> 
# 148 "plugins/ltac/g_auto.mlg"
                                                            
    let table = try Some (Hints.searchtable_map base) with Not_found -> None in
    match table with
    | None ->
      let msg = str "Hint table " ++ str base ++ str " not found" in
      Tacticals.tclZEROMSG msg
    | Some t ->
      let state = Hints.Hint_db.transparent_state t in
      Tactics.unify ~state x y
  
          )))]


# 160 "plugins/ltac/g_auto.mlg"
 

let pr_pre_hints_path_atom _ _ _ = Hints.pp_hints_path_atom Libnames.pr_qualid
let pr_hints_path_atom _ _ _ = Hints.pp_hints_path_atom Printer.pr_global
let glob_hints_path_atom ist = Hints.glob_hints_path_atom



let (wit_hints_path_atom, hints_path_atom) = Tacentries.argument_extend ~name:"hints_path_atom" 
                                             {
                                             Tacentries.arg_parsing = 
                                             Vernacextend.Arg_rules (
                                             [(Pcoq.Production.make
                                               (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "_"))))
                                               (fun _ loc -> 
# 176 "plugins/ltac/g_auto.mlg"
               Hints.PathAny 
                                                             ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                              (fun g loc -> 
# 175 "plugins/ltac/g_auto.mlg"
                             Hints.PathHints g 
                                                            ))]);
                                             Tacentries.arg_tag = None;
                                             Tacentries.arg_intern = 
                                             Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                             
# 171 "plugins/ltac/g_auto.mlg"
                  glob_hints_path_atom 
                                             ));
                                             Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                             Tacentries.arg_interp = 
                                             Tacentries.ArgInterpRet;
                                             Tacentries.arg_printer = 
                                             ((fun env sigma -> 
# 173 "plugins/ltac/g_auto.mlg"
                   pr_pre_hints_path_atom 
                                             ), (fun env sigma -> 
# 174 "plugins/ltac/g_auto.mlg"
                    pr_hints_path_atom 
                                             ), (fun env sigma -> 
# 169 "plugins/ltac/g_auto.mlg"
               pr_hints_path_atom 
                                             ));
                                             }
let _ = (wit_hints_path_atom, hints_path_atom)


# 179 "plugins/ltac/g_auto.mlg"
 

let pr_hints_path prc prx pry c = Hints.pp_hints_path c
let pr_pre_hints_path prc prx pry c = Hints.pp_hints_path_gen Libnames.pr_qualid c
let glob_hints_path ist = Hints.glob_hints_path



let (wit_hints_path, hints_path) = Tacentries.argument_extend ~name:"hints_path" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              (Pcoq.Symbol.self))
                                                              (Pcoq.Symbol.self))
                                                              (fun q p loc ->
                                                              
# 200 "plugins/ltac/g_auto.mlg"
                                       Hints.PathSeq (p, q) 
                                                              ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.nterm hints_path_atom)))
                                                             (fun a loc -> 
# 199 "plugins/ltac/g_auto.mlg"
                              Hints.PathAtom a 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             (Pcoq.Symbol.self))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "|"))))
                                                             (Pcoq.Symbol.self))
                                                             (fun q _ p
                                                             loc -> 
# 198 "plugins/ltac/g_auto.mlg"
                                           Hints.PathOr (p, q) 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "eps"))))
                                                             (fun _ loc -> 
# 197 "plugins/ltac/g_auto.mlg"
                 Hints.PathEpsilon 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "emp"))))
                                                             (fun _ loc -> 
# 196 "plugins/ltac/g_auto.mlg"
                 Hints.PathEmpty 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             (Pcoq.Symbol.self))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "*"))))
                                                             (fun _ p loc ->
                                                             
# 195 "plugins/ltac/g_auto.mlg"
                             Hints.PathStar p 
                                                             ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                             (Pcoq.Symbol.self))
                                                             ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                             (fun _ p _
                                                             loc -> 
# 194 "plugins/ltac/g_auto.mlg"
                                  p 
                                                                    ))]);
                                   Tacentries.arg_tag = None;
                                   Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                           
# 190 "plugins/ltac/g_auto.mlg"
                glob_hints_path 
                                                           ));
                                   Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                   Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 191 "plugins/ltac/g_auto.mlg"
                 pr_pre_hints_path 
                                                            ), (fun env sigma -> 
                                                            
# 192 "plugins/ltac/g_auto.mlg"
                  pr_hints_path 
                                                            ), (fun env sigma -> 
                                                            
# 188 "plugins/ltac/g_auto.mlg"
             pr_hints_path 
                                                            ));
                                   }
let _ = (wit_hints_path, hints_path)

let (wit_opthints, opthints) = Tacentries.argument_extend ~name:"opthints" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.stop)
                                                          (fun loc -> 
# 207 "plugins/ltac/g_auto.mlg"
           None 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                         ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm preident)))))
                                                         (fun l _ loc -> 
# 206 "plugins/ltac/g_auto.mlg"
                                   Some l 
                                                                    ))]);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.Val.Opt 
                                                    (Geninterp.Val.List 
                                                    (Geninterp.val_tag (Genarg.topwit wit_preident))));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.OptArg 
                                                       (Genarg.ListArg 
                                                       (wit_preident)));
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.OptArg 
                                                      (Genarg.ListArg 
                                                      (wit_preident)));
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.OptArg 
                                                       (Genarg.ListArg 
                                                       (wit_preident)));
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 205 "plugins/ltac/g_auto.mlg"
               pr_hintbases 
                                                        ), (fun env sigma -> 
                                                        
# 205 "plugins/ltac/g_auto.mlg"
               pr_hintbases 
                                                        ), (fun env sigma -> 
                                                        
# 205 "plugins/ltac/g_auto.mlg"
               pr_hintbases 
                                                        ));
                               }
let _ = (wit_opthints, opthints)

let () = Vernacextend.vernac_extend ~command:"HintCut" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Hint", 
                                     Vernacextend.TyTerminal ("Cut", 
                                     Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_hints_path), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_opthints), 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body p dbnames
         locality = Vernacextend.vtdefault (fun () -> 
# 211 "plugins/ltac/g_auto.mlg"
                                                                                                                
  let entry = Hints.HintsCutEntry (Hints.glob_hints_path p) in
  Hints.add_hints ~locality
    (match dbnames with None -> ["core"] | Some l -> l) entry;
 
                    ) in fun p
         dbnames ?loc ~atts () -> coqpp_body p dbnames
         (Attributes.parse Attributes.really_hint_locality atts)), None))]

