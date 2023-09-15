
# 13 "plugins/ssrmatching/g_ssrmatching.mlg"
 

open Ltac_plugin
open Pcoq.Constr
open Ssrmatching
open Ssrmatching.Internal

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.get_keyword_state () ;;



let __coq_plugin_name = "coq-core.plugins.ssrmatching"
let _ = Mltop.add_known_module __coq_plugin_name

# 28 "plugins/ssrmatching/g_ssrmatching.mlg"
 

let pr_rpattern _ _ _ = pr_rpattern



let (wit_rpattern, rpattern) = Tacentries.argument_extend ~name:"rpattern" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.nterm lconstr)))
                                                          ((Pcoq.Symbol.token (CLexer.terminal "as"))))
                                                          ((Pcoq.Symbol.nterm lconstr)))
                                                          ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                          ((Pcoq.Symbol.nterm lconstr)))
                                                          (fun c _ x _ e
                                                          loc -> 
# 49 "plugins/ssrmatching/g_ssrmatching.mlg"
      mk_rpattern (E_As_X_In_T (mk_lterm e None, mk_lterm x None, mk_lterm c None)) 
                                                                 ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         (fun c _ x _ e
                                                         loc -> 
# 47 "plugins/ssrmatching/g_ssrmatching.mlg"
      mk_rpattern (E_In_X_In_T (mk_lterm e None, mk_lterm x None, mk_lterm c None)) 
                                                                ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         (fun c _ x _ loc ->
                                                         
# 45 "plugins/ssrmatching/g_ssrmatching.mlg"
      mk_rpattern (In_X_In_T (mk_lterm x None, mk_lterm c None)) 
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         (fun c _ x loc -> 
# 43 "plugins/ssrmatching/g_ssrmatching.mlg"
      mk_rpattern (X_In_T (mk_lterm x None, mk_lterm c None)) 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         (fun c _ loc -> 
# 41 "plugins/ssrmatching/g_ssrmatching.mlg"
                             mk_rpattern (In_T (mk_lterm c None)) 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm lconstr)))
                                                         (fun c loc -> 
# 40 "plugins/ssrmatching/g_ssrmatching.mlg"
                        mk_rpattern (T (mk_lterm c None)) 
                                                                    ))]);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.val_tag (Genarg.topwit wit_rpatternty));
                               Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                       
# 38 "plugins/ssrmatching/g_ssrmatching.mlg"
                  glob_rpattern 
                                                       ));
                               Tacentries.arg_subst = Tacentries.ArgSubstFun (
                                                      
# 39 "plugins/ssrmatching/g_ssrmatching.mlg"
                   subst_rpattern 
                                                      );
                               Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                       
# 37 "plugins/ssrmatching/g_ssrmatching.mlg"
                   interp_rpattern 
                                                       );
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 36 "plugins/ssrmatching/g_ssrmatching.mlg"
               pr_rpattern 
                                                        ), (fun env sigma -> 
                                                        
# 36 "plugins/ssrmatching/g_ssrmatching.mlg"
               pr_rpattern 
                                                        ), (fun env sigma -> 
                                                        
# 36 "plugins/ssrmatching/g_ssrmatching.mlg"
               pr_rpattern 
                                                        ));
                               }
let _ = (wit_rpattern, rpattern)


# 52 "plugins/ssrmatching/g_ssrmatching.mlg"
 

let pr_ssrterm _ _ _ = pr_ssrterm



let (wit_cpattern, cpattern) = Tacentries.argument_extend ~name:"cpattern" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.token (CLexer.terminal "Qed"))))
                                                          ((Pcoq.Symbol.nterm constr)))
                                                          (fun c _ loc -> 
# 64 "plugins/ssrmatching/g_ssrmatching.mlg"
                           mk_lterm c None 
                                                                    ))]);
                               Tacentries.arg_tag = None;
                               Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                       
# 61 "plugins/ssrmatching/g_ssrmatching.mlg"
                     glob_cpattern 
                                                       ));
                               Tacentries.arg_subst = Tacentries.ArgSubstFun (
                                                      
# 61 "plugins/ssrmatching/g_ssrmatching.mlg"
                                                      subst_ssrterm 
                                                      );
                               Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                       
# 60 "plugins/ssrmatching/g_ssrmatching.mlg"
                      interp_ssrterm 
                                                       );
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 62 "plugins/ssrmatching/g_ssrmatching.mlg"
                      pr_ssrterm 
                                                        ), (fun env sigma -> 
                                                        
# 63 "plugins/ssrmatching/g_ssrmatching.mlg"
                       pr_ssrterm 
                                                        ), (fun env sigma -> 
                                                        
# 59 "plugins/ssrmatching/g_ssrmatching.mlg"
                  pr_ssrterm 
                                                        ));
                               }
let _ = (wit_cpattern, cpattern)


# 67 "plugins/ssrmatching/g_ssrmatching.mlg"
 

let input_ssrtermkind strm = match LStream.peek_nth 0 strm with
  | Tok.KEYWORD "(" -> InParens
  | Tok.KEYWORD "@" -> WithAt
  | _ -> NoFlag
let ssrtermkind = Pcoq.Entry.(of_parser "ssrtermkind" { parser_fun = input_ssrtermkind })



let _ = let () =
        Pcoq.grammar_extend cpattern
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm ssrtermkind)))
                                            ((Pcoq.Symbol.nterm constr)))
                            (fun c k loc -> 
# 79 "plugins/ssrmatching/g_ssrmatching.mlg"
                                                   
    let pattern = mk_term k c None in
    if loc_of_cpattern pattern <> Some loc && k = InParens
    then mk_term Cpattern c None
    else pattern 
                                            )]))
        in ()

let (wit_lcpattern, lcpattern) = Tacentries.argument_extend ~name:"lcpattern" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (CLexer.terminal "Qed"))))
                                                            ((Pcoq.Symbol.nterm lconstr)))
                                                            (fun c _ loc -> 
# 93 "plugins/ssrmatching/g_ssrmatching.mlg"
                            mk_lterm c None 
                                                                    ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.val_tag (Genarg.topwit wit_cpattern));
                                 Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                         
# 90 "plugins/ssrmatching/g_ssrmatching.mlg"
                     glob_cpattern 
                                                         ));
                                 Tacentries.arg_subst = Tacentries.ArgSubstFun (
                                                        
# 90 "plugins/ssrmatching/g_ssrmatching.mlg"
                                                      subst_ssrterm 
                                                        );
                                 Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                         
# 89 "plugins/ssrmatching/g_ssrmatching.mlg"
                      interp_ssrterm 
                                                         );
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 91 "plugins/ssrmatching/g_ssrmatching.mlg"
                      pr_ssrterm 
                                                          ), (fun env sigma -> 
                                                          
# 92 "plugins/ssrmatching/g_ssrmatching.mlg"
                       pr_ssrterm 
                                                          ), (fun env sigma -> 
                                                          
# 88 "plugins/ssrmatching/g_ssrmatching.mlg"
                  pr_ssrterm 
                                                          ));
                                 }
let _ = (wit_lcpattern, lcpattern)

let _ = let () =
        Pcoq.grammar_extend lcpattern
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm ssrtermkind)))
                                            ((Pcoq.Symbol.nterm lconstr)))
                            (fun c k loc -> 
# 98 "plugins/ssrmatching/g_ssrmatching.mlg"
                                                     
    let pattern = mk_term k c None in
    if loc_of_cpattern pattern <> Some loc && k = InParens
    then mk_term Cpattern c None
    else pattern 
                                            )]))
        in ()

let (wit_ssrpatternarg, ssrpatternarg) = Tacentries.argument_extend ~name:"ssrpatternarg" 
                                         {
                                         Tacentries.arg_parsing = Vernacextend.Arg_alias (rpattern);
                                         Tacentries.arg_tag = Some
                                                              (Geninterp.val_tag (Genarg.topwit wit_rpattern));
                                         Tacentries.arg_intern = Tacentries.ArgInternWit (wit_rpattern);
                                         Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_rpattern);
                                         Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_rpattern);
                                         Tacentries.arg_printer = ((fun env sigma -> 
                                                                  
# 105 "plugins/ssrmatching/g_ssrmatching.mlg"
                                                             pr_rpattern 
                                                                  ), (fun env sigma -> 
                                                                  
# 105 "plugins/ssrmatching/g_ssrmatching.mlg"
                                                             pr_rpattern 
                                                                  ), (fun env sigma -> 
                                                                  
# 105 "plugins/ssrmatching/g_ssrmatching.mlg"
                                                             pr_rpattern 
                                                                  ));
                                         }
let _ = (wit_ssrpatternarg, ssrpatternarg)

let () = Tacentries.tactic_extend __coq_plugin_name "ssrinstoftpat" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ssrinstancesoftpat", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_cpattern), 
                            Tacentries.TyNil)), (fun arg ist -> 
# 110 "plugins/ssrmatching/g_ssrmatching.mlg"
                                              ssrinstancesof arg 
                                                )))]


# 113 "plugins/ssrmatching/g_ssrmatching.mlg"
 

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.set_keyword_state frozen_lexer ;;



