
# 11 "plugins/ltac/extratactics.mlg"
 

open Pp
open Genarg
open Stdarg
open Tacarg
open Extraargs
open Pltac
open Mod_subst
open Names
open CErrors
open Util
open Equality
open Tactypes
open Proofview.Notations
open Attributes
open Vernacextend



let __coq_plugin_name = "coq-core.plugins.ltac"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "assert_succeeds" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("assert_succeeds", Tacentries.TyArg (
                                                                   Extend.TUentryl (Genarg.get_arg_tag wit_tactic, 3), 
                                                                   Tacentries.TyNil)), 
           (fun tac ist -> 
# 35 "plugins/ltac/extratactics.mlg"
       Internals.assert_succeeds (Tacinterp.tactic_of_value ist tac) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "replace" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("replace", Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                           Tacentries.TyIdent ("with", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_clause), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_by_arg_tac), 
                                                           Tacentries.TyNil)))))), 
           (fun c1 c2 cl tac ist -> 
# 40 "plugins/ltac/extratactics.mlg"
     Internals.replace_in_clause_maybe_by ist c1 c2 cl tac 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "replace_term_left" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("replace", Tacentries.TyIdent ("->", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_clause), 
                                                           Tacentries.TyNil)))), 
           (fun c cl ist -> 
# 45 "plugins/ltac/extratactics.mlg"
       Internals.replace_term ist (Some true) c cl 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "replace_term_right" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("replace", Tacentries.TyIdent ("<-", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_clause), 
                                                           Tacentries.TyNil)))), 
           (fun c cl ist -> 
# 50 "plugins/ltac/extratactics.mlg"
       Internals.replace_term ist (Some false) c cl 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "replace_term" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("replace", Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_clause), 
                                                           Tacentries.TyNil))), 
           (fun c cl ist -> 
# 55 "plugins/ltac/extratactics.mlg"
       Internals.replace_term ist None c cl 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "simplify_eq" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("simplify_eq", Tacentries.TyNil), 
           (fun ist -> 
# 59 "plugins/ltac/extratactics.mlg"
                         dEq ~keep_proofs:None false None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("simplify_eq", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg), 
                                                              Tacentries.TyNil)), 
          (fun c ist -> 
# 60 "plugins/ltac/extratactics.mlg"
                                            Internals.mytclWithHoles (dEq ~keep_proofs:None) false c 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "esimplify_eq" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("esimplify_eq", Tacentries.TyNil), 
           (fun ist -> 
# 63 "plugins/ltac/extratactics.mlg"
                          dEq ~keep_proofs:None true None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("esimplify_eq", Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg), 
                                                               Tacentries.TyNil)), 
          (fun c ist -> 
# 64 "plugins/ltac/extratactics.mlg"
                                             Internals.mytclWithHoles (dEq ~keep_proofs:None) true c 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "discriminate" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("discriminate", Tacentries.TyNil), 
           (fun ist -> 
# 68 "plugins/ltac/extratactics.mlg"
                          discr_tac false None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("discriminate", Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg), 
                                                               Tacentries.TyNil)), 
          (fun c ist -> 
# 70 "plugins/ltac/extratactics.mlg"
      Internals.mytclWithHoles discr_tac false c 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ediscriminate" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ediscriminate", Tacentries.TyNil), 
           (fun ist -> 
# 73 "plugins/ltac/extratactics.mlg"
                           discr_tac true None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("ediscriminate", Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg), 
                                                                Tacentries.TyNil)), 
          (fun c ist -> 
# 75 "plugins/ltac/extratactics.mlg"
      Internals.mytclWithHoles discr_tac true c 
          )))]


# 78 "plugins/ltac/extratactics.mlg"
 

let isInjPat pat = match pat.CAst.v with IntroAction (IntroInjection _) -> Some pat.CAst.loc | _ -> None

let decode_inj_ipat ?loc = function
  (* For the "as [= pat1 ... patn ]" syntax *)
  | [{ CAst.v = IntroAction (IntroInjection ipat) }] -> ipat
  (* For the "as pat1 ... patn" syntax *)
  | ([] | [_]) as ipat -> ipat
  | pat1::pat2::_ as ipat ->
  (* To be sure that there is no confusion of syntax, we check that no [= ...] occurs
     in the non-singleton list of patterns *)
  match isInjPat pat1 with
  | Some _ -> user_err ?loc:pat2.CAst.loc (str "Unexpected pattern.")
  | None ->
  match List.map_filter isInjPat ipat with
  | loc :: _ -> user_err ?loc (str "Unexpected injection pattern.")
  | [] -> ipat



let () = Tacentries.tactic_extend __coq_plugin_name "injection" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("injection", Tacentries.TyNil), 
           (fun ist -> 
# 100 "plugins/ltac/extratactics.mlg"
                       injClause None None false None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("injection", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg), 
                                                            Tacentries.TyNil)), 
          (fun c ist -> 
# 101 "plugins/ltac/extratactics.mlg"
                                          Internals.mytclWithHoles (injClause None None) false c 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "einjection" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("einjection", Tacentries.TyNil), 
           (fun ist -> 
# 104 "plugins/ltac/extratactics.mlg"
                        injClause None None true None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("einjection", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg), 
                                                             Tacentries.TyNil)), 
          (fun c ist -> 
# 105 "plugins/ltac/extratactics.mlg"
                                           Internals.mytclWithHoles (injClause None None) true c 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "injection_as" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("injection", Tacentries.TyIdent ("as", 
                                                             Tacentries.TyArg (
                                                             Extend.TUlist0 (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_simple_intropattern)), 
                                                             Tacentries.TyNil))), 
           (fun ipat ist -> 
# 109 "plugins/ltac/extratactics.mlg"
      injClause None (Some (decode_inj_ipat ipat)) false None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("injection", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg), 
                                                            Tacentries.TyIdent ("as", 
                                                            Tacentries.TyArg (
                                                            Extend.TUlist0 (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_simple_intropattern)), 
                                                            Tacentries.TyNil)))), 
          (fun c ipat ist -> 
# 111 "plugins/ltac/extratactics.mlg"
      Internals.mytclWithHoles (injClause None (Some (decode_inj_ipat ipat))) false c 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "einjection_as" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("einjection", Tacentries.TyIdent ("as", 
                                                              Tacentries.TyArg (
                                                              Extend.TUlist0 (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_simple_intropattern)), 
                                                              Tacentries.TyNil))), 
           (fun ipat ist -> 
# 115 "plugins/ltac/extratactics.mlg"
      injClause None (Some (decode_inj_ipat ipat)) true None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("einjection", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg), 
                                                             Tacentries.TyIdent ("as", 
                                                             Tacentries.TyArg (
                                                             Extend.TUlist0 (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_simple_intropattern)), 
                                                             Tacentries.TyNil)))), 
          (fun c ipat ist -> 
# 117 "plugins/ltac/extratactics.mlg"
      Internals.mytclWithHoles (injClause None (Some (decode_inj_ipat ipat))) true c 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "simple_injection" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("simple", Tacentries.TyIdent ("injection", 
                                                          Tacentries.TyNil)), 
           (fun ist -> 
# 120 "plugins/ltac/extratactics.mlg"
                                simpleInjClause None false None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("simple", Tacentries.TyIdent ("injection", 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_destruction_arg), 
                                                         Tacentries.TyNil))), 
          (fun c ist -> 
# 121 "plugins/ltac/extratactics.mlg"
                                                   Internals.mytclWithHoles (simpleInjClause None) false c 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "dependent_rewrite" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("dependent", Tacentries.TyIdent ("rewrite", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyNil)))), 
           (fun b c ist -> 
# 125 "plugins/ltac/extratactics.mlg"
                                                     rewriteInConcl b c 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("dependent", Tacentries.TyIdent ("rewrite", 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyIdent ("in", 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                            Tacentries.TyNil)))))), 
          (fun b c id ist -> 
# 127 "plugins/ltac/extratactics.mlg"
         rewriteInHyp b c id 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "cut_rewrite" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("cutrewrite", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                              Tacentries.TyNil))), 
           (fun b eqn ist -> 
# 131 "plugins/ltac/extratactics.mlg"
                                              cutRewriteInConcl b eqn 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("cutrewrite", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyIdent ("in", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                             Tacentries.TyNil))))), 
          (fun b eqn id ist -> 
# 133 "plugins/ltac/extratactics.mlg"
         cutRewriteInHyp b eqn id 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "decompose_sum" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("decompose", Tacentries.TyIdent ("sum", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyNil))), 
           (fun c ist -> 
# 140 "plugins/ltac/extratactics.mlg"
                                       Elim.h_decompose_or c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "decompose_record" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("decompose", Tacentries.TyIdent ("record", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyNil))), 
           (fun c ist -> 
# 144 "plugins/ltac/extratactics.mlg"
                                          Elim.h_decompose_and c 
           )))]


# 150 "plugins/ltac/extratactics.mlg"
 

open Contradiction



let () = Tacentries.tactic_extend __coq_plugin_name "absurd" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("absurd", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil)), 
           (fun c ist -> 
# 157 "plugins/ltac/extratactics.mlg"
                              absurd c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "contradiction" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("contradiction", Tacentries.TyArg (
                                                                 Extend.TUopt (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr_with_bindings)), 
                                                                 Tacentries.TyNil)), 
           (fun c ist -> 
# 162 "plugins/ltac/extratactics.mlg"
      Internals.onSomeWithHoles contradiction c 
           )))]


# 168 "plugins/ltac/extratactics.mlg"
 

open Autorewrite



let () = Tacentries.tactic_extend __coq_plugin_name "autorewrite" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("autorewrite", Tacentries.TyIdent ("with", 
                                                               Tacentries.TyArg (
                                                               Extend.TUlist1 (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                               Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_clause), 
                                                               Tacentries.TyNil)))), 
           (fun l cl ist -> 
# 176 "plugins/ltac/extratactics.mlg"
      auto_multi_rewrite  l ( cl) 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("autorewrite", Tacentries.TyIdent ("with", 
                                                              Tacentries.TyArg (
                                                              Extend.TUlist1 (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_clause), 
                                                              Tacentries.TyIdent ("using", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                              Tacentries.TyNil)))))), 
          (fun l cl t ist -> 
# 178 "plugins/ltac/extratactics.mlg"
     
      auto_multi_rewrite_with (Tacinterp.tactic_of_value ist t) l cl
   
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "autorewrite_star" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("autorewrite", Tacentries.TyIdent ("*", 
                                                               Tacentries.TyIdent ("with", 
                                                               Tacentries.TyArg (
                                                               Extend.TUlist1 (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                               Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_clause), 
                                                               Tacentries.TyNil))))), 
           (fun l cl ist -> 
# 185 "plugins/ltac/extratactics.mlg"
      auto_multi_rewrite ~conds:AllMatches l cl 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("autorewrite", Tacentries.TyIdent ("*", 
                                                              Tacentries.TyIdent ("with", 
                                                              Tacentries.TyArg (
                                                              Extend.TUlist1 (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_clause), 
                                                              Tacentries.TyIdent ("using", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                              Tacentries.TyNil))))))), 
          (fun l cl t ist -> 
# 187 "plugins/ltac/extratactics.mlg"
    auto_multi_rewrite_with ~conds:AllMatches (Tacinterp.tactic_of_value ist t) l cl 
          )))]


# 193 "plugins/ltac/extratactics.mlg"
 

let rewrite_star ist clause orient occs c (tac : Geninterp.Val.t option) =
  let tac' = Option.map (fun t -> Tacinterp.tactic_of_value ist t, FirstSolved) tac in
  Internals.with_delayed_uconstr ist c
    (fun c -> general_rewrite ~where:clause ~l2r:orient occs ?tac:tac' ~freeze:true ~dep:true ~with_evars:true (c,NoBindings))



let () = Tacentries.tactic_extend __coq_plugin_name "rewrite_star" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("rewrite", Tacentries.TyIdent ("*", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                           Tacentries.TyIdent ("in", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                           Tacentries.TyIdent ("at", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_occurrences), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_by_arg_tac), 
                                                           Tacentries.TyNil))))))))), 
           (fun o c id occ tac ist -> 
# 204 "plugins/ltac/extratactics.mlg"
      rewrite_star ist (Some id) o (occurrences_of occ) c tac 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("rewrite", Tacentries.TyIdent ("*", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                          Tacentries.TyIdent ("at", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_occurrences), 
                                                          Tacentries.TyIdent ("in", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_by_arg_tac), 
                                                          Tacentries.TyNil))))))))), 
          (fun o c occ id tac ist -> 
# 206 "plugins/ltac/extratactics.mlg"
      rewrite_star ist (Some id) o (occurrences_of occ) c tac 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("rewrite", Tacentries.TyIdent ("*", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                          Tacentries.TyIdent ("in", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_by_arg_tac), 
                                                          Tacentries.TyNil))))))), 
          (fun o c id tac ist -> 
# 208 "plugins/ltac/extratactics.mlg"
      rewrite_star ist (Some id) o Locus.AllOccurrences c tac 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("rewrite", Tacentries.TyIdent ("*", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                          Tacentries.TyIdent ("at", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_occurrences), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_by_arg_tac), 
                                                          Tacentries.TyNil))))))), 
          (fun o c occ tac ist -> 
# 210 "plugins/ltac/extratactics.mlg"
      rewrite_star ist None o (occurrences_of occ) c tac 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("rewrite", Tacentries.TyIdent ("*", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_by_arg_tac), 
                                                          Tacentries.TyNil))))), 
          (fun o c tac ist -> 
# 212 "plugins/ltac/extratactics.mlg"
      rewrite_star ist None o Locus.AllOccurrences c tac 
          )))]


# 218 "plugins/ltac/extratactics.mlg"
 

let add_rewrite_hint ~locality ~poly bases ort t lcsr =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let f ce =
    let c, ctx = Constrintern.interp_constr env sigma ce in
    let c = EConstr.to_constr sigma c in
    let ctx =
      let ctx = UState.context_set ctx in
        if poly then ctx
        else (* This is a global universe context that shouldn't be
                refreshed at every use of the hint, declare it globally. *)
          (DeclareUctx.declare_universe_context ~poly:false ctx;
           Univ.ContextSet.empty)
    in
      CAst.make ?loc:(Constrexpr_ops.constr_loc ce) ((c, ctx), ort, Option.map (in_gen (rawwit wit_ltac)) t) in
  let eqs = List.map f lcsr in
  let add_hints base = add_rew_rules ~locality base eqs in
  List.iter add_hints bases

let classify_hint _ = VtSideff ([], VtLater)

let hint_rewrite_locality = Attributes.hint_locality ~default:default_hint_rewrite_locality



let () = Vernacextend.vernac_extend ~command:"HintRewrite" ~classifier:( classify_hint ) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Hint", 
                                     Vernacextend.TyTerminal ("Rewrite", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                     Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body o l bl
         (polymorphic, locality) = Vernacextend.vtdefault (fun () -> 
# 247 "plugins/ltac/extratactics.mlg"
    add_rewrite_hint ~locality ~poly:polymorphic bl o None l 
                                   ) in fun o
         l bl ?loc ~atts () -> coqpp_body o l bl
         (Attributes.parse Attributes.Notations.(polymorphic ++ hint_rewrite_locality) atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Hint", 
                                    Vernacextend.TyTerminal ("Rewrite", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                    Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                    Vernacextend.TyTerminal ("using", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                    Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                  Extend.TUlist0 (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                                  Vernacextend.TyNil)))))))), 
         (let coqpp_body o l t bl
         (polymorphic, locality) = Vernacextend.vtdefault (fun () -> 
# 250 "plugins/ltac/extratactics.mlg"
    add_rewrite_hint ~locality ~poly:polymorphic bl o (Some t) l 
                                   ) in fun o
         l t bl ?loc ~atts () -> coqpp_body o l t bl
         (Attributes.parse Attributes.Notations.(polymorphic ++ hint_rewrite_locality) atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Hint", 
                                    Vernacextend.TyTerminal ("Rewrite", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                    Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                    Vernacextend.TyNil)))), (let coqpp_body o
                                                            l
                                                            (polymorphic, locality) = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 252 "plugins/ltac/extratactics.mlg"
    add_rewrite_hint ~locality ~poly:polymorphic ["core"] o None l 
                                                            ) in fun o l
                                                            ?loc ~atts ()
                                                            -> coqpp_body o l
                                                            (Attributes.parse Attributes.Notations.(polymorphic ++ hint_rewrite_locality) atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Hint", 
                                    Vernacextend.TyTerminal ("Rewrite", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                    Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                    Vernacextend.TyTerminal ("using", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                    Vernacextend.TyNil)))))), (let coqpp_body o
                                                              l t
                                                              (polymorphic, locality) = 
                                                              Vernacextend.vtdefault (fun () -> 
                                                              
# 254 "plugins/ltac/extratactics.mlg"
    add_rewrite_hint ~locality ~poly:polymorphic ["core"] o (Some t) l 
                                                              ) in fun o l t
                                                              ?loc ~atts ()
                                                              -> coqpp_body o
                                                              l t
                                                              (Attributes.parse Attributes.Notations.(polymorphic ++ hint_rewrite_locality) atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "refine" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("refine", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                          Tacentries.TyNil)), 
           (fun c ist -> 
# 262 "plugins/ltac/extratactics.mlg"
     Internals.refine_tac ist ~simple:false ~with_classes:true c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "simple_refine" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("simple", Tacentries.TyIdent ("refine", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                          Tacentries.TyNil))), 
           (fun c ist -> 
# 267 "plugins/ltac/extratactics.mlg"
     Internals.refine_tac ist ~simple:true ~with_classes:true c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "notcs_refine" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("notypeclasses", Tacentries.TyIdent ("refine", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                                 Tacentries.TyNil))), 
           (fun c ist -> 
# 272 "plugins/ltac/extratactics.mlg"
     Internals.refine_tac ist ~simple:false ~with_classes:false c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "notcs_simple_refine" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("simple", Tacentries.TyIdent ("notypeclasses", 
                                                          Tacentries.TyIdent ("refine", 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_uconstr), 
                                                          Tacentries.TyNil)))), 
           (fun c ist -> 
# 277 "plugins/ltac/extratactics.mlg"
     Internals.refine_tac ist ~simple:true ~with_classes:false c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "solve_constraints" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("solve_constraints", 
                            Tacentries.TyNil), (fun ist -> 
# 282 "plugins/ltac/extratactics.mlg"
                               Refine.solve_constraints 
                                               )))]


# 288 "plugins/ltac/extratactics.mlg"
 

open Inv
open Leminv

let seff id = VtSideff ([id], VtLater)



let () = Vernacextend.vernac_extend ~command:"DeriveInversionClear"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Derive", 
                                     Vernacextend.TyTerminal ("Inversion_clear", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal ("with", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("Sort", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_sort_family), 
                                     Vernacextend.TyNil))))))), (let coqpp_body na
                                                                c s
                                                                polymorphic = 
                                                                Vernacextend.vtdefault (fun () -> 
                                                                
# 306 "plugins/ltac/extratactics.mlg"
      
      add_inversion_lemma_exn ~poly:polymorphic na c s false inv_clear_tac 
                                                                ) in fun na c
                                                                s
                                                                ?loc ~atts ()
                                                                -> coqpp_body na
                                                                c s
                                                                (Attributes.parse polymorphic atts)), Some 
         (fun na c s -> 
# 305 "plugins/ltac/extratactics.mlg"
       seff na 
         )));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Derive", 
                                    Vernacextend.TyTerminal ("Inversion_clear", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                    Vernacextend.TyTerminal ("with", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNil))))), (let coqpp_body na
                                                             c
                                                             polymorphic = 
                                                             Vernacextend.vtdefault (fun () -> 
                                                             
# 310 "plugins/ltac/extratactics.mlg"
      
      add_inversion_lemma_exn ~poly:polymorphic na c Sorts.InProp false inv_clear_tac 
                                                             ) in fun na c
                                                             ?loc ~atts ()
                                                             -> coqpp_body na
                                                             c
                                                             (Attributes.parse polymorphic atts)), Some 
         (fun na c -> 
# 309 "plugins/ltac/extratactics.mlg"
                                                                                   seff na 
         )))]

let () = Vernacextend.vernac_extend ~command:"DeriveInversion"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Derive", 
                                     Vernacextend.TyTerminal ("Inversion", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal ("with", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("Sort", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_sort_family), 
                                     Vernacextend.TyNil))))))), (let coqpp_body na
                                                                c s
                                                                polymorphic = 
                                                                Vernacextend.vtdefault (fun () -> 
                                                                
# 317 "plugins/ltac/extratactics.mlg"
      
      add_inversion_lemma_exn ~poly:polymorphic na c s false inv_tac 
                                                                ) in fun na c
                                                                s
                                                                ?loc ~atts ()
                                                                -> coqpp_body na
                                                                c s
                                                                (Attributes.parse polymorphic atts)), Some 
         (fun na c s -> 
# 316 "plugins/ltac/extratactics.mlg"
       seff na 
         )));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Derive", 
                                    Vernacextend.TyTerminal ("Inversion", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                    Vernacextend.TyTerminal ("with", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyNil))))), (let coqpp_body na
                                                             c
                                                             polymorphic = 
                                                             Vernacextend.vtdefault (fun () -> 
                                                             
# 321 "plugins/ltac/extratactics.mlg"
      
      add_inversion_lemma_exn ~poly:polymorphic na c Sorts.InProp false inv_tac 
                                                             ) in fun na c
                                                             ?loc ~atts ()
                                                             -> coqpp_body na
                                                             c
                                                             (Attributes.parse polymorphic atts)), Some 
         (fun na c -> 
# 320 "plugins/ltac/extratactics.mlg"
                                                                             seff na 
         )))]

let () = Vernacextend.vernac_extend ~command:"DeriveDependentInversion"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Derive", 
                                     Vernacextend.TyTerminal ("Dependent", 
                                     Vernacextend.TyTerminal ("Inversion", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal ("with", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("Sort", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_sort_family), 
                                     Vernacextend.TyNil)))))))), (let coqpp_body na
                                                                 c s
                                                                 polymorphic = 
                                                                 Vernacextend.vtdefault (fun () -> 
                                                                 
# 328 "plugins/ltac/extratactics.mlg"
      
      add_inversion_lemma_exn ~poly:polymorphic na c s true dinv_tac 
                                                                 ) in fun na
                                                                 c s
                                                                 ?loc ~atts ()
                                                                 -> coqpp_body na
                                                                 c s
                                                                 (Attributes.parse polymorphic atts)), Some 
         (fun na c s -> 
# 327 "plugins/ltac/extratactics.mlg"
       seff na 
         )))]

let () = Vernacextend.vernac_extend ~command:"DeriveDependentInversionClear"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Derive", 
                                     Vernacextend.TyTerminal ("Dependent", 
                                     Vernacextend.TyTerminal ("Inversion_clear", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal ("with", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("Sort", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_sort_family), 
                                     Vernacextend.TyNil)))))))), (let coqpp_body na
                                                                 c s
                                                                 polymorphic = 
                                                                 Vernacextend.vtdefault (fun () -> 
                                                                 
# 335 "plugins/ltac/extratactics.mlg"
      
      add_inversion_lemma_exn ~poly:polymorphic na c s true dinv_clear_tac 
                                                                 ) in fun na
                                                                 c s
                                                                 ?loc ~atts ()
                                                                 -> coqpp_body na
                                                                 c s
                                                                 (Attributes.parse polymorphic atts)), Some 
         (fun na c s -> 
# 334 "plugins/ltac/extratactics.mlg"
       seff na 
         )))]

let () = Tacentries.tactic_extend __coq_plugin_name "subst" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("subst", Tacentries.TyArg (
                                                         Extend.TUlist1 (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_hyp)), 
                                                         Tacentries.TyNil)), 
           (fun l ist -> 
# 343 "plugins/ltac/extratactics.mlg"
                                  subst l 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("subst", Tacentries.TyNil), 
          (fun ist -> 
# 344 "plugins/ltac/extratactics.mlg"
                   subst_all () 
          )))]


# 347 "plugins/ltac/extratactics.mlg"
 

let simple_subst_tactic_flags =
  { only_leibniz = true; rewrite_dependent_proof = false }



let () = Tacentries.tactic_extend __coq_plugin_name "simple_subst" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("simple", Tacentries.TyIdent ("subst", 
                                                          Tacentries.TyNil)), 
           (fun ist -> 
# 355 "plugins/ltac/extratactics.mlg"
                            subst_all ~flags:simple_subst_tactic_flags () 
           )))]


# 358 "plugins/ltac/extratactics.mlg"
 

open Evar_tactics



let () = Tacentries.tactic_extend __coq_plugin_name "evar" ~level:0 [(
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("evar", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_test_lpar_id_colon), 
                                                                    Tacentries.TyIdent ("(", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                    Tacentries.TyIdent (":", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_lconstr), 
                                                                    Tacentries.TyIdent (")", 
                                                                    Tacentries.TyNil))))))), 
                                                                    (fun _ id
                                                                    typ ist
                                                                    -> 
                                                                    
# 370 "plugins/ltac/extratactics.mlg"
                                                                        let_evar (Name.Name id) typ 
                                                                    )));
                                                                    (
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("evar", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Tacentries.TyNil)), 
                                                                    (fun typ
                                                                    ist -> 
                                                                    
# 371 "plugins/ltac/extratactics.mlg"
                              let_evar Name.Anonymous typ 
                                                                    )))]

let () = Tacentries.tactic_extend __coq_plugin_name "instantiate" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("instantiate", Tacentries.TyIdent ("(", 
                                                               Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                               Tacentries.TyIdent (":=", 
                                                               Tacentries.TyArg (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_lglob), 
                                                               Tacentries.TyIdent (")", 
                                                               Tacentries.TyNil)))))), 
           (fun id c ist -> 
# 376 "plugins/ltac/extratactics.mlg"
      instantiate_tac_by_name id c 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("instantiate", Tacentries.TyIdent ("(", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_integer), 
                                                              Tacentries.TyIdent (":=", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_lglob), 
                                                              Tacentries.TyIdent (")", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_hloc), 
                                                              Tacentries.TyNil))))))), 
          (fun i c hl ist -> 
# 378 "plugins/ltac/extratactics.mlg"
      instantiate_tac i c hl 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "instantiate_noarg" ~level:0 ~deprecation:( Deprecation.make ~since:"8.16" () ) 
         [(Tacentries.TyML (Tacentries.TyIdent ("instantiate", Tacentries.TyNil), 
           (fun ist -> 
# 382 "plugins/ltac/extratactics.mlg"
                         Proofview.tclUNIT () 
           )))]


# 388 "plugins/ltac/extratactics.mlg"
 

open Tactics
open Libobject

(* Registered lemmas are expected to be of the form
     x R y -> y == z -> x R z    (in the right table)
     x R y -> x == z -> z R y    (in the left table)
*)

let transitivity_right_table = Summary.ref [] ~name:"transitivity-steps-r"
let transitivity_left_table = Summary.ref [] ~name:"transitivity-steps-l"

(* [step] tries to apply a rewriting lemma; then apply [tac] intended to
   complete to proof of the last hypothesis (assumed to state an equality) *)

let step left x tac =
  let l =
    List.map (fun lem ->
      let lem = EConstr.of_constr lem in
      Tacticals.tclTHENLAST
        (apply_with_bindings (lem, ImplicitBindings [x]))
        tac)
      !(if left then transitivity_left_table else transitivity_right_table)
  in
  Tacticals.tclFIRST l

(* Main function to push lemmas in persistent environment *)

let cache_transitivity_lemma (left,lem) =
  if left then
    transitivity_left_table  := lem :: !transitivity_left_table
  else
    transitivity_right_table := lem :: !transitivity_right_table

let subst_transitivity_lemma (subst,(b,ref)) = (b,subst_mps subst ref)

let inTransitivity : bool * Constr.t -> obj =
  declare_object @@ global_object_nodischarge "TRANSITIVITY-STEPS"
    ~cache:cache_transitivity_lemma
    ~subst:(Some subst_transitivity_lemma)

(* Main entry points *)

let add_transitivity_lemma left lem =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let lem',ctx (*FIXME*) = Constrintern.interp_constr env sigma lem in
  let lem' = EConstr.to_constr sigma lem' in
  Lib.add_leaf (inTransitivity (left,lem'))



let () = Tacentries.tactic_extend __coq_plugin_name "stepl" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("stepl", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                         Tacentries.TyIdent ("by", 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                         Tacentries.TyNil)))), 
           (fun c tac ist -> 
# 444 "plugins/ltac/extratactics.mlg"
                                             step true c (Tacinterp.tactic_of_value ist tac) 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("stepl", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                        Tacentries.TyNil)), 
          (fun c ist -> 
# 445 "plugins/ltac/extratactics.mlg"
                            step true c (Proofview.tclUNIT ()) 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "stepr" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("stepr", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                         Tacentries.TyIdent ("by", 
                                                         Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                         Tacentries.TyNil)))), 
           (fun c tac ist -> 
# 449 "plugins/ltac/extratactics.mlg"
                                             step false c (Tacinterp.tactic_of_value ist tac) 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("stepr", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                        Tacentries.TyNil)), 
          (fun c ist -> 
# 450 "plugins/ltac/extratactics.mlg"
                            step false c (Proofview.tclUNIT ()) 
          )))]

let () = Vernacextend.vernac_extend ~command:"AddStepl" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Declare", 
                                     Vernacextend.TyTerminal ("Left", 
                                     Vernacextend.TyTerminal ("Step", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil)))), (let coqpp_body t
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 455 "plugins/ltac/extratactics.mlg"
      add_transitivity_lemma true t 
                                                                  ) in fun t
                                                             ?loc ~atts ()
                                                             -> coqpp_body t
                                                             (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"AddStepr" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Declare", 
                                     Vernacextend.TyTerminal ("Right", 
                                     Vernacextend.TyTerminal ("Step", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil)))), (let coqpp_body t
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 460 "plugins/ltac/extratactics.mlg"
      add_transitivity_lemma false t 
                                                                  ) in fun t
                                                             ?loc ~atts ()
                                                             -> coqpp_body t
                                                             (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "generalize_eqs" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("generalize_eqs", Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                  Tacentries.TyNil)), 
           (fun id ist -> 
# 467 "plugins/ltac/extratactics.mlg"
                                   abstract_generalize ~generalize_vars:false id 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "dep_generalize_eqs" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("dependent", Tacentries.TyIdent ("generalize_eqs", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                             Tacentries.TyNil))), 
           (fun id ist -> 
# 470 "plugins/ltac/extratactics.mlg"
                                               abstract_generalize ~generalize_vars:false ~force_dep:true id 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "generalize_eqs_vars" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("generalize_eqs_vars", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                            Tacentries.TyNil)), (fun id ist -> 
# 473 "plugins/ltac/extratactics.mlg"
                                        abstract_generalize ~generalize_vars:true id 
                                                )))]

let () = Tacentries.tactic_extend __coq_plugin_name "dep_generalize_eqs_vars" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("dependent", Tacentries.TyIdent ("generalize_eqs_vars", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                             Tacentries.TyNil))), 
           (fun id ist -> 
# 476 "plugins/ltac/extratactics.mlg"
                                                    abstract_generalize ~force_dep:true ~generalize_vars:true id 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "specialize_eqs" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("specialize_eqs", Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                  Tacentries.TyNil)), 
           (fun id ist -> 
# 484 "plugins/ltac/extratactics.mlg"
                                    specialize_eqs id 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "hresolve_core" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("hresolve_core", Tacentries.TyIdent ("(", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                 Tacentries.TyIdent (":=", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                 Tacentries.TyIdent (")", 
                                                                 Tacentries.TyIdent ("at", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                                 Tacentries.TyIdent ("in", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                 Tacentries.TyNil)))))))))), 
           (fun id c occ t ist -> 
# 488 "plugins/ltac/extratactics.mlg"
                                                                                                Internals.hResolve id c occ t 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("hresolve_core", Tacentries.TyIdent ("(", 
                                                                Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                Tacentries.TyIdent (":=", 
                                                                Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                Tacentries.TyIdent (")", 
                                                                Tacentries.TyIdent ("in", 
                                                                Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                Tacentries.TyNil)))))))), 
          (fun id c t ist -> 
# 489 "plugins/ltac/extratactics.mlg"
                                                                           Internals.hResolve_auto id c t 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "hget_evar" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("hget_evar", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_nat_or_var), 
                                                             Tacentries.TyNil)), 
           (fun n ist -> 
# 497 "plugins/ltac/extratactics.mlg"
                                     Evar_tactics.hget_evar n 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "destauto" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("destauto", Tacentries.TyNil), 
           (fun ist -> 
# 501 "plugins/ltac/extratactics.mlg"
                      Internals.destauto 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("destauto", Tacentries.TyIdent ("in", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                           Tacentries.TyNil))), 
          (fun id ist -> 
# 502 "plugins/ltac/extratactics.mlg"
                                   Internals.destauto_in id 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "transparent_abstract" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("transparent_abstract", 
                            Tacentries.TyArg (Extend.TUentryl (Genarg.get_arg_tag wit_tactic, 3), 
                            Tacentries.TyNil)), (fun t ist -> 
# 513 "plugins/ltac/extratactics.mlg"
                                             Proofview.Goal.enter begin fun gl ->
    Abstract.tclABSTRACT ~opaque:false None (Tacinterp.tactic_of_value ist t) end; 
                                                )));
         (Tacentries.TyML (Tacentries.TyIdent ("transparent_abstract", 
                           Tacentries.TyArg (Extend.TUentryl (Genarg.get_arg_tag wit_tactic, 3), 
                           Tacentries.TyIdent ("using", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                        Tacentries.TyNil)))), 
          (fun t id ist -> 
# 515 "plugins/ltac/extratactics.mlg"
                                                               Proofview.Goal.enter begin fun gl ->
    Abstract.tclABSTRACT ~opaque:false (Some id) (Tacinterp.tactic_of_value ist t) end; 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "constr_eq" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("constr_eq", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyNil))), 
           (fun x y ist -> 
# 522 "plugins/ltac/extratactics.mlg"
                                           Tactics.constr_eq ~strict:false x y 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "constr_eq_strict" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("constr_eq_strict", Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Tacentries.TyNil))), 
           (fun x y ist -> 
# 526 "plugins/ltac/extratactics.mlg"
                                                  Tactics.constr_eq ~strict:true x y 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "constr_eq_nounivs" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("constr_eq_nounivs", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                            Tacentries.TyNil))), (fun x y ist -> 
# 530 "plugins/ltac/extratactics.mlg"
                                                  
    Proofview.tclEVARMAP >>= fun sigma ->
    if EConstr.eq_constr_nounivs sigma x y then Proofview.tclUNIT () else Tacticals.tclFAIL (str "Not equal") 
                                                 )))]

let () = Tacentries.tactic_extend __coq_plugin_name "is_evar" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("is_evar", Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                           Tacentries.TyNil)), 
           (fun x ist -> 
# 536 "plugins/ltac/extratactics.mlg"
                               Internals.is_evar x 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "has_evar" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("has_evar", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyNil)), 
           (fun x ist -> 
# 540 "plugins/ltac/extratactics.mlg"
                                Internals.has_evar x 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "is_hyp" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("is_var", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil)), 
           (fun x ist -> 
# 544 "plugins/ltac/extratactics.mlg"
                              Internals.is_var x 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "is_fix" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("is_fix", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil)), 
           (fun x ist -> 
# 548 "plugins/ltac/extratactics.mlg"
                              Internals.is_fix x 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "is_cofix" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("is_cofix", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyNil)), 
           (fun x ist -> 
# 552 "plugins/ltac/extratactics.mlg"
                                Internals.is_cofix x 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "is_ind" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("is_ind", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil)), 
           (fun x ist -> 
# 556 "plugins/ltac/extratactics.mlg"
                              Internals.is_ind x 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "is_constructor" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("is_constructor", Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                  Tacentries.TyNil)), 
           (fun x ist -> 
# 560 "plugins/ltac/extratactics.mlg"
                                      Internals.is_constructor x 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "is_proj" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("is_proj", Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                           Tacentries.TyNil)), 
           (fun x ist -> 
# 564 "plugins/ltac/extratactics.mlg"
                               Internals.is_proj x 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "is_const" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("is_const", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyNil)), 
           (fun x ist -> 
# 568 "plugins/ltac/extratactics.mlg"
                                Internals.is_const x 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "shelve" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("shelve", Tacentries.TyNil), 
           (fun ist -> 
# 573 "plugins/ltac/extratactics.mlg"
                    Proofview.shelve 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "shelve_unifiable" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("shelve_unifiable", Tacentries.TyNil), 
           (fun ist -> 
# 580 "plugins/ltac/extratactics.mlg"
                              Proofview.shelve_unifiable 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "unshelve" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("unshelve", Tacentries.TyArg (
                                                            Extend.TUentryl (Genarg.get_arg_tag wit_tactic, 1), 
                                                            Tacentries.TyNil)), 
           (fun t ist -> 
# 585 "plugins/ltac/extratactics.mlg"
                                 Internals.unshelve ist t 
           )))]

let () = Vernacextend.vernac_extend ~command:"Unshelve"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Unshelve", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtmodifyproof (
                                                          
# 592 "plugins/ltac/extratactics.mlg"
       fun ~pstate -> Declare.Proof.map ~f:(fun p  -> Proof.unshelve p) pstate  
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), Some 
         
# 591 "plugins/ltac/extratactics.mlg"
       classify_as_proofstep 
         ))]

let () = Tacentries.tactic_extend __coq_plugin_name "give_up" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("give_up", Tacentries.TyNil), 
           (fun ist -> 
# 600 "plugins/ltac/extratactics.mlg"
      Proofview.give_up 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "cycle" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("cycle", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), 
                                                         Tacentries.TyNil)), 
           (fun n ist -> 
# 605 "plugins/ltac/extratactics.mlg"
                                 Proofview.cycle n 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "swap" ~level:0 [(
                                                                    Tacentries.TyML (
                                                                    Tacentries.TyIdent ("swap", 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), 
                                                                    Tacentries.TyArg (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_int_or_var), 
                                                                    Tacentries.TyNil))), 
                                                                    (fun i j
                                                                    ist -> 
                                                                    
# 610 "plugins/ltac/extratactics.mlg"
                                              Proofview.swap i j 
                                                                    )))]

let () = Tacentries.tactic_extend __coq_plugin_name "revgoals" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("revgoals", Tacentries.TyNil), 
           (fun ist -> 
# 615 "plugins/ltac/extratactics.mlg"
                      Proofview.revgoals 
           )))]


# 618 "plugins/ltac/extratactics.mlg"
 

type cmp =
  | Eq
  | Lt | Le
  | Gt | Ge

type 'i test =
  | Test of cmp * 'i * 'i

let pr_cmp = function
  | Eq -> Pp.str"="
  | Lt -> Pp.str"<"
  | Le -> Pp.str"<="
  | Gt -> Pp.str">"
  | Ge -> Pp.str">="

let pr_cmp' _prc _prlc _prt = pr_cmp

let pr_test_gen f (Test(c,x,y)) =
  Pp.(f x ++ pr_cmp c ++ f y)

let pr_test = pr_test_gen (Pputils.pr_or_var Pp.int)

let pr_test' _prc _prlc _prt = pr_test

let pr_itest = pr_test_gen Pp.int

let pr_itest' _prc _prlc _prt = pr_itest



let (wit_comparison, comparison) = Tacentries.argument_extend ~name:"comparison" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal ">="))))
                                                              (fun _ loc -> 
# 655 "plugins/ltac/extratactics.mlg"
                Ge 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal ">"))))
                                                             (fun _ loc -> 
# 654 "plugins/ltac/extratactics.mlg"
                Gt 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "<="))))
                                                             (fun _ loc -> 
# 653 "plugins/ltac/extratactics.mlg"
                Le 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "<"))))
                                                             (fun _ loc -> 
# 652 "plugins/ltac/extratactics.mlg"
                Lt 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "="))))
                                                             (fun _ loc -> 
# 651 "plugins/ltac/extratactics.mlg"
                Eq 
                                                                    ))]);
                                   Tacentries.arg_tag = None;
                                   Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                   Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                   Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 650 "plugins/ltac/extratactics.mlg"
                                        pr_cmp' 
                                                            ), (fun env sigma -> 
                                                            
# 650 "plugins/ltac/extratactics.mlg"
                                        pr_cmp' 
                                                            ), (fun env sigma -> 
                                                            
# 650 "plugins/ltac/extratactics.mlg"
                                        pr_cmp' 
                                                            ));
                                   }
let _ = (wit_comparison, comparison)


# 658 "plugins/ltac/extratactics.mlg"
 

let interp_test ist env sigma = function
  | Test (c,x,y) ->
      Test(c,Tacinterp.interp_int_or_var ist x,Tacinterp.interp_int_or_var ist y)



let (wit_test, test) = Tacentries.argument_extend ~name:"test" {
                                                               Tacentries.arg_parsing = 
                                                               Vernacextend.Arg_rules (
                                                               [(Pcoq.Production.make
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm int_or_var)))
                                                                 ((Pcoq.Symbol.nterm comparison)))
                                                                 ((Pcoq.Symbol.nterm int_or_var)))
                                                                 (fun y c x
                                                                 loc -> 
                                                                 
# 671 "plugins/ltac/extratactics.mlg"
                                                     Test(c,x,y) 
                                                                 ))]);
                                                               Tacentries.arg_tag = 
                                                               None;
                                                               Tacentries.arg_intern = 
                                                               Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                                               Tacentries.arg_subst = 
                                                               Tacentries.ArgSubstFun (fun s v -> v);
                                                               Tacentries.arg_interp = 
                                                               Tacentries.ArgInterpSimple (
                                                               
# 668 "plugins/ltac/extratactics.mlg"
                   interp_test 
                                                               );
                                                               Tacentries.arg_printer = 
                                                               ((fun env sigma -> 
                                                               
# 669 "plugins/ltac/extratactics.mlg"
                   pr_test' 
                                                               ), (fun env sigma -> 
                                                               
# 670 "plugins/ltac/extratactics.mlg"
                    pr_test' 
                                                               ), (fun env sigma -> 
                                                               
# 667 "plugins/ltac/extratactics.mlg"
               pr_itest' 
                                                               ));
                                                               }
let _ = (wit_test, test)


# 674 "plugins/ltac/extratactics.mlg"
 

let interp_cmp = function
  | Eq -> Int.equal
  | Lt -> ((<):int->int->bool)
  | Le -> ((<=):int->int->bool)
  | Gt -> ((>):int->int->bool)
  | Ge -> ((>=):int->int->bool)

let run_test = function
  | Test(c,x,y) -> interp_cmp c x y

let guard tst =
  if run_test tst then
    Proofview.tclUNIT ()
  else
    let msg = Pp.(str"Condition not satisfied:"++ws 1++(pr_itest tst)) in
    Tacticals.tclZEROMSG msg



let () = Tacentries.tactic_extend __coq_plugin_name "guard" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("guard", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_test), 
                                                         Tacentries.TyNil)), 
           (fun tst ist -> 
# 696 "plugins/ltac/extratactics.mlg"
                             guard tst 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "decompose" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("decompose", Tacentries.TyIdent ("[", 
                                                             Tacentries.TyArg (
                                                             Extend.TUlist1 (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                                             Tacentries.TyIdent ("]", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyNil))))), 
           (fun l c ist -> 
# 700 "plugins/ltac/extratactics.mlg"
                                                           Internals.decompose l c 
           )))]

let () = Vernacextend.vernac_extend ~command:"Declare_keys" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Declare", 
                                     Vernacextend.TyTerminal ("Equivalent", 
                                     Vernacextend.TyTerminal ("Keys", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil))))), (let coqpp_body c
                                                              c'
                                                              () = Vernacextend.vtdefault (fun () -> 
                                                                   
# 706 "plugins/ltac/extratactics.mlg"
                                                              Internals.declare_equivalent_keys c c' 
                                                                   ) in fun c
                                                              c'
                                                              ?loc ~atts ()
                                                              -> coqpp_body c
                                                              c'
                                                              (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Print_keys" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                     Vernacextend.TyTerminal ("Equivalent", 
                                     Vernacextend.TyTerminal ("Keys", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 710 "plugins/ltac/extratactics.mlg"
                                       Feedback.msg_notice (Keys.pr_keys Printer.pr_global) 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"OptimizeProof"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Optimize", 
                                     Vernacextend.TyTerminal ("Proof", 
                                     Vernacextend.TyNil)), (let coqpp_body () = 
                                                           Vernacextend.vtmodifyproof (
                                                           
# 715 "plugins/ltac/extratactics.mlg"
    fun ~pstate -> Declare.Proof.compact pstate 
                                                           ) in fun ?loc ~atts ()
                                                           -> coqpp_body (Attributes.unsupported_attributes atts)), Some 
         
# 714 "plugins/ltac/extratactics.mlg"
                                         classify_as_proofstep 
         ));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Optimize", 
                                    Vernacextend.TyTerminal ("Heap", 
                                    Vernacextend.TyNil)), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 717 "plugins/ltac/extratactics.mlg"
    Gc.compact () 
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), Some 
         
# 716 "plugins/ltac/extratactics.mlg"
                             classify_as_proofstep 
         ))]

let () = Tacentries.tactic_extend __coq_plugin_name "optimize_heap" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("optimize_heap", Tacentries.TyNil), 
           (fun ist -> 
# 721 "plugins/ltac/extratactics.mlg"
                           Internals.tclOPTIMIZE_HEAP 
           )))]

let () = Vernacextend.vernac_extend ~command:"infoH" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("infoH", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                     Vernacextend.TyNil)), (let coqpp_body tac
                                                           () = Vernacextend.vtreadproof (
                                                                
# 725 "plugins/ltac/extratactics.mlg"
                                                Internals.infoH tac 
                                                                ) in fun tac
                                                           ?loc ~atts ()
                                                           -> coqpp_body tac
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "with_strategy" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("with_strategy", Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_strategy_level_or_var), 
                                                                 Tacentries.TyIdent ("[", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_smart_global)), 
                                                                 Tacentries.TyIdent ("]", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentryl (Genarg.get_arg_tag wit_tactic, 3), 
                                                                 Tacentries.TyNil)))))), 
           (fun v q tac ist -> 
# 731 "plugins/ltac/extratactics.mlg"
                                                                                                
  with_set_strategy [(v, q)] (Tacinterp.tactic_of_value ist tac)

           )))]

