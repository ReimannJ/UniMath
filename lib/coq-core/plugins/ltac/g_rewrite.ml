
# 13 "plugins/ltac/g_rewrite.mlg"
 

open Names
open Locus
open Constrexpr
open Glob_term
open Genintern
open Geninterp
open Extraargs
open Rewrite
open ComRewrite
open Stdarg
open Tactypes
open Pcoq.Prim
open Pcoq.Constr
open Pvernac.Vernac_
open Pltac
open Vernacextend



let __coq_plugin_name = "coq-core.plugins.ltac"
let _ = Mltop.add_known_module __coq_plugin_name

# 36 "plugins/ltac/g_rewrite.mlg"
 

type constr_expr_with_bindings = constr_expr with_bindings
type glob_constr_with_bindings = glob_constr_and_expr with_bindings
type glob_constr_with_bindings_sign = interp_sign * glob_constr_and_expr with_bindings

let pr_glob_constr_with_bindings_sign env sigma _ _ _ (ge : glob_constr_with_bindings_sign) =
  Printer.pr_glob_constr_env env sigma (fst (fst (snd ge)))
let pr_glob_constr_with_bindings env sigma _ _ _ (ge : glob_constr_with_bindings) =
  Printer.pr_glob_constr_env env sigma (fst (fst ge))
let pr_constr_expr_with_bindings env sigma prc _ _ (ge : constr_expr_with_bindings) = prc env sigma (fst ge)
let interp_glob_constr_with_bindings ist _ _ c = (ist, c)
let glob_glob_constr_with_bindings ist l = Tacintern.intern_constr_with_bindings ist l
let subst_glob_constr_with_bindings s c =
  Tacsubst.subst_glob_with_bindings s c



let (wit_glob_constr_with_bindings, glob_constr_with_bindings) = Tacentries.argument_extend ~name:"glob_constr_with_bindings" 
                                                                 {
                                                                 Tacentries.arg_parsing = 
                                                                 Vernacextend.Arg_alias (constr_with_bindings);
                                                                 Tacentries.arg_tag = 
                                                                 None;
                                                                 Tacentries.arg_intern = 
                                                                 Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                                 
# 58 "plugins/ltac/g_rewrite.mlg"
                    glob_glob_constr_with_bindings 
                                                                 ));
                                                                 Tacentries.arg_subst = 
                                                                 Tacentries.ArgSubstFun (
                                                                 
# 59 "plugins/ltac/g_rewrite.mlg"
                     subst_glob_constr_with_bindings 
                                                                 );
                                                                 Tacentries.arg_interp = 
                                                                 Tacentries.ArgInterpSimple (
                                                                 
# 57 "plugins/ltac/g_rewrite.mlg"
                     interp_glob_constr_with_bindings 
                                                                 );
                                                                 Tacentries.arg_printer = 
                                                                 ((fun env sigma -> 
                                                                 
# 61 "plugins/ltac/g_rewrite.mlg"
                     pr_constr_expr_with_bindings env sigma 
                                                                 ), (fun env sigma -> 
                                                                 
# 62 "plugins/ltac/g_rewrite.mlg"
                      pr_glob_constr_with_bindings env sigma 
                                                                 ), (fun env sigma -> 
                                                                 
# 55 "plugins/ltac/g_rewrite.mlg"
                 pr_glob_constr_with_bindings_sign env sigma 
                                                                 ));
                                                                 }
let _ = (wit_glob_constr_with_bindings, glob_constr_with_bindings)


# 67 "plugins/ltac/g_rewrite.mlg"
 

type raw_strategy = (constr_expr, Tacexpr.raw_red_expr) strategy_ast
type glob_strategy = (glob_constr_and_expr, Tacexpr.glob_red_expr) strategy_ast

let interp_strategy ist env sigma s =
  let interp_redexpr r = fun env sigma -> Tacinterp.interp_red_expr ist env sigma r in
  let interp_constr c = (fst c, fun env sigma -> Tacinterp.interp_open_constr ist env sigma c) in
  let s = map_strategy interp_constr interp_redexpr s in
  strategy_of_ast s

let glob_strategy ist s = map_strategy (Tacintern.intern_constr ist) (Tacintern.intern_red_expr ist) s
let subst_strategy s str = str

let pr_strategy _ _ _ (s : strategy) = Pp.str "<strategy>"
let pr_raw_strategy env sigma prc prlc _ (s : raw_strategy) =
  let prr = Pptactic.pr_red_expr env sigma (prc, prlc, Pputils.pr_or_by_notation Libnames.pr_qualid, prc) in
  Rewrite.pr_strategy (prc env sigma) prr s
let pr_glob_strategy env sigma prc prlc _ (s : glob_strategy) =
  let prpat env sigma (_,c,_) = prc env sigma c in
  let prcst = Pputils.pr_or_var Pptactic.(pr_and_short_name (pr_evaluable_reference_env env)) in
  let prr = Pptactic.pr_red_expr env sigma (prc, prlc, prcst, prpat) in
  Rewrite.pr_strategy (prc env sigma) prr s



let (wit_rewstrategy, rewstrategy) = Tacentries.argument_extend ~name:"rewstrategy" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "fold"))))
                                                                ((Pcoq.Symbol.nterm constr)))
                                                                (fun c _
                                                                loc -> 
                                                                
# 125 "plugins/ltac/g_rewrite.mlg"
                              StratFold c 
                                                                ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "eval"))))
                                                               ((Pcoq.Symbol.nterm red_expr)))
                                                               (fun r _
                                                               loc -> 
                                                               
# 124 "plugins/ltac/g_rewrite.mlg"
                                StratEval r 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "terms"))))
                                                               ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm constr))))
                                                               (fun h _
                                                               loc -> 
                                                               
# 123 "plugins/ltac/g_rewrite.mlg"
                                    StratTerms h 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "hints"))))
                                                               ((Pcoq.Symbol.nterm preident)))
                                                               (fun h _
                                                               loc -> 
                                                               
# 122 "plugins/ltac/g_rewrite.mlg"
                                 StratHints (false, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "old_hints"))))
                                                               ((Pcoq.Symbol.nterm preident)))
                                                               (fun h _
                                                               loc -> 
                                                               
# 121 "plugins/ltac/g_rewrite.mlg"
                                     StratHints (true, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "choice"))))
                                                               ((Pcoq.Symbol.list1 (Pcoq.Symbol.self))))
                                                               (fun h _
                                                               loc -> 
                                                               
# 120 "plugins/ltac/g_rewrite.mlg"
                                             StratNAry (Choice, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                               (Pcoq.Symbol.self))
                                                               ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                               (fun _ h _
                                                               loc -> 
                                                               
# 119 "plugins/ltac/g_rewrite.mlg"
                                    h 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               (Pcoq.Symbol.self))
                                                               ((Pcoq.Symbol.token (CLexer.terminal ";"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h' _ h
                                                               loc -> 
                                                               
# 118 "plugins/ltac/g_rewrite.mlg"
                                                StratBinary (Compose, h, h') 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "repeat"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 117 "plugins/ltac/g_rewrite.mlg"
                                     StratUnary (Repeat, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "any"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 116 "plugins/ltac/g_rewrite.mlg"
                                  StratUnary (Any, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "try"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 115 "plugins/ltac/g_rewrite.mlg"
                                  StratUnary (Try, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "progress"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 114 "plugins/ltac/g_rewrite.mlg"
                                       StratUnary (Progress, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "refl"))))
                                                               (fun _ loc ->
                                                               
# 113 "plugins/ltac/g_rewrite.mlg"
                    StratRefl 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "fail"))))
                                                               (fun _ loc ->
                                                               
# 112 "plugins/ltac/g_rewrite.mlg"
                    StratFail 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "id"))))
                                                               (fun _ loc ->
                                                               
# 111 "plugins/ltac/g_rewrite.mlg"
                  StratId 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "topdown"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 110 "plugins/ltac/g_rewrite.mlg"
                                      StratUnary(Topdown, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "bottomup"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 109 "plugins/ltac/g_rewrite.mlg"
                                       StratUnary(Bottomup, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "outermost"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 108 "plugins/ltac/g_rewrite.mlg"
                                        StratUnary(Outermost, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "innermost"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 107 "plugins/ltac/g_rewrite.mlg"
                                        StratUnary(Innermost, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "subterm"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 106 "plugins/ltac/g_rewrite.mlg"
                                      StratUnary (Subterm, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "subterms"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun h _
                                                               loc -> 
                                                               
# 105 "plugins/ltac/g_rewrite.mlg"
                                       StratUnary (Subterms, h) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "<-"))))
                                                               ((Pcoq.Symbol.nterm constr)))
                                                               (fun c _
                                                               loc -> 
                                                               
# 104 "plugins/ltac/g_rewrite.mlg"
                            StratConstr (c, false) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm glob)))
                                                               (fun c loc ->
                                                               
# 103 "plugins/ltac/g_rewrite.mlg"
                     StratConstr (c, true) 
                                                               ))]);
                                     Tacentries.arg_tag = None;
                                     Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                             
# 97 "plugins/ltac/g_rewrite.mlg"
                    glob_strategy 
                                                             ));
                                     Tacentries.arg_subst = Tacentries.ArgSubstFun (
                                                            
# 98 "plugins/ltac/g_rewrite.mlg"
                     subst_strategy 
                                                            );
                                     Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                             
# 96 "plugins/ltac/g_rewrite.mlg"
                     interp_strategy 
                                                             );
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 100 "plugins/ltac/g_rewrite.mlg"
                     pr_raw_strategy env sigma 
                                                              ), (fun env sigma -> 
                                                              
# 101 "plugins/ltac/g_rewrite.mlg"
                      pr_glob_strategy env sigma 
                                                              ), (fun env sigma -> 
                                                              
# 94 "plugins/ltac/g_rewrite.mlg"
                 pr_strategy 
                                                              ));
                                     }
let _ = (wit_rewstrategy, rewstrategy)


# 130 "plugins/ltac/g_rewrite.mlg"
 

let db_strat db = StratUnary (Topdown, StratHints (false, db))
let cl_rewrite_clause_db ist db = cl_rewrite_clause_strat (strategy_of_ast (db_strat db))

let cl_rewrite_clause (ist, c) b occ cl =
  let c env sigma = Tacinterp.interp_open_constr_with_bindings ist env sigma c in
  cl_rewrite_clause c b occ cl



let () = Tacentries.tactic_extend __coq_plugin_name "rewrite_strat" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("rewrite_strat", Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_rewstrategy), 
                                                                 Tacentries.TyIdent ("in", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                 Tacentries.TyNil)))), 
           (fun s id ist -> 
# 142 "plugins/ltac/g_rewrite.mlg"
                                                       cl_rewrite_clause_strat s (Some id) 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("rewrite_strat", Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_rewstrategy), 
                                                                Tacentries.TyNil)), 
          (fun s ist -> 
# 143 "plugins/ltac/g_rewrite.mlg"
                                          cl_rewrite_clause_strat s None 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("rewrite_db", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_preident), 
                                                             Tacentries.TyIdent ("in", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                             Tacentries.TyNil)))), 
          (fun db id ist -> 
# 144 "plugins/ltac/g_rewrite.mlg"
                                                  cl_rewrite_clause_db ist db (Some id) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("rewrite_db", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_preident), 
                                                             Tacentries.TyNil)), 
          (fun db ist -> 
# 145 "plugins/ltac/g_rewrite.mlg"
                                     cl_rewrite_clause_db ist db None 
          )))]


# 148 "plugins/ltac/g_rewrite.mlg"
 

let clsubstitute o c =
  Proofview.Goal.enter begin fun gl ->
  let is_tac id = match DAst.get (fst (fst (snd c))) with GVar id' when Id.equal id' id -> true | _ -> false in
  let hyps = Tacmach.pf_ids_of_hyps gl in
    Tacticals.tclMAP
      (fun cl ->
        match cl with
          | Some id when is_tac id -> Tacticals.tclIDTAC
          | _ -> cl_rewrite_clause c o AllOccurrences cl)
      (None :: List.map (fun id -> Some id) hyps)
  end



let () = Tacentries.tactic_extend __coq_plugin_name "substitute" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("substitute", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_glob_constr_with_bindings), 
                                                              Tacentries.TyNil))), 
           (fun o c ist -> 
# 165 "plugins/ltac/g_rewrite.mlg"
                                                               clsubstitute o c 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "setoid_rewrite" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("setoid_rewrite", Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                                  Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_glob_constr_with_bindings), 
                                                                  Tacentries.TyNil))), 
           (fun o c ist -> 
# 173 "plugins/ltac/g_rewrite.mlg"
        cl_rewrite_clause c o AllOccurrences None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("setoid_rewrite", Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_glob_constr_with_bindings), 
                                                                 Tacentries.TyIdent ("in", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                 Tacentries.TyNil))))), 
          (fun o c id ist -> 
# 175 "plugins/ltac/g_rewrite.mlg"
        cl_rewrite_clause c o AllOccurrences (Some id) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("setoid_rewrite", Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_glob_constr_with_bindings), 
                                                                 Tacentries.TyIdent ("at", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_occurrences), 
                                                                 Tacentries.TyNil))))), 
          (fun o c occ ist -> 
# 177 "plugins/ltac/g_rewrite.mlg"
        cl_rewrite_clause c o (occurrences_of occ) None 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("setoid_rewrite", Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_glob_constr_with_bindings), 
                                                                 Tacentries.TyIdent ("at", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_occurrences), 
                                                                 Tacentries.TyIdent ("in", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                 Tacentries.TyNil))))))), 
          (fun o c occ id ist -> 
# 179 "plugins/ltac/g_rewrite.mlg"
        cl_rewrite_clause c o (occurrences_of occ) (Some id) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("setoid_rewrite", Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_orient), 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_glob_constr_with_bindings), 
                                                                 Tacentries.TyIdent ("in", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                 Tacentries.TyIdent ("at", 
                                                                 Tacentries.TyArg (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_occurrences), 
                                                                 Tacentries.TyNil))))))), 
          (fun o c id occ ist -> 
# 181 "plugins/ltac/g_rewrite.mlg"
        cl_rewrite_clause c o (occurrences_of occ) (Some id) 
          )))]


# 184 "plugins/ltac/g_rewrite.mlg"
 

let declare_relation atts a ?binders aeq n refl symm trans =
  declare_relation atts a ?binders aeq n.CAst.v refl symm trans



let () = Vernacextend.vernac_extend ~command:"AddRelation" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Relation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("reflexivity", 
                                     Vernacextend.TyTerminal ("proved", 
                                     Vernacextend.TyTerminal ("by", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("symmetry", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))))))))))), 
         (let coqpp_body a aeq lemma1 lemma2 n
         atts = Vernacextend.vtdefault (fun () -> 
# 194 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts a aeq n (Some lemma1) (Some lemma2) None 
                ) in fun a
         aeq lemma1 lemma2 n ?loc ~atts () -> coqpp_body a aeq lemma1 lemma2
         n (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("reflexivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))))))), 
         (let coqpp_body a aeq lemma1 n
         atts = Vernacextend.vtdefault (fun () -> 
# 198 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts a aeq n (Some lemma1) None None 
                ) in fun a
         aeq lemma1 n ?loc ~atts () -> coqpp_body a aeq lemma1 n
         (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body a aeq n
         atts = Vernacextend.vtdefault (fun () -> 
# 200 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts a aeq n None None None 
                ) in fun a
         aeq n ?loc ~atts () -> coqpp_body a aeq n
         (Attributes.parse rewrite_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"AddRelation2" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Relation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("symmetry", 
                                     Vernacextend.TyTerminal ("proved", 
                                     Vernacextend.TyTerminal ("by", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))))))), 
         (let coqpp_body a aeq lemma2 n
         atts = Vernacextend.vtdefault (fun () -> 
# 206 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts a aeq n None (Some lemma2) None 
                ) in fun a
         aeq lemma2 n ?loc ~atts () -> coqpp_body a aeq lemma2 n
         (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("symmetry", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("transitivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))))))))))), 
         (let coqpp_body a aeq lemma2 lemma3 n
         atts = Vernacextend.vtdefault (fun () -> 
# 208 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts a aeq n None (Some lemma2) (Some lemma3) 
                ) in fun a
         aeq lemma2 lemma3 n ?loc ~atts () -> coqpp_body a aeq lemma2 lemma3
         n (Attributes.parse rewrite_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"AddRelation3" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Relation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("reflexivity", 
                                     Vernacextend.TyTerminal ("proved", 
                                     Vernacextend.TyTerminal ("by", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("transitivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))))))))))), 
         (let coqpp_body a aeq lemma1 lemma3 n
         atts = Vernacextend.vtdefault (fun () -> 
# 214 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts a aeq n (Some lemma1) None (Some lemma3) 
                ) in fun a
         aeq lemma1 lemma3 n ?loc ~atts () -> coqpp_body a aeq lemma1 lemma3
         n (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("reflexivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("symmetry", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("transitivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))))))))))))))), 
         (let coqpp_body a aeq lemma1 lemma2 lemma3 n
         atts = Vernacextend.vtdefault (fun () -> 
# 218 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts a aeq n (Some lemma1) (Some lemma2) (Some lemma3) 
                ) in fun a
         aeq lemma1 lemma2 lemma3 n ?loc ~atts () -> coqpp_body a aeq lemma1
         lemma2 lemma3 n (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("transitivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))))))), 
         (let coqpp_body a aeq lemma3 n
         atts = Vernacextend.vtdefault (fun () -> 
# 221 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts a aeq n None None (Some lemma3) 
                ) in fun a
         aeq lemma3 n ?loc ~atts () -> coqpp_body a aeq lemma3 n
         (Attributes.parse rewrite_attributes atts)), None))]


# 224 "plugins/ltac/g_rewrite.mlg"
 

type binders_argtype = local_binder_expr list

let wit_binders =
 (Genarg.create_arg "binders" : binders_argtype Genarg.uniform_genarg_type)

let binders = Pcoq.create_generic_entry2 "binders" (Genarg.rawwit wit_binders)

let () =
  let raw_printer env sigma _ _ _ l = Pp.pr_non_empty_arg (Ppconstr.pr_binders env sigma) l in
  Pptactic.declare_extra_vernac_genarg_pprule wit_binders raw_printer



let _ = let () = assert (Pcoq.Entry.is_empty binders) in
        let () =
        Pcoq.grammar_extend binders
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Pcoq.Constr.binders)))
                                  (fun b loc -> 
# 242 "plugins/ltac/g_rewrite.mlg"
                                     b 
                                                )])]))
        in ()

let () = Vernacextend.vernac_extend ~command:"AddParametricRelation" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Parametric", 
                                     Vernacextend.TyTerminal ("Relation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                     Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("reflexivity", 
                                                                   Vernacextend.TyTerminal ("proved", 
                                                                   Vernacextend.TyTerminal ("by", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("symmetry", 
                                                                   Vernacextend.TyTerminal ("proved", 
                                                                   Vernacextend.TyTerminal ("by", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                   Vernacextend.TyNil))))))))))))))))), 
         (let coqpp_body b a aeq lemma1 lemma2 n
         atts = Vernacextend.vtdefault (fun () -> 
# 249 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts ~binders:b a aeq n (Some lemma1) (Some lemma2) None 
                ) in fun b
         a aeq lemma1 lemma2 n ?loc ~atts () -> coqpp_body b a aeq lemma1
         lemma2 n (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Parametric", 
                                                                    Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                                                    Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("reflexivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))))))))))))), 
         (let coqpp_body b a aeq lemma1 n
         atts = Vernacextend.vtdefault (fun () -> 
# 253 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts ~binders:b a aeq n (Some lemma1) None None 
                ) in fun b
         a aeq lemma1 n ?loc ~atts () -> coqpp_body b a aeq lemma1 n
         (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Parametric", 
                                                                    Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                                                    Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))))))))), 
         (let coqpp_body b a aeq n
         atts = Vernacextend.vtdefault (fun () -> 
# 255 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts ~binders:b a aeq n None None None 
                ) in fun b
         a aeq n ?loc ~atts () -> coqpp_body b a aeq n
         (Attributes.parse rewrite_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"AddParametricRelation2" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Parametric", 
                                     Vernacextend.TyTerminal ("Relation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                     Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("symmetry", 
                                                                   Vernacextend.TyTerminal ("proved", 
                                                                   Vernacextend.TyTerminal ("by", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                   Vernacextend.TyNil))))))))))))), 
         (let coqpp_body b a aeq lemma2 n
         atts = Vernacextend.vtdefault (fun () -> 
# 261 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts ~binders:b a aeq n None (Some lemma2) None 
                ) in fun b
         a aeq lemma2 n ?loc ~atts () -> coqpp_body b a aeq lemma2 n
         (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Parametric", 
                                                                    Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                                                    Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("symmetry", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("transitivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))))))))))))))))), 
         (let coqpp_body b a aeq lemma2 lemma3 n
         atts = Vernacextend.vtdefault (fun () -> 
# 263 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts ~binders:b a aeq n None (Some lemma2) (Some lemma3) 
                ) in fun b
         a aeq lemma2 lemma3 n ?loc ~atts () -> coqpp_body b a aeq lemma2
         lemma3 n (Attributes.parse rewrite_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"AddParametricRelation3" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Parametric", 
                                     Vernacextend.TyTerminal ("Relation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                     Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("reflexivity", 
                                                                   Vernacextend.TyTerminal ("proved", 
                                                                   Vernacextend.TyTerminal ("by", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("transitivity", 
                                                                   Vernacextend.TyTerminal ("proved", 
                                                                   Vernacextend.TyTerminal ("by", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyTerminal ("as", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                   Vernacextend.TyNil))))))))))))))))), 
         (let coqpp_body b a aeq lemma1 lemma3 n
         atts = Vernacextend.vtdefault (fun () -> 
# 269 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts ~binders:b a aeq n (Some lemma1) None (Some lemma3) 
                ) in fun b
         a aeq lemma1 lemma3 n ?loc ~atts () -> coqpp_body b a aeq lemma1
         lemma3 n (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Parametric", 
                                                                    Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                                                    Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("reflexivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("symmetry", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("transitivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))))))))))))))))))))), 
         (let coqpp_body b a aeq lemma1 lemma2 lemma3 n
         atts = Vernacextend.vtdefault (fun () -> 
# 273 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts ~binders:b a aeq n (Some lemma1) (Some lemma2) (Some lemma3) 
                ) in fun b
         a aeq lemma1 lemma2 lemma3 n ?loc ~atts () -> coqpp_body b a aeq
         lemma1 lemma2 lemma3 n (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Parametric", 
                                                                    Vernacextend.TyTerminal ("Relation", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                                                    Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("transitivity", 
                                                                    Vernacextend.TyTerminal ("proved", 
                                                                    Vernacextend.TyTerminal ("by", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))))))))))))), 
         (let coqpp_body b a aeq lemma3 n
         atts = Vernacextend.vtdefault (fun () -> 
# 276 "plugins/ltac/g_rewrite.mlg"
        declare_relation atts ~binders:b a aeq n None None (Some lemma3) 
                ) in fun b
         a aeq lemma3 n ?loc ~atts () -> coqpp_body b a aeq lemma3 n
         (Attributes.parse rewrite_attributes atts)), None))]


# 279 "plugins/ltac/g_rewrite.mlg"
 

let add_setoid atts binders a aeq t n =
  add_setoid atts binders a aeq t n.CAst.v

let morphism_tactic =
  let open Tacexpr in
  let name = "Coq.Classes.SetoidTactics.add_morphism_tactic" in
  let tacqid = Libnames.qualid_of_string name in
  let tac = CAst.make @@ TacArg (TacCall (CAst.make (tacqid, []))) in
  Tacinterp.interp tac



let () = Vernacextend.vernac_extend ~command:"AddSetoid1" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Setoid", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("as", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))))))), 
         (let coqpp_body a aeq t n
         atts = Vernacextend.vtdefault (fun () -> 
# 295 "plugins/ltac/g_rewrite.mlg"
      
         add_setoid atts [] a aeq t n
     
                ) in fun a
         aeq t n ?loc ~atts () -> coqpp_body a aeq t n
         (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Parametric", 
                                                                    Vernacextend.TyTerminal ("Setoid", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                                                    Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))))))), 
         (let coqpp_body binders a aeq t n
         atts = Vernacextend.vtdefault (fun () -> 
# 299 "plugins/ltac/g_rewrite.mlg"
      
         add_setoid atts binders a aeq t n
     
                ) in fun binders
         a aeq t n ?loc ~atts () -> coqpp_body binders a aeq t n
         (Attributes.parse rewrite_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Morphism", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))))), 
         (let coqpp_body m n
         atts = Vernacextend.vtopenproof (fun () ->
# 304 "plugins/ltac/g_rewrite.mlg"
         if Lib.is_modtype () then
           CErrors.user_err Pp.(str "Add Morphism cannot be used in a module type. Use Parameter Morphism instead.");
         add_morphism_interactive atts ~tactic:morphism_tactic m n.CAst.v 
                ) in fun m
         n ?loc ~atts () -> coqpp_body m n
         (Attributes.parse rewrite_attributes atts)), Some (fun m n -> 
# 303 "plugins/ltac/g_rewrite.mlg"
         VtStartProof(GuaranteesOpacity, [n.CAst.v]) 
                                                           )));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Declare", 
                                    Vernacextend.TyTerminal ("Morphism", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                    Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                  Vernacextend.TyNil))))), 
         (let coqpp_body m n
         atts = Vernacextend.vtdefault (fun () -> 
# 309 "plugins/ltac/g_rewrite.mlg"
         add_morphism_as_parameter atts m n.CAst.v 
                ) in fun m
         n ?loc ~atts () -> coqpp_body m n
         (Attributes.parse rewrite_attributes atts)), Some (fun m n -> 
# 308 "plugins/ltac/g_rewrite.mlg"
         VtSideff([n.CAst.v], VtLater) 
                                                           )));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Morphism", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("with", 
                                                                    Vernacextend.TyTerminal ("signature", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_lconstr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))))), 
         (let coqpp_body m s n
         atts = Vernacextend.vtopenproof (fun () ->
# 312 "plugins/ltac/g_rewrite.mlg"
         add_morphism atts ~tactic:morphism_tactic [] m s n.CAst.v 
                ) in fun m
         s n ?loc ~atts () -> coqpp_body m s n
         (Attributes.parse rewrite_attributes atts)), Some (fun m s n -> 
# 311 "plugins/ltac/g_rewrite.mlg"
         VtStartProof(GuaranteesOpacity,[n.CAst.v]) 
                                                           )));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", Vernacextend.TyTerminal ("Parametric", 
                                                                    Vernacextend.TyTerminal ("Morphism", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_binders), 
                                                                    Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyTerminal ("with", 
                                                                    Vernacextend.TyTerminal ("signature", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_lconstr), 
                                                                    Vernacextend.TyTerminal ("as", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))))))))))), 
         (let coqpp_body binders m s n
         atts = Vernacextend.vtopenproof (fun () ->
# 316 "plugins/ltac/g_rewrite.mlg"
         add_morphism atts ~tactic:morphism_tactic binders m s n.CAst.v 
                ) in fun binders
         m s n ?loc ~atts () -> coqpp_body binders m s n
         (Attributes.parse rewrite_attributes atts)), Some (fun binders m s n
                                                           -> 
# 315 "plugins/ltac/g_rewrite.mlg"
         VtStartProof(GuaranteesOpacity,[n.CAst.v]) 
                                                           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "setoid_symmetry" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("setoid_symmetry", Tacentries.TyNil), 
           (fun ist -> 
# 320 "plugins/ltac/g_rewrite.mlg"
                              setoid_symmetry 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("setoid_symmetry", Tacentries.TyIdent ("in", 
                                                                  Tacentries.TyArg (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_hyp), 
                                                                  Tacentries.TyNil))), 
          (fun n ist -> 
# 321 "plugins/ltac/g_rewrite.mlg"
                                          setoid_symmetry_in n 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "setoid_reflexivity" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("setoid_reflexivity", 
                            Tacentries.TyNil), (fun ist -> 
# 325 "plugins/ltac/g_rewrite.mlg"
                                setoid_reflexivity 
                                               )))]

let () = Tacentries.tactic_extend __coq_plugin_name "setoid_transitivity" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("setoid_transitivity", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                            Tacentries.TyNil)), (fun t ist -> 
# 329 "plugins/ltac/g_rewrite.mlg"
                                           setoid_transitivity (Some t) 
                                                )));
         (Tacentries.TyML (Tacentries.TyIdent ("setoid_etransitivity", 
                           Tacentries.TyNil), (fun ist -> 
# 330 "plugins/ltac/g_rewrite.mlg"
                                  setoid_transitivity None 
                                              )))]

let () = Vernacextend.vernac_extend ~command:"PrintRewriteHintDb" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                     Vernacextend.TyTerminal ("Rewrite", 
                                     Vernacextend.TyTerminal ("HintDb", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_preident), 
                                     Vernacextend.TyNil)))), (let coqpp_body s
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 335 "plugins/ltac/g_rewrite.mlg"
    Feedback.msg_notice (Autorewrite.print_rewrite_hintdb s) 
                                                                  ) in fun s
                                                             ?loc ~atts ()
                                                             -> coqpp_body s
                                                             (Attributes.unsupported_attributes atts)), None))]

