
# 11 "plugins/funind/g_indfun.mlg"
 

open Ltac_plugin
open Util
open Pp
open Constrexpr
open Indfun_common
open Indfun
open Stdarg
open Tacarg
open Extraargs
open Tactypes
open Pcoq.Prim
open Pcoq.Constr
open Pltac



let __coq_plugin_name = "coq-core.plugins.funind"
let _ = Mltop.add_known_module __coq_plugin_name

# 31 "plugins/funind/g_indfun.mlg"
 

let pr_fun_ind_using env sigma prc prlc _ opt_c =
  match opt_c with
    | None -> mt ()
    | Some b -> spc () ++ hov 2 (str "using" ++ spc () ++ Miscprint.pr_with_bindings (prc env sigma) (prlc env sigma) b)

(* Duplication of printing functions because "'a with_bindings" is
   (internally) not uniform in 'a: indeed constr_with_bindings at the
   "typed" level has type "open_constr with_bindings" instead of
   "constr with_bindings"; hence, its printer cannot be polymorphic in
   (prc,prlc)... *)

let pr_fun_ind_using_typed prc prlc _ opt_c =
  match opt_c with
    | None -> mt ()
    | Some b ->
      let env = Global.env () in
      let evd = Evd.from_env env in
      let (_, b) = b env evd in
      spc () ++ hov 2 (str "using" ++ spc () ++ Miscprint.pr_with_bindings (prc env evd) (prlc env evd) b)



let (wit_fun_ind_using, fun_ind_using) = Tacentries.argument_extend ~name:"fun_ind_using" 
                                         {
                                         Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                                  [(Pcoq.Production.make
                                                                    (Pcoq.Rule.stop)
                                                                    (fun
                                                                    loc -> 
                                                                    
# 61 "plugins/funind/g_indfun.mlg"
           None 
                                                                    ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "using"))))
                                                                   ((Pcoq.Symbol.nterm constr_with_bindings)))
                                                                   (fun c _
                                                                   loc -> 
                                                                   
# 60 "plugins/funind/g_indfun.mlg"
                                           Some c 
                                                                   ))]);
                                         Tacentries.arg_tag = Some
                                                              (Geninterp.Val.Opt 
                                                              (Geninterp.val_tag (Genarg.topwit wit_constr_with_bindings)));
                                         Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.OptArg 
                                                                 (wit_constr_with_bindings));
                                         Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.OptArg 
                                                                (wit_constr_with_bindings));
                                         Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.OptArg 
                                                                 (wit_constr_with_bindings));
                                         Tacentries.arg_printer = ((fun env sigma -> 
                                                                  
# 58 "plugins/funind/g_indfun.mlg"
                   pr_fun_ind_using env sigma 
                                                                  ), (fun env sigma -> 
                                                                  
# 59 "plugins/funind/g_indfun.mlg"
                    pr_fun_ind_using env sigma 
                                                                  ), (fun env sigma -> 
                                                                  
# 57 "plugins/funind/g_indfun.mlg"
               pr_fun_ind_using_typed 
                                                                  ));
                                         }
let _ = (wit_fun_ind_using, fun_ind_using)

let () = Tacentries.tactic_extend __coq_plugin_name "newfuninv" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("functional", Tacentries.TyIdent ("inversion", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_quantified_hypothesis), 
                                                              Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_reference)), 
                                                              Tacentries.TyNil)))), 
           (fun hyp fname ist -> 
# 67 "plugins/funind/g_indfun.mlg"
      
       Invfun.invfun hyp fname
     
           )))]


# 72 "plugins/funind/g_indfun.mlg"
 

let pr_intro_as_pat _prc _ _ pat =
  match pat with
    | Some pat ->
      spc () ++ str "as" ++ spc () ++ (* Miscprint.pr_intro_pattern prc  pat *)
        str"<simple_intropattern>"
    | None -> mt ()

let out_disjunctive = CAst.map (function
  | IntroAction (IntroOrAndPattern l) -> l
  | _ -> CErrors.user_err Pp.(str "Disjunctive or conjunctive intro pattern expected."))



let (wit_with_names, with_names) = Tacentries.argument_extend ~name:"with_names" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.stop)
                                                              (fun loc -> 
# 89 "plugins/funind/g_indfun.mlg"
           None 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "as"))))
                                                             ((Pcoq.Symbol.nterm simple_intropattern)))
                                                             (fun ipat _
                                                             loc -> 
# 88 "plugins/funind/g_indfun.mlg"
                                           Some ipat 
                                                                    ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.Opt 
                                                        (Geninterp.val_tag (Genarg.topwit wit_intro_pattern)));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.OptArg 
                                                           (wit_intro_pattern));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.OptArg 
                                                          (wit_intro_pattern));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.OptArg 
                                                           (wit_intro_pattern));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 87 "plugins/funind/g_indfun.mlg"
                                                                      pr_intro_as_pat 
                                                            ), (fun env sigma -> 
                                                            
# 87 "plugins/funind/g_indfun.mlg"
                                                                      pr_intro_as_pat 
                                                            ), (fun env sigma -> 
                                                            
# 87 "plugins/funind/g_indfun.mlg"
                                                                      pr_intro_as_pat 
                                                            ));
                                   }
let _ = (wit_with_names, with_names)


# 92 "plugins/funind/g_indfun.mlg"
 

let functional_induction b c x pat =
  functional_induction true c x (Option.map out_disjunctive pat)



let () = Tacentries.tactic_extend __coq_plugin_name "newfunind" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("functional", Tacentries.TyIdent ("induction", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_lconstr), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_fun_ind_using), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_with_names), 
                                                              Tacentries.TyNil))))), 
           (fun c princl pat ist -> 
# 101 "plugins/funind/g_indfun.mlg"
    
     (Ltac_plugin.Internals.onSomeWithHoles
          (fun x -> functional_induction true c x pat) princl)
   
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "snewfunind" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("soft", Tacentries.TyIdent ("functional", 
                                                        Tacentries.TyIdent ("induction", 
                                                        Tacentries.TyArg (
                                                        Extend.TUlist1 (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_fun_ind_using), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_with_names), 
                                                        Tacentries.TyNil)))))), 
           (fun cl princl pat ist -> 
# 110 "plugins/funind/g_indfun.mlg"
      
       let c = match cl with
         | [] -> assert false
         | [c] -> c
         | c::cl -> EConstr.applist(c,cl)
       in
       Ltac_plugin.Internals.onSomeWithHoles (fun x -> functional_induction false c x pat) princl 
           )))]


# 119 "plugins/funind/g_indfun.mlg"
 

let pr_constr_comma_sequence env sigma prc _ _ = prlist_with_sep pr_comma (prc env sigma)



let (wit_constr_comma_sequence', constr_comma_sequence') = Tacentries.argument_extend ~name:"constr_comma_sequence'" 
                                                           {
                                                           Tacentries.arg_parsing = 
                                                           Vernacextend.Arg_rules (
                                                           [(Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.nterm constr)))
                                                             (fun c loc -> 
# 129 "plugins/funind/g_indfun.mlg"
                     [c] 
                                                                    ));
                                                           (Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm constr)))
                                                            ((Pcoq.Symbol.token (CLexer.terminal ","))))
                                                            (Pcoq.Symbol.self))
                                                            (fun l _ c loc ->
                                                            
# 128 "plugins/funind/g_indfun.mlg"
                                                   c::l 
                                                            ))]);
                                                           Tacentries.arg_tag = 
                                                           Some
                                                           (Geninterp.Val.List 
                                                           (Geninterp.val_tag (Genarg.topwit wit_constr)));
                                                           Tacentries.arg_intern = 
                                                           Tacentries.ArgInternWit (Genarg.ListArg 
                                                           (wit_constr));
                                                           Tacentries.arg_subst = 
                                                           Tacentries.ArgSubstWit (Genarg.ListArg 
                                                           (wit_constr));
                                                           Tacentries.arg_interp = 
                                                           Tacentries.ArgInterpWit (Genarg.ListArg 
                                                           (wit_constr));
                                                           Tacentries.arg_printer = 
                                                           ((fun env sigma -> 
                                                           
# 127 "plugins/funind/g_indfun.mlg"
               pr_constr_comma_sequence env sigma 
                                                           ), (fun env sigma -> 
                                                           
# 127 "plugins/funind/g_indfun.mlg"
               pr_constr_comma_sequence env sigma 
                                                           ), (fun env sigma -> 
                                                           
# 127 "plugins/funind/g_indfun.mlg"
               pr_constr_comma_sequence env sigma 
                                                           ));
                                                           }
let _ = (wit_constr_comma_sequence', constr_comma_sequence')


# 132 "plugins/funind/g_indfun.mlg"
 

let pr_auto_using env sigma prc _prlc _prt = Pptactic.pr_auto_using (prc env sigma)



let (wit_auto_using', auto_using') = Tacentries.argument_extend ~name:"auto_using'" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.stop)
                                                                (fun loc -> 
# 142 "plugins/funind/g_indfun.mlg"
           [] 
                                                                    ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "using"))))
                                                               ((Pcoq.Symbol.nterm constr_comma_sequence')))
                                                               (fun l _
                                                               loc -> 
                                                               
# 141 "plugins/funind/g_indfun.mlg"
                                             l 
                                                               ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.Val.List 
                                                          (Geninterp.val_tag (Genarg.topwit wit_constr)));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                             (wit_constr));
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                            (wit_constr));
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                             (wit_constr));
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 140 "plugins/funind/g_indfun.mlg"
               pr_auto_using env sigma 
                                                              ), (fun env sigma -> 
                                                              
# 140 "plugins/funind/g_indfun.mlg"
               pr_auto_using env sigma 
                                                              ), (fun env sigma -> 
                                                              
# 140 "plugins/funind/g_indfun.mlg"
               pr_auto_using env sigma 
                                                              ));
                                     }
let _ = (wit_auto_using', auto_using')


# 145 "plugins/funind/g_indfun.mlg"
 

module Vernac = Pvernac.Vernac_
module Tactic = Pltac

let (wit_function_fix_definition : Vernacexpr.fixpoint_expr Loc.located Genarg.uniform_genarg_type) =
  Genarg.create_arg "function_fix_definition"

let function_fix_definition =
  Pcoq.create_generic_entry2 "function_fix_definition" (Genarg.rawwit wit_function_fix_definition)



let _ = let () = assert (Pcoq.Entry.is_empty function_fix_definition)
        in
        let () =
        Pcoq.grammar_extend function_fix_definition
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Vernac.fix_definition)))
                                  (fun g loc -> 
# 162 "plugins/funind/g_indfun.mlg"
                                       Loc.tag ~loc g 
                                                )])]))
        in ()


# 167 "plugins/funind/g_indfun.mlg"
 

let () =
  let raw_printer env sigma _ _ _ (loc,body) = Ppvernac.pr_rec_definition body in
  Pptactic.declare_extra_vernac_genarg_pprule wit_function_fix_definition raw_printer

let is_proof_termination_interactively_checked recsl =
  List.exists (function
  | _,( Vernacexpr.{ rec_order = Some { CAst.v = CMeasureRec _ } }
      | Vernacexpr.{ rec_order = Some { CAst.v = CWfRec _} }) -> true
  | _, Vernacexpr.{ rec_order = Some { CAst.v = CStructRec _ } }
  | _, Vernacexpr.{ rec_order = None } -> false) recsl

let classify_as_Fixpoint recsl =
 Vernac_classifier.classify_vernac
    (Vernacexpr.(CAst.make @@ { control = []; attrs = []; expr = VernacFixpoint(NoDischarge, List.map snd recsl)}))

let classify_funind recsl =
  match classify_as_Fixpoint recsl with
  | Vernacextend.VtSideff (ids, _)
    when is_proof_termination_interactively_checked recsl ->
      Vernacextend.(VtStartProof (GuaranteesOpacity, ids))
  | x -> x

let is_interactive recsl =
  match classify_funind recsl with
  | Vernacextend.VtStartProof _ -> true
  | _ -> false



let () = Vernacextend.vernac_extend ~command:"Function"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Function", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1sep (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_function_fix_definition), "with"), 
                                     Vernacextend.TyNil)), (let coqpp_body recsl
                                                           () = 
# 210 "plugins/funind/g_indfun.mlg"
        
    let warn = "-unused-pattern-matching-variable,-matching-variable,-non-recursive" in
    if is_interactive recsl then
      Vernacextend.vtopenproof (fun () ->
          CWarnings.with_warn warn
            Gen_principle.do_generate_principle_interactive (List.map snd recsl))
    else
      Vernacextend.vtdefault (fun () ->
          CWarnings.with_warn warn
            Gen_principle.do_generate_principle (List.map snd recsl))
  
                                                                 in fun recsl
                                                           ?loc ~atts ()
                                                           -> coqpp_body recsl
                                                           (Attributes.unsupported_attributes atts)), Some 
         (fun recsl -> 
# 209 "plugins/funind/g_indfun.mlg"
         classify_funind recsl 
         )))]


# 223 "plugins/funind/g_indfun.mlg"
 

let pr_fun_scheme_arg (princ_name,fun_name,s) =
  Names.Id.print princ_name ++ str " :=" ++ spc() ++ str "Induction for " ++
  Libnames.pr_qualid fun_name ++ spc() ++ str "Sort " ++
  Sorts.pr_sort_family s



let (wit_fun_scheme_arg, fun_scheme_arg) = Vernacextend.vernac_argument_extend ~name:"fun_scheme_arg" 
                                           {
                                           Vernacextend.arg_parsing = 
                                           Vernacextend.Arg_rules ([(
                                                                   Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.nterm identref)))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "Induction"))))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "for"))))
                                                                   ((Pcoq.Symbol.nterm reference)))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "Sort"))))
                                                                   ((Pcoq.Symbol.nterm sort_family)))
                                                                   (fun s _
                                                                   fun_name _
                                                                   _ _
                                                                   princ_name
                                                                   loc -> 
                                                                   
# 234 "plugins/funind/g_indfun.mlg"
                                                                                                 (princ_name.CAst.v,fun_name,s) 
                                                                   ))]);
                                           Vernacextend.arg_printer = fun env sigma -> 
                                           
# 233 "plugins/funind/g_indfun.mlg"
             pr_fun_scheme_arg 
                                           ;
                                           }
let _ = (wit_fun_scheme_arg, fun_scheme_arg)


# 237 "plugins/funind/g_indfun.mlg"
 

let warning_error names e =
  match e with
  | Building_graph e ->
    let names = pr_enum Libnames.pr_qualid names in
    let error = if do_observe () then (spc () ++ CErrors.print e) else mt () in
    Gen_principle.warn_cannot_define_graph (names,error)
  | Defining_principle e ->
    let names = pr_enum Libnames.pr_qualid names in
    let error = if do_observe () then CErrors.print e else mt () in
    Gen_principle.warn_cannot_define_principle (names,error)
  | _ -> raise e



let () = Vernacextend.vernac_extend ~command:"NewFunctionalScheme"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Functional", 
                                     Vernacextend.TyTerminal ("Scheme", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1sep (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_fun_scheme_arg), "with"), 
                                     Vernacextend.TyNil))), (let coqpp_body fas
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 257 "plugins/funind/g_indfun.mlg"
      begin
        try
          Gen_principle.build_scheme fas
        with
        | Gen_principle.No_graph_found ->
          begin
            match fas with
            | (_,fun_name,_)::_ ->
              begin
                Gen_principle.make_graph (Smartlocate.global_with_alias fun_name);
                try Gen_principle.build_scheme fas
                with
                | Gen_principle.No_graph_found ->
                  CErrors.user_err Pp.(str "Cannot generate induction principle(s)")
                | e when CErrors.noncritical e ->
                  let names = List.map (fun (_,na,_) -> na) fas in
                  warning_error names e
              end
              | _ -> assert false (* we can only have non empty  list *)
          end
        | e when CErrors.noncritical e ->
          let names = List.map (fun (_,na,_) -> na) fas in
          warning_error names e
      end
    
                                                                 ) in fun fas
                                                            ?loc ~atts ()
                                                            -> coqpp_body fas
                                                            (Attributes.unsupported_attributes atts)), Some 
         (fun fas -> 
# 255 "plugins/funind/g_indfun.mlg"
        Vernacextend.(VtSideff(List.map pi1 fas, VtLater)) 
         )))]

let () = Vernacextend.vernac_extend ~command:"NewFunctionalCase"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Functional", 
                                     Vernacextend.TyTerminal ("Case", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_fun_scheme_arg), 
                                     Vernacextend.TyNil))), (let coqpp_body fas
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 288 "plugins/funind/g_indfun.mlg"
       Gen_principle.build_case_scheme fas 
                                                                 ) in fun fas
                                                            ?loc ~atts ()
                                                            -> coqpp_body fas
                                                            (Attributes.unsupported_attributes atts)), Some 
         (fun fas -> 
# 287 "plugins/funind/g_indfun.mlg"
       Vernacextend.(VtSideff([pi1 fas], VtLater)) 
         )))]

let () = Vernacextend.vernac_extend ~command:"GenerateGraph" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Generate", 
                                     Vernacextend.TyTerminal ("graph", 
                                     Vernacextend.TyTerminal ("for", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNil)))), (let coqpp_body c
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 294 "plugins/funind/g_indfun.mlg"
    Gen_principle.make_graph (Smartlocate.global_with_alias c) 
                                                                  ) in fun c
                                                             ?loc ~atts ()
                                                             -> coqpp_body c
                                                             (Attributes.unsupported_attributes atts)), None))]

