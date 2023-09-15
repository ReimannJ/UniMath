
# 15 "plugins/ltac/g_obligations.mlg"
 

open Constrexpr
open Constrexpr_ops
open Stdarg
open Tacarg
open Extraargs

let (set_default_tactic, get_default_tactic, print_default_tactic) =
  Tactic_option.declare_tactic_option "Program tactic"

let () =
  (* Delay to recover the tactic imperatively *)
  let tac = Proofview.tclBIND (Proofview.tclUNIT ()) begin fun () ->
    snd (get_default_tactic ())
  end in
  Declare.Obls.default_tactic := tac

let with_tac f tac =
  let env = Genintern.empty_glob_sign (Global.env ()) in
  let tac = match tac with
  | None -> None
  | Some tac ->
    let tac = Genarg.in_gen (Genarg.rawwit wit_ltac) tac in
    let _, tac = Genintern.generic_intern env tac in
    Some tac
  in
  f tac

(* We define new entries for programs, with the use of this module
 * Subtac. These entries are named Subtac.<foo>
 *)

module Tactic = Pltac

open Pcoq

let sigref loc = mkRefC (Libnames.qualid_of_string ~loc "Coq.Init.Specif.sig")

type 'a withtac_argtype = (Tacexpr.raw_tactic_expr option, 'a) Genarg.abstract_argument_type

let wit_withtac : Tacexpr.raw_tactic_expr option Genarg.uniform_genarg_type =
  Genarg.create_arg "withtac"

let withtac = Pcoq.create_generic_entry2 "withtac" (Genarg.rawwit wit_withtac)



let _ = let () = assert (Pcoq.Entry.is_empty withtac) in
        let () =
        Pcoq.grammar_extend withtac
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 68 "plugins/ltac/g_obligations.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                 ((Pcoq.Symbol.nterm Tactic.tactic)))
                                 (fun t _ loc -> 
# 67 "plugins/ltac/g_obligations.mlg"
                                       Some t 
                                                 )])]))
        in let () =
        Pcoq.grammar_extend Constr.closed_binder
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                            ((Pcoq.Symbol.nterm Prim.name)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                            ((Pcoq.Symbol.nterm Constr.lconstr)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                            ((Pcoq.Symbol.nterm Constr.lconstr)))
                                            ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                            (fun _ c _ t _ id _ loc -> 
# 72 "plugins/ltac/g_obligations.mlg"
                                                                                
          let typ = mkAppC (sigref loc, [mkLambdaC ([id], default_binder_kind, t, c)]) in
          [CLocalAssum ([id], default_binder_kind, typ)] 
                                                       )]))
        in ()


# 79 "plugins/ltac/g_obligations.mlg"
 

open Declare.Obls

let obligation ~pm obl tac = with_tac (fun t -> obligation ~pm obl t) tac
let next_obligation ~pm obl tac = with_tac (fun t -> next_obligation ~pm obl t) tac

let classify_obbl _ = Vernacextend.(VtStartProof (Doesn'tGuaranteeOpacity,[]))



let () = Vernacextend.vernac_extend ~command:"Obligations" ~classifier:( classify_obbl ) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Obligation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_natural), 
                                     Vernacextend.TyTerminal ("of", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_lglob), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_withtac), 
                                                                    Vernacextend.TyNil))))))), 
         (let coqpp_body num name t tac
         () = Vernacextend.vtdeclareprogram (
# 92 "plugins/ltac/g_obligations.mlg"
      obligation (num, Some name.CAst.v, Some t) tac 
              ) in fun num
         name t tac ?loc ~atts () -> coqpp_body num name t tac
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Obligation", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_natural), 
                                    Vernacextend.TyTerminal ("of", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_withtac), 
                                                                   Vernacextend.TyNil))))), 
         (let coqpp_body num name tac
         () = Vernacextend.vtdeclareprogram (
# 94 "plugins/ltac/g_obligations.mlg"
      obligation (num, Some name.CAst.v, None) tac 
              ) in fun num
         name tac ?loc ~atts () -> coqpp_body num name tac
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Obligation", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_natural), 
                                    Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_lglob), 
                                                                  Vernacextend.TyNonTerminal (
                                                                  Extend.TUentry (Genarg.get_arg_tag wit_withtac), 
                                                                  Vernacextend.TyNil))))), 
         (let coqpp_body num t tac
         () = Vernacextend.vtdeclareprogram (
# 96 "plugins/ltac/g_obligations.mlg"
      obligation (num, None, Some t) tac 
              ) in fun num
         t tac ?loc ~atts () -> coqpp_body num t tac
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Obligation", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_natural), 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_withtac), 
                                    Vernacextend.TyNil))), (let coqpp_body num
                                                           tac
                                                           () = Vernacextend.vtdeclareprogram (
                                                                
# 98 "plugins/ltac/g_obligations.mlg"
      obligation (num, None, None) tac 
                                                                ) in fun num
                                                           tac ?loc ~atts ()
                                                           -> coqpp_body num
                                                           tac
                                                           (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Next", 
                                    Vernacextend.TyTerminal ("Obligation", 
                                    Vernacextend.TyTerminal ("of", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_withtac), 
                                                                   Vernacextend.TyNil))))), 
         (let coqpp_body name tac
         () = Vernacextend.vtdeclareprogram (
# 100 "plugins/ltac/g_obligations.mlg"
      next_obligation (Some name.CAst.v) tac 
              ) in fun name
         tac ?loc ~atts () -> coqpp_body name tac
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Next", 
                                    Vernacextend.TyTerminal ("Obligation", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_withtac), 
                                    Vernacextend.TyNil))), (let coqpp_body tac
                                                           () = Vernacextend.vtdeclareprogram (
                                                                
# 101 "plugins/ltac/g_obligations.mlg"
                                            next_obligation None tac 
                                                                ) in fun tac
                                                           ?loc ~atts ()
                                                           -> coqpp_body tac
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Solve_Obligation" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Solve", 
                                     Vernacextend.TyTerminal ("Obligation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_natural), 
                                     Vernacextend.TyTerminal ("of", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyTerminal ("with", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                    Vernacextend.TyNil))))))), 
         (let coqpp_body num name t
         () = Vernacextend.vtmodifyprogram (
# 106 "plugins/ltac/g_obligations.mlg"
      try_solve_obligation num (Some name.CAst.v) (Some (Tacinterp.interp t)) 
              ) in fun num
         name t ?loc ~atts () -> coqpp_body num name t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Solve", 
                                    Vernacextend.TyTerminal ("Obligation", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_natural), 
                                    Vernacextend.TyTerminal ("with", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                    Vernacextend.TyNil))))), (let coqpp_body num
                                                             t
                                                             () = Vernacextend.vtmodifyprogram (
                                                                  
# 108 "plugins/ltac/g_obligations.mlg"
      try_solve_obligation num None (Some (Tacinterp.interp t)) 
                                                                  ) in fun num
                                                             t ?loc ~atts ()
                                                             -> coqpp_body num
                                                             t
                                                             (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Solve_Obligations" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Solve", 
                                     Vernacextend.TyTerminal ("Obligations", 
                                     Vernacextend.TyTerminal ("of", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyTerminal ("with", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body name t
         () = Vernacextend.vtmodifyprogram (
# 113 "plugins/ltac/g_obligations.mlg"
      try_solve_obligations (Some name.CAst.v) (Some (Tacinterp.interp t)) 
              ) in fun name
         t ?loc ~atts () -> coqpp_body name t
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Solve", 
                                    Vernacextend.TyTerminal ("Obligations", 
                                    Vernacextend.TyTerminal ("of", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                   Vernacextend.TyNil)))), 
         (let coqpp_body name
         () = Vernacextend.vtmodifyprogram (
# 115 "plugins/ltac/g_obligations.mlg"
      try_solve_obligations (Some name.CAst.v) None 
              ) in fun name
         ?loc ~atts () -> coqpp_body name
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Solve", 
                                    Vernacextend.TyTerminal ("Obligations", 
                                    Vernacextend.TyTerminal ("with", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                    Vernacextend.TyNil)))), (let coqpp_body t
                                                            () = Vernacextend.vtmodifyprogram (
                                                                 
# 117 "plugins/ltac/g_obligations.mlg"
      try_solve_obligations None (Some (Tacinterp.interp t)) 
                                                                 ) in fun t
                                                            ?loc ~atts ()
                                                            -> coqpp_body t
                                                            (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Solve", 
                                    Vernacextend.TyTerminal ("Obligations", 
                                    Vernacextend.TyNil)), (let coqpp_body () = 
                                                          Vernacextend.vtmodifyprogram (
                                                          
# 119 "plugins/ltac/g_obligations.mlg"
      try_solve_obligations None None 
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Solve_All_Obligations" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Solve", 
                                     Vernacextend.TyTerminal ("All", 
                                     Vernacextend.TyTerminal ("Obligations", 
                                     Vernacextend.TyTerminal ("with", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                     Vernacextend.TyNil))))), (let coqpp_body t
                                                              () = Vernacextend.vtmodifyprogram (
                                                                   
# 124 "plugins/ltac/g_obligations.mlg"
      solve_all_obligations (Some (Tacinterp.interp t)) 
                                                                   ) in fun t
                                                              ?loc ~atts ()
                                                              -> coqpp_body t
                                                              (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Solve", 
                                    Vernacextend.TyTerminal ("All", Vernacextend.TyTerminal ("Obligations", 
                                                                    Vernacextend.TyNil))), 
         (let coqpp_body () = Vernacextend.vtmodifyprogram (
# 126 "plugins/ltac/g_obligations.mlg"
      solve_all_obligations None 
                              ) in fun ?loc ~atts ()
         -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Admit_Obligations" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Admit", 
                                     Vernacextend.TyTerminal ("Obligations", 
                                     Vernacextend.TyTerminal ("of", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body name
         () = Vernacextend.vtmodifyprogram (
# 130 "plugins/ltac/g_obligations.mlg"
                                                     admit_obligations (Some name.CAst.v) 
              ) in fun name
         ?loc ~atts () -> coqpp_body name
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Admit", 
                                    Vernacextend.TyTerminal ("Obligations", 
                                    Vernacextend.TyNil)), (let coqpp_body () = 
                                                          Vernacextend.vtmodifyprogram (
                                                          
# 131 "plugins/ltac/g_obligations.mlg"
                                 admit_obligations None 
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Set_Solver" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Obligation", 
                                     Vernacextend.TyTerminal ("Tactic", 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t
         locality = Vernacextend.vtdefault (fun () -> 
# 135 "plugins/ltac/g_obligations.mlg"
                                                                                    
        set_default_tactic
          (Locality.make_section_locality locality)
          (Tacintern.glob_tactic t);
  
                    ) in fun t
         ?loc ~atts () -> coqpp_body t
         (Attributes.parse Attributes.locality atts)), None))]


# 142 "plugins/ltac/g_obligations.mlg"
 

open Pp



let () = Vernacextend.vernac_extend ~command:"Show_Solver" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                     Vernacextend.TyTerminal ("Obligation", 
                                     Vernacextend.TyTerminal ("Tactic", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 149 "plugins/ltac/g_obligations.mlg"
                                       
    Feedback.msg_notice (str"Program obligation tactic is " ++ print_default_tactic ()) 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Show_Obligations" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Obligations", 
                                     Vernacextend.TyTerminal ("of", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))), 
         (let coqpp_body name () = Vernacextend.vtreadprogram (
# 154 "plugins/ltac/g_obligations.mlg"
                                             fun ~pm -> show_obligations ~pm (Some name.CAst.v) 
                                   ) in fun name
         ?loc ~atts () -> coqpp_body name
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Obligations", 
                                    Vernacextend.TyNil), (let coqpp_body () = 
                                                         Vernacextend.vtreadprogram (
                                                         
# 155 "plugins/ltac/g_obligations.mlg"
                         fun ~pm -> show_obligations ~pm None 
                                                         ) in fun ?loc ~atts ()
                                                         -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Show_Preterm" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Preterm", 
                                     Vernacextend.TyTerminal ("of", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil))), 
         (let coqpp_body name () = Vernacextend.vtreadprogram (
# 159 "plugins/ltac/g_obligations.mlg"
                                         fun ~pm -> Feedback.msg_notice (show_term ~pm (Some name.CAst.v)) 
                                   ) in fun name
         ?loc ~atts () -> coqpp_body name
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Preterm", 
                                    Vernacextend.TyNil), (let coqpp_body () = 
                                                         Vernacextend.vtreadprogram (
                                                         
# 160 "plugins/ltac/g_obligations.mlg"
                     fun ~pm -> Feedback.msg_notice (show_term ~pm None) 
                                                         ) in fun ?loc ~atts ()
                                                         -> coqpp_body (Attributes.unsupported_attributes atts)), None))]


# 163 "plugins/ltac/g_obligations.mlg"
 

(* Declare a printer for the content of Program tactics *)
let () =
  let printer env sigma _ _ _ = function
  | None -> mt ()
  | Some tac -> str "with" ++ spc () ++ Pptactic.pr_raw_tactic env sigma tac
  in
  Pptactic.declare_extra_vernac_genarg_pprule wit_withtac printer



