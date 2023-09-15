
# 11 "plugins/firstorder/g_ground.mlg"
 

open Ltac_plugin
open Formula
open Sequent
open Ground
open Goptions
open Tacmach
open Tacticals
open Tacinterp
open Stdarg
open Tacarg
open Attributes
open Pcoq.Prim



let __coq_plugin_name = "coq-core.plugins.firstorder"
let _ = Mltop.add_known_module __coq_plugin_name

# 32 "plugins/firstorder/g_ground.mlg"
 

let ground_depth =
  declare_nat_option_and_ref ~depr:false ~key:["Firstorder";"Depth"] ~value:3

let default_intuition_tac =
  let tac _ _ = Auto.h_auto None [] (Some []) in
  let name = { Tacexpr.mltac_plugin = "coq-core.plugins.firstorder"; mltac_tactic = "auto_with"; } in
  let entry = { Tacexpr.mltac_name = name; mltac_index = 0 } in
  Tacenv.register_ml_tactic name [| tac |];
  CAst.make (Tacexpr.TacML (entry, []))

let (set_default_solver, default_solver, print_default_solver) =
  Tactic_option.declare_tactic_option ~default:default_intuition_tac "Firstorder default solver"



let () = Vernacextend.vernac_extend ~command:"Firstorder_Set_Solver" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Set", 
                                     Vernacextend.TyTerminal ("Firstorder", 
                                     Vernacextend.TyTerminal ("Solver", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                     Vernacextend.TyNil)))), (let coqpp_body t
                                                             locality = 
                                                             Vernacextend.vtdefault (fun () -> 
                                                             
# 50 "plugins/firstorder/g_ground.mlg"
                                                               
      set_default_solver
        (Locality.make_section_locality locality)
        (Tacintern.glob_tactic t)
  
                                                             ) in fun t
                                                             ?loc ~atts ()
                                                             -> coqpp_body t
                                                             (Attributes.parse locality atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Firstorder_Print_Solver" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                     Vernacextend.TyTerminal ("Firstorder", 
                                     Vernacextend.TyTerminal ("Solver", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 58 "plugins/firstorder/g_ground.mlg"
                                        
    Feedback.msg_notice
      (Pp.(++) (Pp.str"Firstorder solver tactic is ") (print_default_solver ())) 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]


# 63 "plugins/firstorder/g_ground.mlg"
 

let gen_ground_tac flag taco ids bases =
  let backup= !qflag in
  Proofview.tclOR begin
  Proofview.Goal.enter begin fun gl ->
      qflag:=flag;
      let solver=
        match taco with
            Some tac-> tac
          | None-> snd (default_solver ()) in
      let startseq k =
        Proofview.Goal.enter begin fun gl ->
        let seq=empty_seq (ground_depth ()) in
        let seq, sigma = extend_with_ref_list (pf_env gl) (project gl) ids seq in
        let seq, sigma = extend_with_auto_hints (pf_env gl) sigma bases seq in
        tclTHEN (Proofview.Unsafe.tclEVARS sigma) (k seq)
        end
      in
      let result=ground_tac solver startseq in
      qflag := backup;
      result
  end
  end
  (fun (e, info) -> qflag := backup; Proofview.tclZERO ~info e)

(* special for compatibility with Intuition

let constant str = Coqlib.get_constr str

let defined_connectives=lazy
  [[],EvalConstRef (destConst (constant "core.not.type"));
   [],EvalConstRef (destConst (constant "core.iff.type"))]

let normalize_evaluables=
  onAllHypsAndConcl
    (function
         None->unfold_in_concl (Lazy.force defined_connectives)
       | Some id->
           unfold_in_hyp (Lazy.force defined_connectives)
           (Tacexpr.InHypType id)) *)

open Ppconstr
open Printer
let pr_firstorder_using_raw _ _ _ = Pptactic.pr_auto_using pr_qualid
let pr_firstorder_using_glob _ _ _ = Pptactic.pr_auto_using (Pputils.pr_or_var (fun x -> pr_global (snd x)))
let pr_firstorder_using_typed _ _ _ = Pptactic.pr_auto_using pr_global



let (wit_firstorder_using, firstorder_using) = Tacentries.argument_extend ~name:"firstorder_using" 
                                               {
                                               Tacentries.arg_parsing = 
                                               Vernacextend.Arg_rules (
                                               [(Pcoq.Production.make
                                                 (Pcoq.Rule.stop)
                                                 (fun loc -> 
# 119 "plugins/firstorder/g_ground.mlg"
           [] 
                                                             ));
                                               (Pcoq.Production.make
                                                (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "using"))))
                                                                ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm reference)) ((Pcoq.Symbol.rules 
                                                                [Pcoq.Rules.make 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal ","))))
                                                                (fun _ loc ->
                                                                
# 0 ""
()
                                                                )])) false)))
                                                (fun l _ loc -> 
# 118 "plugins/firstorder/g_ground.mlg"
                                                l 
                                                                ))]);
                                               Tacentries.arg_tag = Some
                                                                    (Geninterp.Val.List 
                                                                    (Geninterp.val_tag (Genarg.topwit wit_reference)));
                                               Tacentries.arg_intern = 
                                               Tacentries.ArgInternWit (Genarg.ListArg 
                                               (wit_reference));
                                               Tacentries.arg_subst = 
                                               Tacentries.ArgSubstWit (Genarg.ListArg 
                                               (wit_reference));
                                               Tacentries.arg_interp = 
                                               Tacentries.ArgInterpWit (Genarg.ListArg 
                                               (wit_reference));
                                               Tacentries.arg_printer = 
                                               ((fun env sigma -> 
# 116 "plugins/firstorder/g_ground.mlg"
                   pr_firstorder_using_raw 
                                               ), (fun env sigma -> 
# 117 "plugins/firstorder/g_ground.mlg"
                    pr_firstorder_using_glob 
                                               ), (fun env sigma -> 
# 115 "plugins/firstorder/g_ground.mlg"
               pr_firstorder_using_typed 
                                               ));
                                               }
let _ = (wit_firstorder_using, firstorder_using)

let () = Tacentries.tactic_extend __coq_plugin_name "firstorder" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("firstorder", Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_tactic)), 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_firstorder_using), 
                                                              Tacentries.TyNil))), 
           (fun t l ist -> 
# 124 "plugins/firstorder/g_ground.mlg"
        gen_ground_tac true (Option.map (tactic_of_value ist) t) l [] 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("firstorder", Tacentries.TyArg (
                                                             Extend.TUopt (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_tactic)), 
                                                             Tacentries.TyIdent ("with", 
                                                             Tacentries.TyArg (
                                                             Extend.TUlist1 (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                             Tacentries.TyNil)))), 
          (fun t l ist -> 
# 126 "plugins/firstorder/g_ground.mlg"
        gen_ground_tac true (Option.map (tactic_of_value ist) t) [] l 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("firstorder", Tacentries.TyArg (
                                                             Extend.TUopt (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_tactic)), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_firstorder_using), 
                                                             Tacentries.TyIdent ("with", 
                                                             Tacentries.TyArg (
                                                             Extend.TUlist1 (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                                             Tacentries.TyNil))))), 
          (fun t l l' ist -> 
# 129 "plugins/firstorder/g_ground.mlg"
        gen_ground_tac true (Option.map (tactic_of_value ist) t) l l' 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "gintuition" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("gintuition", Tacentries.TyArg (
                                                              Extend.TUopt (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_tactic)), 
                                                              Tacentries.TyNil)), 
           (fun t ist -> 
# 134 "plugins/firstorder/g_ground.mlg"
       gen_ground_tac false (Option.map (tactic_of_value ist) t) [] [] 
           )))]

