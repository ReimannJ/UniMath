
# 11 "plugins/ring/g_ring.mlg"
 

open Ltac_plugin
open Pp
open Util
open Ring_ast
open Ring
open Stdarg
open Tacarg
open Pcoq.Constr
open Pltac



let __coq_plugin_name = "coq-core.plugins.ring"
let _ = Mltop.add_known_module __coq_plugin_name
let () = Tacentries.tactic_extend __coq_plugin_name "protect_fv" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("protect_fv", Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_string), 
                                                              Tacentries.TyIdent ("in", 
                                                              Tacentries.TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                              Tacentries.TyNil)))), 
           (fun map id ist -> 
# 29 "plugins/ring/g_ring.mlg"
      protect_tac_in map id 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("protect_fv", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_string), 
                                                             Tacentries.TyNil)), 
          (fun map ist -> 
# 31 "plugins/ring/g_ring.mlg"
      protect_tac map 
          )))]


# 34 "plugins/ring/g_ring.mlg"
 

open Pptactic
open Ppconstr

let pr_ring_mod env sigma = function
  | Ring_kind (Computational eq_test) -> str "decidable" ++ pr_arg (pr_constr_expr env sigma) eq_test
  | Ring_kind Abstract ->  str "abstract"
  | Ring_kind (Morphism morph) -> str "morphism" ++ pr_arg (pr_constr_expr env sigma) morph
  | Const_tac (CstTac cst_tac) -> str "constants" ++ spc () ++ str "[" ++ pr_raw_tactic env sigma cst_tac ++ str "]"
  | Const_tac (Closed l) -> str "closed" ++ spc () ++ str "[" ++ prlist_with_sep spc pr_qualid l ++ str "]"
  | Pre_tac t -> str "preprocess" ++ spc () ++ str "[" ++ pr_raw_tactic env sigma t ++ str "]"
  | Post_tac t -> str "postprocess" ++ spc () ++ str "[" ++ pr_raw_tactic env sigma t ++ str "]"
  | Setoid(sth,ext) -> str "setoid" ++ pr_arg (pr_constr_expr env sigma) sth ++ pr_arg (pr_constr_expr env sigma) ext
  | Pow_spec(Closed l,spec) -> str "power_tac" ++ pr_arg (pr_constr_expr env sigma) spec ++ spc () ++ str "[" ++ prlist_with_sep spc pr_qualid l ++ str "]"
  | Pow_spec(CstTac cst_tac,spec) -> str "power_tac" ++ pr_arg (pr_constr_expr env sigma) spec ++ spc () ++ str "[" ++ pr_raw_tactic env sigma cst_tac ++ str "]"
  | Sign_spec t -> str "sign" ++ pr_arg (pr_constr_expr env sigma) t
  | Div_spec t -> str "div" ++ pr_arg (pr_constr_expr env sigma) t



let (wit_ring_mod, ring_mod) = Vernacextend.vernac_argument_extend ~name:"ring_mod" 
                               {
                               Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (CLexer.terminal "div"))))
                                                            ((Pcoq.Symbol.nterm constr)))
                                                            (fun div_spec _
                                                            loc -> 
# 70 "plugins/ring/g_ring.mlg"
                                    Div_spec div_spec 
                                                                   ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "power_tac"))))
                                                           ((Pcoq.Symbol.nterm constr)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                           ((Pcoq.Symbol.nterm tactic)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                           (fun _ cst_tac _
                                                           pow_spec _ loc ->
                                                           
# 69 "plugins/ring/g_ring.mlg"
             Pow_spec (CstTac cst_tac, pow_spec) 
                                                           ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "power"))))
                                                           ((Pcoq.Symbol.nterm constr)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                           (fun _ l _
                                                           pow_spec _ loc ->
                                                           
# 67 "plugins/ring/g_ring.mlg"
             Pow_spec (Closed l, pow_spec) 
                                                           ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "sign"))))
                                                           ((Pcoq.Symbol.nterm constr)))
                                                           (fun sign_spec _
                                                           loc -> 
# 65 "plugins/ring/g_ring.mlg"
                                      Sign_spec sign_spec 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "setoid"))))
                                                           ((Pcoq.Symbol.nterm constr)))
                                                           ((Pcoq.Symbol.nterm constr)))
                                                           (fun ext sth _
                                                           loc -> 
# 64 "plugins/ring/g_ring.mlg"
                                              Setoid(sth,ext) 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "postprocess"))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                           ((Pcoq.Symbol.nterm tactic)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                           (fun _ post _ _
                                                           loc -> 
# 63 "plugins/ring/g_ring.mlg"
                                                Post_tac post 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "preprocess"))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                           ((Pcoq.Symbol.nterm tactic)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                           (fun _ pre _ _
                                                           loc -> 
# 62 "plugins/ring/g_ring.mlg"
                                              Pre_tac pre 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "closed"))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                           (fun _ l _ _
                                                           loc -> 
# 61 "plugins/ring/g_ring.mlg"
                                                Const_tac(Closed l) 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "constants"))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                           ((Pcoq.Symbol.nterm tactic)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                           (fun _ cst_tac _ _
                                                           loc -> 
# 60 "plugins/ring/g_ring.mlg"
                                                 Const_tac(CstTac cst_tac) 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "morphism"))))
                                                           ((Pcoq.Symbol.nterm constr)))
                                                           (fun morph _
                                                           loc -> 
# 59 "plugins/ring/g_ring.mlg"
                                      Ring_kind(Morphism morph) 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "abstract"))))
                                                           (fun _ loc -> 
# 58 "plugins/ring/g_ring.mlg"
                        Ring_kind Abstract 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "decidable"))))
                                                           ((Pcoq.Symbol.nterm constr)))
                                                           (fun eq_test _
                                                           loc -> 
# 57 "plugins/ring/g_ring.mlg"
                                         Ring_kind(Computational eq_test) 
                                                                  ))]);
                               Vernacextend.arg_printer = fun env sigma -> 
                               
# 56 "plugins/ring/g_ring.mlg"
               pr_ring_mod env sigma 
                               ;
                               }
let _ = (wit_ring_mod, ring_mod)


# 73 "plugins/ring/g_ring.mlg"
 

let pr_ring_mods env sigma l = surround (prlist_with_sep pr_comma (pr_ring_mod env sigma) l)



let (wit_ring_mods, ring_mods) = Vernacextend.vernac_argument_extend ~name:"ring_mods" 
                                 {
                                 Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                              ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm ring_mod)) ((Pcoq.Symbol.rules 
                                                              [Pcoq.Rules.make 
                                                              (Pcoq.Rule.next_norec 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal ","))))
                                                              (fun _ loc -> 
                                                              
# 0 ""
()
                                                              )])) false)))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                              (fun _ mods _
                                                              loc -> 
                                                              
# 81 "plugins/ring/g_ring.mlg"
                                                     mods 
                                                              ))]);
                                 Vernacextend.arg_printer = fun env sigma -> 
                                 
# 80 "plugins/ring/g_ring.mlg"
               pr_ring_mods env sigma 
                                 ;
                                 }
let _ = (wit_ring_mods, ring_mods)

let () = Vernacextend.vernac_extend ~command:"AddSetoidRing" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Ring", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                     Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUopt (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ring_mods)), 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body id t l
         () = Vernacextend.vtdefault (fun () -> 
# 86 "plugins/ring/g_ring.mlg"
      add_theory id.CAst.v t (Option.default [] l) 
              ) in fun id
         t l ?loc ~atts () -> coqpp_body id t l
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                    Vernacextend.TyTerminal ("Rings", 
                                    Vernacextend.TyNil)), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 87 "plugins/ring/g_ring.mlg"
                                                                  
    print_rings ()
  
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), Some 
         
# 87 "plugins/ring/g_ring.mlg"
                             Vernacextend.classify_as_query 
         ))]

let () = Tacentries.tactic_extend __coq_plugin_name "ring_lookup" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ring_lookup", Tacentries.TyArg (
                                                               Extend.TUentryl (Genarg.get_arg_tag wit_tactic, 0), 
                                                               Tacentries.TyIdent ("[", 
                                                               Tacentries.TyArg (
                                                               Extend.TUlist0 (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                                               Tacentries.TyIdent ("]", 
                                                               Tacentries.TyArg (
                                                               Extend.TUlist1 (
                                                               Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                                               Tacentries.TyNil)))))), 
           (fun f lH lrt ist -> 
# 94 "plugins/ring/g_ring.mlg"
      let (t,lr) = List.sep_last lrt in ring_lookup f lH lr t 
           )))]


# 97 "plugins/ring/g_ring.mlg"
 

let pr_field_mod env sigma = function
  | Ring_mod m -> pr_ring_mod env sigma m
  | Inject inj -> str "completeness" ++ pr_arg (pr_constr_expr env sigma) inj



let (wit_field_mod, field_mod) = Vernacextend.vernac_argument_extend ~name:"field_mod" 
                                 {
                                 Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "completeness"))))
                                                              ((Pcoq.Symbol.nterm constr)))
                                                              (fun inj _
                                                              loc -> 
                                                              
# 108 "plugins/ring/g_ring.mlg"
                                        Inject inj 
                                                              ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.nterm ring_mod)))
                                                             (fun m loc -> 
# 107 "plugins/ring/g_ring.mlg"
                         Ring_mod m 
                                                                    ))]);
                                 Vernacextend.arg_printer = fun env sigma -> 
                                 
# 106 "plugins/ring/g_ring.mlg"
               pr_field_mod env sigma 
                                 ;
                                 }
let _ = (wit_field_mod, field_mod)


# 111 "plugins/ring/g_ring.mlg"
 

let pr_field_mods env sigma l = surround (prlist_with_sep pr_comma (pr_field_mod env sigma) l)



let (wit_field_mods, field_mods) = Vernacextend.vernac_argument_extend ~name:"field_mods" 
                                   {
                                   Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                                ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm field_mod)) ((Pcoq.Symbol.rules 
                                                                [Pcoq.Rules.make 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal ","))))
                                                                (fun _ loc ->
                                                                
# 0 ""
()
                                                                )])) false)))
                                                                ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                                (fun _ mods _
                                                                loc -> 
                                                                
# 119 "plugins/ring/g_ring.mlg"
                                                      mods 
                                                                ))]);
                                   Vernacextend.arg_printer = fun env sigma -> 
                                   
# 118 "plugins/ring/g_ring.mlg"
               pr_field_mods env sigma 
                                   ;
                                   }
let _ = (wit_field_mods, field_mods)

let () = Vernacextend.vernac_extend ~command:"AddSetoidField" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Add", 
                                     Vernacextend.TyTerminal ("Field", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                     Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUopt (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_field_mods)), 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body id t l
         () = Vernacextend.vtdefault (fun () -> 
# 124 "plugins/ring/g_ring.mlg"
    let l = match l with None -> [] | Some l -> l in add_field_theory id.CAst.v t l 
              ) in fun id
         t l ?loc ~atts () -> coqpp_body id t l
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                    Vernacextend.TyTerminal ("Fields", 
                                    Vernacextend.TyNil)), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 125 "plugins/ring/g_ring.mlg"
                                                               
    print_fields ()
  
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), Some 
         
# 125 "plugins/ring/g_ring.mlg"
                           Vernacextend.classify_as_query
         ))]

let () = Tacentries.tactic_extend __coq_plugin_name "field_lookup" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("field_lookup", Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                Tacentries.TyIdent ("[", 
                                                                Tacentries.TyArg (
                                                                Extend.TUlist0 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                                                Tacentries.TyIdent ("]", 
                                                                Tacentries.TyArg (
                                                                Extend.TUlist1 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr)), 
                                                                Tacentries.TyNil)))))), 
           (fun f lH lt ist -> 
# 132 "plugins/ring/g_ring.mlg"
        let (t,l) = List.sep_last lt in field_lookup f lH l t 
           )))]

