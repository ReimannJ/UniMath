let __coq_plugin_name = "coq-plugin-tutorial.tuto1"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
 

(* If we forget this line and include our own tactic definition using
  TACTIC EXTEND, as below, then we get the strange error message
  no implementation available for Tacentries, only when compiling
  theories/Loader.v
*)
open Ltac_plugin
open Pp
(* This module defines the types of arguments to be used in the
   EXTEND directives below, for example the string one. *)
open Stdarg



let () = Vernacextend.vernac_extend ~command:"WhatIsThis" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("What's", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil)), (let coqpp_body e
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 39 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let env = Global.env () in (* we'll explain later *)
     let sigma = Evd.from_env env in (* we'll explain later *)
     Inspector.print_input e (Ppconstr.pr_constr_expr env sigma) "term"
   
                                                                ) in fun e
                                                           ?loc ~atts ()
                                                           -> coqpp_body e
                                                           (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("What", 
                                    Vernacextend.TyTerminal ("kind", 
                                    Vernacextend.TyTerminal ("of", Vernacextend.TyTerminal ("term", 
                                                                   Vernacextend.TyTerminal ("is", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_string), 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body s () = Vernacextend.vtdefault (fun () -> 
# 45 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
     Inspector.print_input s strbrk "string" 
                                ) in fun s
         ?loc ~atts () -> coqpp_body s
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("What", 
                                    Vernacextend.TyTerminal ("kind", 
                                    Vernacextend.TyTerminal ("of", Vernacextend.TyTerminal ("term", 
                                                                   Vernacextend.TyTerminal ("is", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_int), 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body i () = Vernacextend.vtdefault (fun () -> 
# 47 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
     Inspector.print_input i Pp.int "int" 
                                ) in fun i
         ?loc ~atts () -> coqpp_body i
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("What", 
                                    Vernacextend.TyTerminal ("kind", 
                                    Vernacextend.TyTerminal ("of", Vernacextend.TyTerminal ("term", 
                                                                   Vernacextend.TyTerminal ("is", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body id
         () = Vernacextend.vtdefault (fun () -> 
# 49 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
     Inspector.print_input id Ppconstr.pr_id "identifier" 
              ) in fun id
         ?loc ~atts () -> coqpp_body id
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("What", 
                                    Vernacextend.TyTerminal ("kind", 
                                    Vernacextend.TyTerminal ("of", Vernacextend.TyTerminal ("identifier", 
                                                                   Vernacextend.TyTerminal ("is", 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body r () = Vernacextend.vtdefault (fun () -> 
# 51 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
     Inspector.print_input r Ppconstr.pr_qualid "reference" 
                                ) in fun r
         ?loc ~atts () -> coqpp_body r
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"WhatAreThese" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("What", 
                                     Vernacextend.TyTerminal ("is", Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_int)), 
                                                                    Vernacextend.TyTerminal ("a", 
                                                                    Vernacextend.TyTerminal ("list", 
                                                                    Vernacextend.TyTerminal ("of", 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body l () = Vernacextend.vtdefault (fun () -> 
# 60 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let print l = str "[" ++ Pp.prlist_with_sep (fun () -> str ";") Pp.int l ++ str "]" in
     Inspector.print_input l print "int list"
   
                                ) in fun l
         ?loc ~atts () -> coqpp_body l
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Is", Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist1 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_int)), 
                                                                   Vernacextend.TyTerminal ("nonempty", 
                                                                   Vernacextend.TyNil))), 
         (let coqpp_body l () = Vernacextend.vtdefault (fun () -> 
# 65 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let print l = str "[" ++ Pp.prlist_with_sep (fun () -> str ";") Pp.int l ++ str "]" in
     Inspector.print_input l print "nonempty int list"
   
                                ) in fun l
         ?loc ~atts () -> coqpp_body l
         (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("And", Vernacextend.TyTerminal ("is", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUopt (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_int)), 
                                                                    Vernacextend.TyTerminal ("provided", 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body o () = Vernacextend.vtdefault (fun () -> 
# 70 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let print o = strbrk (if Option.has_some o then "Yes" else "No") in
     Feedback.msg_notice (print o)
   
                                ) in fun o
         ?loc ~atts () -> coqpp_body o
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Intern" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Intern", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil)), (let coqpp_body e
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 116 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let env = Global.env () in (* use this; never use empty *)
     let sigma = Evd.from_env env in (* use this; never use empty *)
     let debug sigma = Termops.pr_evar_map ~with_univs:true None env sigma in
     Feedback.msg_notice (strbrk "State before intern: " ++ debug sigma);
     let (sigma, t) = Constrintern.interp_constr_evars env sigma e in
     Feedback.msg_notice (strbrk "State after intern: " ++ debug sigma);
     let print t = Printer.pr_econstr_env env sigma t in
     Feedback.msg_notice (strbrk "Interned: " ++ print t)
   
                                                                ) in fun e
                                                           ?loc ~atts ()
                                                           -> coqpp_body e
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"MyDefine" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("MyDefine", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body i e
         poly = Vernacextend.vtdefault (fun () -> 
# 151 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let env = Global.env () in
     let sigma = Evd.from_env env in
     let (sigma, t) = Constrintern.interp_constr_evars env sigma e in
     let r = Simple_declare.declare_definition ~poly i sigma t in
     let print r = strbrk "Defined " ++ Printer.pr_global r ++ strbrk "." in
     Feedback.msg_notice (print r)
   
                ) in fun i
         e ?loc ~atts () -> coqpp_body i e
         (Attributes.parse Attributes.polymorphic atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExamplePrint" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("MyPrint", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNil)), (let coqpp_body r
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 173 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let env = Global.env () in
     let sigma = Evd.from_env env in
     try
       let t = Simple_print.simple_body_access (Nametab.global r) in
       Feedback.msg_notice (Printer.pr_econstr_env env sigma t)
     with Failure s ->
       CErrors.user_err (str s)
   
                                                                ) in fun r
                                                           ?loc ~atts ()
                                                           -> coqpp_body r
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"DefineLookup" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("DefineLookup", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body i e
         poly = Vernacextend.vtdefault (fun () -> 
# 199 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let env = Global.env () in
     let sigma = Evd.from_env env in
     let (sigma, t) = Constrintern.interp_constr_evars env sigma e in
     let r = Simple_declare.declare_definition ~poly i sigma t in
     let print r = strbrk "Defined " ++ Printer.pr_global r ++ strbrk "." in
     Feedback.msg_notice (print r);
     let env = Global.env () in
     let sigma = Evd.from_env env in
     let t = Simple_print.simple_body_access r in
     let print t = strbrk "Found " ++ Printer.pr_econstr_env env sigma t in
     Feedback.msg_notice (print t)
   
                ) in fun i
         e ?loc ~atts () -> coqpp_body i e
         (Attributes.parse Attributes.polymorphic atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Check1" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Check1", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil)), (let coqpp_body e
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 223 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let env = Global.env () in
     let sigma = Evd.from_env env in
     let (sigma, t) = Constrintern.interp_constr_evars env sigma e in
     let (sigma, typ) = Simple_check.simple_check1 env sigma t in
     Feedback.msg_notice (Printer.pr_econstr_env env sigma typ)
   
                                                                ) in fun e
                                                           ?loc ~atts ()
                                                           -> coqpp_body e
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Check2" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Check2", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil)), (let coqpp_body e
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 234 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let env = Global.env () in
     let sigma = Evd.from_env env in
     let (sigma, t) = Constrintern.interp_constr_evars env sigma e in
     let typ = Simple_check.simple_check2 env sigma t in
     Feedback.msg_notice (Printer.pr_econstr_env env sigma typ)
   
                                                                ) in fun e
                                                           ?loc ~atts ()
                                                           -> coqpp_body e
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Convertible" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Convertible", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyNil))), (let coqpp_body e1
                                                            e2
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 252 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    
     let env = Global.env () in
     let sigma = Evd.from_env env in
     let (sigma, t1) = Constrintern.interp_constr_evars env sigma e1 in
     let (sigma, t2) = Constrintern.interp_constr_evars env sigma e2 in
     match Reductionops.infer_conv env sigma t1 t2 with
     | Some _ ->
        Feedback.msg_notice (strbrk "Yes :)")
     | None ->
        Feedback.msg_notice (strbrk "No :(")
   
                                                                 ) in fun e1
                                                            e2 ?loc ~atts ()
                                                            -> coqpp_body e1
                                                            e2
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "my_intro" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("my_intro", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_ident), 
                                                            Tacentries.TyNil)), 
           (fun i ist -> 
# 273 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    Tactics.introduction i 
           )))]

let () = Vernacextend.vernac_extend ~command:"ExploreProof" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("ExploreProof", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtreadproof (
                                                          
# 288 "doc/plugin_tutorial/tuto1/src/g_tuto1.mlg"
    fun ~pstate ->
    let sigma, env = Declare.Proof.get_current_context pstate in
    let pprf = Proof.partial_proof (Declare.Proof.get pstate) in
    Feedback.msg_notice
      (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf)
  
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

