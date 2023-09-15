
# 11 "plugins/extraction/g_extraction.mlg"
 

open Pcoq.Prim



let __coq_plugin_name = "coq-core.plugins.extraction"
let _ = Mltop.add_known_module __coq_plugin_name

# 19 "plugins/extraction/g_extraction.mlg"
 

(* ML names *)

open Ltac_plugin
open Stdarg
open Pp
open Names
open Table
open Extract_env

let pr_mlname _ _ _ s = spc () ++ qs s



let (wit_mlname, mlname) = Tacentries.argument_extend ~name:"mlname" 
                           {
                           Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                    [(Pcoq.Production.make
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.stop)
                                                      ((Pcoq.Symbol.nterm string)))
                                                      (fun s loc -> 
# 38 "plugins/extraction/g_extraction.mlg"
                     s 
                                                                    ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm preident)))
                                                     (fun id loc -> 
# 37 "plugins/extraction/g_extraction.mlg"
                        id 
                                                                    ))]);
                           Tacentries.arg_tag = Some
                                                (Geninterp.val_tag (Genarg.topwit wit_string));
                           Tacentries.arg_intern = Tacentries.ArgInternWit (wit_string);
                           Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_string);
                           Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_string);
                           Tacentries.arg_printer = ((fun env sigma -> 
                                                    
# 36 "plugins/extraction/g_extraction.mlg"
               pr_mlname 
                                                    ), (fun env sigma -> 
                                                    
# 36 "plugins/extraction/g_extraction.mlg"
               pr_mlname 
                                                    ), (fun env sigma -> 
                                                    
# 36 "plugins/extraction/g_extraction.mlg"
               pr_mlname 
                                                    ));
                           }
let _ = (wit_mlname, mlname)


# 41 "plugins/extraction/g_extraction.mlg"
 

let pr_int_or_id _ _ _ = function
  | ArgInt i -> int i
  | ArgId id -> Id.print id



let (wit_int_or_id, int_or_id) = Tacentries.argument_extend ~name:"int_or_id" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm integer)))
                                                            (fun i loc -> 
# 52 "plugins/extraction/g_extraction.mlg"
                      ArgInt i 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm preident)))
                                                           (fun id loc -> 
# 51 "plugins/extraction/g_extraction.mlg"
                        ArgId (Id.of_string id) 
                                                                    ))]);
                                 Tacentries.arg_tag = None;
                                 Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                 Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                 Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 50 "plugins/extraction/g_extraction.mlg"
               pr_int_or_id 
                                                          ), (fun env sigma -> 
                                                          
# 50 "plugins/extraction/g_extraction.mlg"
               pr_int_or_id 
                                                          ), (fun env sigma -> 
                                                          
# 50 "plugins/extraction/g_extraction.mlg"
               pr_int_or_id 
                                                          ));
                                 }
let _ = (wit_int_or_id, int_or_id)


# 55 "plugins/extraction/g_extraction.mlg"
 

let pr_language = function
  | Ocaml -> str "OCaml"
  | Haskell -> str "Haskell"
  | Scheme -> str "Scheme"
  | JSON -> str "JSON"



let (wit_language, language) = Vernacextend.vernac_argument_extend ~name:"language" 
                               {
                               Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (CLexer.terminal "JSON"))))
                                                            (fun _ loc -> 
# 70 "plugins/extraction/g_extraction.mlg"
                  JSON 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "Scheme"))))
                                                           (fun _ loc -> 
# 69 "plugins/extraction/g_extraction.mlg"
                    Scheme 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "Haskell"))))
                                                           (fun _ loc -> 
# 68 "plugins/extraction/g_extraction.mlg"
                     Haskell 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "OCaml"))))
                                                           (fun _ loc -> 
# 67 "plugins/extraction/g_extraction.mlg"
                   Ocaml 
                                                                    ))]);
                               Vernacextend.arg_printer = fun env sigma -> 
                               
# 66 "plugins/extraction/g_extraction.mlg"
             pr_language 
                               ;
                               }
let _ = (wit_language, language)

let () = Vernacextend.vernac_extend ~command:"Extraction" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyNil)), (let coqpp_body x
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 77 "plugins/extraction/g_extraction.mlg"
                                  simple_extraction x 
                                                                ) in fun x
                                                           ?loc ~atts ()
                                                           -> coqpp_body x
                                                           (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Recursive", 
                                    Vernacextend.TyTerminal ("Extraction", 
                                    Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_global)), 
                                    Vernacextend.TyNil))), (let coqpp_body l
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 78 "plugins/extraction/g_extraction.mlg"
                                                      full_extraction None l 
                                                                ) in fun l
                                                           ?loc ~atts ()
                                                           -> coqpp_body l
                                                           (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extraction", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_string), 
                                    Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_global)), 
                                    Vernacextend.TyNil))), (let coqpp_body f
                                                           l
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 82 "plugins/extraction/g_extraction.mlg"
       full_extraction (Some f) l 
                                                                ) in fun f
                                                           l ?loc ~atts ()
                                                           -> coqpp_body f l
                                                           (Attributes.unsupported_attributes atts)), None));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extraction", 
                                    Vernacextend.TyTerminal ("TestCompile", 
                                    Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_global)), 
                                    Vernacextend.TyNil))), (let coqpp_body l
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 86 "plugins/extraction/g_extraction.mlg"
       extract_and_compile l 
                                                                ) in fun l
                                                           ?loc ~atts ()
                                                           -> coqpp_body l
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"SeparateExtraction" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Separate", 
                                     Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_global)), 
                                     Vernacextend.TyNil))), (let coqpp_body l
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 92 "plugins/extraction/g_extraction.mlg"
       separate_extraction l 
                                                                 ) in fun l
                                                            ?loc ~atts ()
                                                            -> coqpp_body l
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExtractionLibrary" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Library", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                     Vernacextend.TyNil))), (let coqpp_body m
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 98 "plugins/extraction/g_extraction.mlg"
       extraction_library false m 
                                                                 ) in fun m
                                                            ?loc ~atts ()
                                                            -> coqpp_body m
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"RecursiveExtractionLibrary" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Recursive", 
                                     Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Library", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                     Vernacextend.TyNil)))), (let coqpp_body m
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 103 "plugins/extraction/g_extraction.mlg"
       extraction_library true m 
                                                                  ) in fun m
                                                             ?loc ~atts ()
                                                             -> coqpp_body m
                                                             (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExtractionLanguage" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Language", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_language), 
                                     Vernacextend.TyNil))), (let coqpp_body l
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 109 "plugins/extraction/g_extraction.mlg"
       extraction_language l 
                                                                 ) in fun l
                                                            ?loc ~atts ()
                                                            -> coqpp_body l
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExtractionInline" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Inline", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_global)), 
                                     Vernacextend.TyNil))), (let coqpp_body l
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 115 "plugins/extraction/g_extraction.mlg"
       extraction_inline true l 
                                                                 ) in fun l
                                                            ?loc ~atts ()
                                                            -> coqpp_body l
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExtractionNoInline" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("NoInline", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_global)), 
                                     Vernacextend.TyNil))), (let coqpp_body l
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 120 "plugins/extraction/g_extraction.mlg"
       extraction_inline false l 
                                                                 ) in fun l
                                                            ?loc ~atts ()
                                                            -> coqpp_body l
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"PrintExtractionInline" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                     Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Inline", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 125 "plugins/extraction/g_extraction.mlg"
      Feedback.msg_notice (print_extraction_inline ()) 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ResetExtractionInline" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Reset", 
                                     Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Inline", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 130 "plugins/extraction/g_extraction.mlg"
       reset_extraction_inline () 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExtractionImplicit" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Implicit", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyTerminal ("[", Vernacextend.TyNonTerminal (
                                                                   Extend.TUlist0 (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_int_or_id)), 
                                                                   Vernacextend.TyTerminal ("]", 
                                                                   Vernacextend.TyNil)))))), 
         (let coqpp_body r l
         () = Vernacextend.vtdefault (fun () -> 
# 136 "plugins/extraction/g_extraction.mlg"
       extraction_implicit r l 
              ) in fun r
         l ?loc ~atts () -> coqpp_body r l
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExtractionBlacklist" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Blacklist", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_preident)), 
                                     Vernacextend.TyNil))), (let coqpp_body l
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 142 "plugins/extraction/g_extraction.mlg"
       extraction_blacklist l 
                                                                 ) in fun l
                                                            ?loc ~atts ()
                                                            -> coqpp_body l
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"PrintExtractionBlacklist" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                     Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Blacklist", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 147 "plugins/extraction/g_extraction.mlg"
       Feedback.msg_notice (print_extraction_blacklist ()) 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ResetExtractionBlacklist" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Reset", 
                                     Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyTerminal ("Blacklist", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 152 "plugins/extraction/g_extraction.mlg"
       reset_extraction_blacklist () 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExtractionConstant" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extract", 
                                     Vernacextend.TyTerminal ("Constant", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                     Vernacextend.TyTerminal ("=>", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_mlname), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body x idl y
         () = Vernacextend.vtdefault (fun () -> 
# 159 "plugins/extraction/g_extraction.mlg"
       extract_constant_inline false x idl y 
              ) in fun x
         idl y ?loc ~atts () -> coqpp_body x idl y
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExtractionInlinedConstant" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extract", 
                                     Vernacextend.TyTerminal ("Inlined", 
                                     Vernacextend.TyTerminal ("Constant", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyTerminal ("=>", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_mlname), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body x y
         () = Vernacextend.vtdefault (fun () -> 
# 164 "plugins/extraction/g_extraction.mlg"
       extract_constant_inline true x [] y 
              ) in fun x
         y ?loc ~atts () -> coqpp_body x y
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ExtractionInductive" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Extract", 
                                     Vernacextend.TyTerminal ("Inductive", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_global), 
                                     Vernacextend.TyTerminal ("=>", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_mlname), 
                                                                    Vernacextend.TyTerminal ("[", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUlist0 (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_mlname)), 
                                                                    Vernacextend.TyTerminal ("]", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUopt (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_string)), 
                                                                    Vernacextend.TyNil))))))))), 
         (let coqpp_body x id idl o
         () = Vernacextend.vtdefault (fun () -> 
# 170 "plugins/extraction/g_extraction.mlg"
       extract_inductive x id idl o 
              ) in fun x
         id idl o ?loc ~atts () -> coqpp_body x id idl o
         (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"ShowExtraction" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Show", 
                                     Vernacextend.TyTerminal ("Extraction", 
                                     Vernacextend.TyNil)), (let coqpp_body () = 
                                                           Vernacextend.vtreadproof (
                                                           
# 176 "plugins/extraction/g_extraction.mlg"
       show_extraction 
                                                           ) in fun ?loc ~atts ()
                                                           -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

