let __coq_plugin_name = "coq-plugin-tutorial.tuto2"
let _ = Mltop.add_known_module __coq_plugin_name

# 59 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
 
  (*** Dependencies from Coq ***)

  (*
   * This lets us take non-terminal arguments to a command (for example,
   * the PassInt command that takes an integer argument needs this
   * this dependency).
   *
   * First used by: PassInt
   *)
  open Stdarg

  (*
   * This is Coq's pretty-printing module. Here, we need it to use some
   * useful syntax for pretty-printing.
   *
   * First use by: Count
   *)
  open Pp


let () = Vernacextend.vernac_extend ~command:"NoOp" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Nothing", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 90 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
                     () 
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"NoOpTerminal" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Command", 
                                     Vernacextend.TyTerminal ("With", 
                                     Vernacextend.TyTerminal ("Some", 
                                     Vernacextend.TyTerminal ("Terminal", 
                                     Vernacextend.TyTerminal ("Parameters", 
                                     Vernacextend.TyNil))))), (let coqpp_body () = 
                                                              Vernacextend.vtdefault (fun () -> 
                                                              
# 178 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
                                                           () 
                                                              ) in fun ?loc ~atts ()
                                                              -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"PassInt" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Pass", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_int), 
                                     Vernacextend.TyNil)), (let coqpp_body i
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 218 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
                         () 
                                                                ) in fun i
                                                           ?loc ~atts ()
                                                           -> coqpp_body i
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"AcceptIntList" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Accept", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist0 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_int)), 
                                     Vernacextend.TyNil)), (let coqpp_body l
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 312 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
                                () 
                                                                ) in fun l
                                                           ?loc ~atts ()
                                                           -> coqpp_body l
                                                           (Attributes.unsupported_attributes atts)), None))]

let (wit_custom, custom) = Vernacextend.vernac_argument_extend ~name:"custom" 
                           {
                           Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.token (CLexer.terminal "Bar"))))
                                                        (fun _ loc -> 
# 420 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
                 Custom.Bar 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "Foo"))))
                                                       (fun _ loc -> 
# 419 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
                 Custom.Foo 
                                                                    ))]);
                           Vernacextend.arg_printer = fun env sigma -> 
                           fun _ -> Pp.str "missing printer";
                           }
let _ = (wit_custom, custom)

let () = Vernacextend.vernac_extend ~command:"PassCustom" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Foobar", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_custom), 
                                     Vernacextend.TyNil)), (let coqpp_body x
                                                           () = Vernacextend.vtdefault (fun () -> 
                                                                
# 444 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
                              () 
                                                                ) in fun x
                                                           ?loc ~atts ()
                                                           -> coqpp_body x
                                                           (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Awesome" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Is", Vernacextend.TyTerminal ("Everything", 
                                                                    Vernacextend.TyTerminal ("Awesome", 
                                                                    Vernacextend.TyNil))), 
         (let coqpp_body () = Vernacextend.vtdefault (fun () -> 
# 476 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
    
     Feedback.msg_notice (Pp.str "Everything is awesome!")
   
                              ) in fun ?loc ~atts ()
         -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"Count" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Count", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 524 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
    
     Counter.increment ();
     let v = Counter.value () in
     Feedback.msg_notice (Pp.str "Times Count has been called: " ++ Pp.int v)
   
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"CountPersistent" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Count", 
                                     Vernacextend.TyTerminal ("Persistent", 
                                     Vernacextend.TyNil)), (let coqpp_body () = 
                                                           Vernacextend.vtdefault (fun () -> 
                                                           
# 594 "doc/plugin_tutorial/tuto2/src/g_tuto2.mlg"
    
     Persistent_counter.increment ();
     let v = Persistent_counter.value () in
     Feedback.msg_notice (Pp.str "Times Count Persistent has been called: " ++ Pp.int v)
   
                                                           ) in fun ?loc ~atts ()
                                                           -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

