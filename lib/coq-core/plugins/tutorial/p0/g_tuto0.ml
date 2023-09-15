let __coq_plugin_name = "coq-plugin-tutorial.tuto0"
let _ = Mltop.add_known_module __coq_plugin_name

# 3 "doc/plugin_tutorial/tuto0/src/g_tuto0.mlg"
 

open Pp
open Ltac_plugin

let tuto_warn = CWarnings.create ~name:"name" ~category:"category"
                            (fun _ -> strbrk Tuto0_main.message)



let () = Vernacextend.vernac_extend ~command:"HelloWorld" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("HelloWorld", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 20 "doc/plugin_tutorial/tuto0/src/g_tuto0.mlg"
                        Feedback.msg_notice (strbrk Tuto0_main.message) 
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "hello_world_tactic" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("hello_world", Tacentries.TyNil), 
           (fun ist -> 
# 28 "doc/plugin_tutorial/tuto0/src/g_tuto0.mlg"
    let _ = Feedback.msg_notice (str Tuto0_main.message) in
    Tacticals.tclIDTAC 
           )))]

let () = Vernacextend.vernac_extend ~command:"HelloWarning" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("HelloWarning", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 41 "doc/plugin_tutorial/tuto0/src/g_tuto0.mlg"
    
     tuto_warn ()
   
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "hello_warning_tactic" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("hello_warning", Tacentries.TyNil), 
           (fun ist -> 
# 51 "doc/plugin_tutorial/tuto0/src/g_tuto0.mlg"
    
     let _ = tuto_warn () in
     Tacticals.tclIDTAC
   
           )))]

let () = Vernacextend.vernac_extend ~command:"HelloError" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("HelloError", 
                                     Vernacextend.TyNil), (let coqpp_body () = 
                                                          Vernacextend.vtdefault (fun () -> 
                                                          
# 64 "doc/plugin_tutorial/tuto0/src/g_tuto0.mlg"
                        CErrors.user_err (str Tuto0_main.message) 
                                                          ) in fun ?loc ~atts ()
                                                          -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

let () = Tacentries.tactic_extend __coq_plugin_name "hello_error_tactic" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("hello_error", Tacentries.TyNil), 
           (fun ist -> 
# 72 "doc/plugin_tutorial/tuto0/src/g_tuto0.mlg"
    let _ = CErrors.user_err (str Tuto0_main.message) in
    Tacticals.tclIDTAC 
           )))]

