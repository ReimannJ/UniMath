let __coq_plugin_name = "coq-core.plugins.number_string_notation"
let _ = Mltop.add_known_module __coq_plugin_name

# 13 "plugins/syntax/g_number_string.mlg"
 

open Notation
open Number
open String_notation
open Pp
open Stdarg
open Pcoq.Prim

let pr_number_after = function
  | Nop -> mt ()
  | Warning n -> str "warning after " ++ NumTok.UnsignedNat.print n
  | Abstract n -> str "abstract after " ++ NumTok.UnsignedNat.print n

let pr_deprecated_number_modifier m = str "(" ++ pr_number_after m ++ str ")"

let pr_number_string_mapping (b, n, n') =
  if b then
    str "[" ++ Libnames.pr_qualid n ++ str "]" ++ spc () ++ str "=>" ++ spc ()
    ++ Libnames.pr_qualid n'
  else
    Libnames.pr_qualid n ++ spc () ++ str "=>" ++ spc ()
    ++ Libnames.pr_qualid n'

let pr_number_string_via (n, l) =
  str "via " ++ Libnames.pr_qualid n ++ str " mapping ["
  ++ prlist_with_sep pr_comma pr_number_string_mapping l ++ str "]"

let pr_number_modifier = function
  | After a -> pr_number_after a
  | Via nl -> pr_number_string_via nl

let pr_number_options l =
  str "(" ++ prlist_with_sep pr_comma pr_number_modifier l ++ str ")"

let pr_string_option l =
  str "(" ++ pr_number_string_via l ++ str ")"



let (wit_deprecated_number_modifier, deprecated_number_modifier) = Vernacextend.vernac_argument_extend ~name:"deprecated_number_modifier" 
                                                                   {
                                                                   Vernacextend.arg_parsing = 
                                                                   Vernacextend.Arg_rules (
                                                                   [(
                                                                   Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "abstract"))))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "after"))))
                                                                   ((Pcoq.Symbol.nterm bignat)))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                                   (fun _ n _
                                                                   _ _ loc ->
                                                                   
# 57 "plugins/syntax/g_number_string.mlg"
                                                Abstract (NumTok.UnsignedNat.of_string n) 
                                                                   ));
                                                                   (Pcoq.Production.make
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                                    ((Pcoq.Symbol.token (CLexer.terminal "warning"))))
                                                                    ((Pcoq.Symbol.token (CLexer.terminal "after"))))
                                                                    ((Pcoq.Symbol.nterm bignat)))
                                                                    ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                                    (fun _
                                                                    waft _ _
                                                                    _ loc ->
                                                                    
# 56 "plugins/syntax/g_number_string.mlg"
                                                  Warning (NumTok.UnsignedNat.of_string waft) 
                                                                    ));
                                                                   (Pcoq.Production.make
                                                                    (Pcoq.Rule.stop)
                                                                    (fun
                                                                    loc -> 
                                                                    
# 55 "plugins/syntax/g_number_string.mlg"
           Nop 
                                                                    ))]);
                                                                   Vernacextend.arg_printer = fun env sigma -> 
                                                                   
# 54 "plugins/syntax/g_number_string.mlg"
               pr_deprecated_number_modifier 
                                                                   ;
                                                                   }
let _ = (wit_deprecated_number_modifier, deprecated_number_modifier)

let (wit_number_string_mapping, number_string_mapping) = Vernacextend.vernac_argument_extend ~name:"number_string_mapping" 
                                                         {
                                                         Vernacextend.arg_parsing = 
                                                         Vernacextend.Arg_rules (
                                                         [(Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                           ((Pcoq.Symbol.nterm reference)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "=>"))))
                                                           ((Pcoq.Symbol.nterm reference)))
                                                           (fun n' _ _ n _
                                                           loc -> 
# 63 "plugins/syntax/g_number_string.mlg"
                                                   true, n, n' 
                                                                  ));
                                                         (Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.nterm reference)))
                                                          ((Pcoq.Symbol.token (CLexer.terminal "=>"))))
                                                          ((Pcoq.Symbol.nterm reference)))
                                                          (fun n' _ n loc ->
                                                          
# 62 "plugins/syntax/g_number_string.mlg"
                                           false, n, n' 
                                                          ))]);
                                                         Vernacextend.arg_printer = fun env sigma -> 
                                                         
# 61 "plugins/syntax/g_number_string.mlg"
               pr_number_string_mapping 
                                                         ;
                                                         }
let _ = (wit_number_string_mapping, number_string_mapping)

let (wit_number_string_via, number_string_via) = Vernacextend.vernac_argument_extend ~name:"number_string_via" 
                                                 {
                                                 Vernacextend.arg_parsing = 
                                                 Vernacextend.Arg_rules (
                                                 [(Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "via"))))
                                                                   ((Pcoq.Symbol.nterm reference)))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "mapping"))))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                                   ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm number_string_mapping)) ((Pcoq.Symbol.rules 
                                                                   [Pcoq.Rules.make 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (CLexer.terminal ","))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 0 ""
()
                                                                   )])) false)))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                   (fun _ l _ _ n _ loc -> 
# 68 "plugins/syntax/g_number_string.mlg"
                                                                                          n, l 
                                                                    ))]);
                                                 Vernacextend.arg_printer = fun env sigma -> 
                                                 
# 67 "plugins/syntax/g_number_string.mlg"
               pr_number_string_via 
                                                 ;
                                                 }
let _ = (wit_number_string_via, number_string_via)

let (wit_number_modifier, number_modifier) = Vernacextend.vernac_argument_extend ~name:"number_modifier" 
                                             {
                                             Vernacextend.arg_parsing = 
                                             Vernacextend.Arg_rules (
                                             [(Pcoq.Production.make
                                               (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm number_string_via)))
                                               (fun v loc -> 
# 75 "plugins/syntax/g_number_string.mlg"
                                Via v 
                                                             ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "abstract"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal "after"))))
                                                              ((Pcoq.Symbol.nterm bignat)))
                                              (fun n _ _ loc -> 
# 74 "plugins/syntax/g_number_string.mlg"
                                        After (Abstract (NumTok.UnsignedNat.of_string n)) 
                                                                ));
                                             (Pcoq.Production.make
                                              (Pcoq.Rule.next (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "warning"))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal "after"))))
                                                              ((Pcoq.Symbol.nterm bignat)))
                                              (fun waft _ _ loc -> 
# 73 "plugins/syntax/g_number_string.mlg"
                                          After (Warning (NumTok.UnsignedNat.of_string waft)) 
                                                                   ))]);
                                             Vernacextend.arg_printer = fun env sigma -> 
                                             
# 72 "plugins/syntax/g_number_string.mlg"
               pr_number_modifier 
                                             ;
                                             }
let _ = (wit_number_modifier, number_modifier)

let (wit_number_options, number_options) = Vernacextend.vernac_argument_extend ~name:"number_options" 
                                           {
                                           Vernacextend.arg_parsing = 
                                           Vernacextend.Arg_rules ([(
                                                                   Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                                   ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm number_modifier)) ((Pcoq.Symbol.rules 
                                                                   [Pcoq.Rules.make 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (CLexer.terminal ","))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 0 ""
()
                                                                   )])) false)))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                                   (fun _ l _
                                                                   loc -> 
                                                                   
# 80 "plugins/syntax/g_number_string.mlg"
                                                       l 
                                                                   ))]);
                                           Vernacextend.arg_printer = fun env sigma -> 
                                           
# 79 "plugins/syntax/g_number_string.mlg"
               pr_number_options 
                                           ;
                                           }
let _ = (wit_number_options, number_options)

let (wit_string_option, string_option) = Vernacextend.vernac_argument_extend ~name:"string_option" 
                                         {
                                         Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                                    [(
                                                                    Pcoq.Production.make
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                                    ((Pcoq.Symbol.nterm number_string_via)))
                                                                    ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                                    (fun _ v
                                                                    _ loc ->
                                                                    
# 85 "plugins/syntax/g_number_string.mlg"
                                        v 
                                                                    ))]);
                                         Vernacextend.arg_printer = fun env sigma -> 
                                         
# 84 "plugins/syntax/g_number_string.mlg"
               pr_string_option 
                                         ;
                                         }
let _ = (wit_string_option, string_option)

let () = Vernacextend.vernac_extend ~command:"NumberNotation" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Number", 
                                     Vernacextend.TyTerminal ("Notation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNonTerminal (Extend.TUopt (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_number_options)), 
                                     Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_preident), 
                                                                   Vernacextend.TyNil)))))))), 
         (let coqpp_body ty f g nl sc
         locality = Vernacextend.vtdefault (fun () -> 
# 92 "plugins/syntax/g_number_string.mlg"
      vernac_number_notation (Locality.make_module_locality locality) ty f g (Option.default [] nl) sc 
                    ) in fun ty
         f g nl sc ?loc ~atts () -> coqpp_body ty f g nl sc
         (Attributes.parse Attributes.locality atts)), None))]

let () = Vernacextend.vernac_extend ~command:"StringNotation" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("String", 
                                     Vernacextend.TyTerminal ("Notation", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNonTerminal (Extend.TUopt (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_string_option)), 
                                     Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_preident), 
                                                                   Vernacextend.TyNil)))))))), 
         (let coqpp_body ty f g o sc
         locality = Vernacextend.vtdefault (fun () -> 
# 98 "plugins/syntax/g_number_string.mlg"
      vernac_string_notation (Locality.make_module_locality locality) ty f g o sc 
                    ) in fun ty
         f g o sc ?loc ~atts () -> coqpp_body ty f g o sc
         (Attributes.parse Attributes.locality atts)), None))]

