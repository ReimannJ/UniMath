
# 11 "plugins/derive/g_derive.mlg"
 

open Stdarg



let __coq_plugin_name = "coq-core.plugins.derive"
let _ = Mltop.add_known_module __coq_plugin_name

# 19 "plugins/derive/g_derive.mlg"
 

let classify_derive_command _ = Vernacextend.(VtStartProof (Doesn'tGuaranteeOpacity,[]))



let () = Vernacextend.vernac_extend ~command:"Derive" ~classifier:( classify_derive_command ) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Derive", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                     Vernacextend.TyTerminal ("SuchThat", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                     Vernacextend.TyTerminal ("As", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_identref), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body f suchthat lemma
         () = Vernacextend.vtopenproof (fun () ->
# 27 "plugins/derive/g_derive.mlg"
    Derive.start_deriving f.CAst.v suchthat lemma.CAst.v 
              ) in fun f
         suchthat lemma ?loc ~atts () -> coqpp_body f suchthat lemma
         (Attributes.unsupported_attributes atts)), None))]

