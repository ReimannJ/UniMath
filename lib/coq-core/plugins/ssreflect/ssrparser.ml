
# 13 "plugins/ssr/ssrparser.mlg"
 

let defaultCast = Constr.DEFAULTcast
let vmCast = Constr.VMcast
open Names
open Pp
open Pcoq
open Ltac_plugin
open Stdarg
open Tacarg
open Libnames
open Tactics
open Util
open Locus
open Tacexpr
open Tacinterp
open Pltac
open Extraargs
open Ppconstr

open Namegen
open Tactypes
open Constrexpr
open Constrexpr_ops

open Proofview
open Proofview.Notations

open Ssrmatching_plugin.Ssrmatching

open Ssrprinters
open Ssrcommon
open Ssrtacticals
open Ssrbwd
open Ssrequality
open Ssripats
open Libobject

(** Ssreflect load check. *)

(* To allow ssrcoq to be fully compatible with the "plain" Coq, we only *)
(* turn on its incompatible features (the new rewrite syntax, and the   *)
(* reserved identifiers) when the theory library (ssreflect.v) has      *)
(* has actually been required, or is being defined. Because this check  *)
(* needs to be done often (for each identifier lookup), we implement    *)
(* some caching, repeating the test only when the environment changes.  *)
(*   We check for protect_term because it is the first constant loaded; *)
(* ssr_have would ultimately be a better choice.                        *)
let ssr_loaded = Summary.ref ~name:"SSR:loaded" false
let is_ssr_loaded () =
  !ssr_loaded ||
  (if CLexer.is_keyword "SsrSyntax_is_Imported" then ssr_loaded:=true;
   !ssr_loaded)



let __coq_plugin_name = "coq-core.plugins.ssreflect"
let _ = Mltop.add_known_module __coq_plugin_name

# 71 "plugins/ssr/ssrparser.mlg"
 

let ssrtac_name name = {
  mltac_plugin = "coq-core.plugins.ssreflect";
  mltac_tactic = "ssr" ^ name;
}

let ssrtac_entry name = {
  mltac_name = ssrtac_name name;
  mltac_index = 0;
}

let cache_tactic_notation (key, body, parule) =
  Tacenv.register_alias key body;
  Pptactic.declare_notation_tactic_pprule key parule

type tactic_grammar_obj = KerName.t * Tacenv.alias_tactic * Pptactic.pp_tactic

let inSsrGrammar : tactic_grammar_obj -> obj =
  declare_object {(default_object "SsrGrammar") with
                  load_function = (fun _ -> cache_tactic_notation);
                  cache_function = cache_tactic_notation;
                  classify_function = (fun x -> Keep)}

let path = MPfile (DirPath.make @@ List.map Id.of_string ["ssreflect"; "ssr"; "Coq"])

let register_ssrtac name f prods =
  let open Pptactic in
  Tacenv.register_ml_tactic (ssrtac_name name) [|f|];
  let map id = Reference (Locus.ArgVar (CAst.make id)) in
  let get_id = function
    | TacTerm s -> None
    | TacNonTerm (_, (_, ido)) -> ido in
  let ids = List.map_filter get_id prods in
  let tac = CAst.make (TacML (ssrtac_entry name, List.map map ids)) in
  let key = KerName.make path (Label.make ("ssrparser_" ^ name)) in
  let body = Tacenv.{ alias_args = ids; alias_body = tac; alias_deprecation = None } in
  let parule = {
    pptac_level = 0;
    pptac_prods = prods
  } in
  let obj () =
    Lib.add_leaf (inSsrGrammar (key, body, parule)) in
  Mltop.declare_cache_obj obj __coq_plugin_name;
  key

let cast_arg wit v = Taccoerce.Value.cast (Genarg.topwit wit) v




# 121 "plugins/ssr/ssrparser.mlg"
 

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.get_keyword_state () ;;

let tacltop = (LevelLe 5)

let pr_ssrtacarg env sigma _ _ prt = prt env sigma tacltop



let (wit_ssrtacarg, ssrtacarg) = Tacentries.argument_extend ~name:"ssrtacarg" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          []);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.val_tag (Genarg.topwit wit_tactic));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (wit_tactic);
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_tactic);
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_tactic);
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 133 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrtacarg env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 133 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrtacarg env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 133 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrtacarg env sigma 
                                                          ));
                                 }
let _ = (wit_ssrtacarg, ssrtacarg)

let _ = let () =
        Pcoq.grammar_extend ssrtacarg
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.stop)
                                            ((Pcoq.Symbol.nterml ltac_expr ("5"))))
                            (fun tac loc -> 
# 137 "plugins/ssr/ssrparser.mlg"
                                                   tac 
                                            )]))
        in ()

let (wit_ssrtac3arg, ssrtac3arg) = Tacentries.argument_extend ~name:"ssrtac3arg" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            []);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.val_tag (Genarg.topwit wit_tactic));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (wit_tactic);
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_tactic);
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_tactic);
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 141 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrtacarg env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 141 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrtacarg env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 141 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrtacarg env sigma 
                                                            ));
                                   }
let _ = (wit_ssrtac3arg, ssrtac3arg)

let _ = let () =
        Pcoq.grammar_extend ssrtac3arg
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.stop)
                                            ((Pcoq.Symbol.nterml ltac_expr ("3"))))
                            (fun tac loc -> 
# 145 "plugins/ssr/ssrparser.mlg"
                                                    tac 
                                            )]))
        in ()


# 148 "plugins/ssr/ssrparser.mlg"
 

(* Lexically closed tactic for tacticals. *)
let pr_ssrtclarg env sigma _ _ prt tac = prt env sigma tacltop tac



let (wit_ssrtclarg, ssrtclarg) = Tacentries.argument_extend ~name:"ssrtclarg" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_alias (ssrtacarg);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrtacarg));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrtacarg);
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrtacarg);
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrtacarg);
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 156 "plugins/ssr/ssrparser.mlg"
                 pr_ssrtclarg env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 156 "plugins/ssr/ssrparser.mlg"
                 pr_ssrtclarg env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 156 "plugins/ssr/ssrparser.mlg"
                 pr_ssrtclarg env sigma 
                                                          ));
                                 }
let _ = (wit_ssrtclarg, ssrtclarg)


# 160 "plugins/ssr/ssrparser.mlg"
 

open Genarg

(** Adding a new uninterpreted generic argument type *)
let add_genarg tag pr =
  let wit = Genarg.make0 tag in
  let tag = Geninterp.Val.create tag in
  let glob ist x = (ist, x) in
  let subst _ x = x in
  let interp ist x = Ftactic.return (Geninterp.Val.Dyn (tag, x)) in
  let gen_pr env sigma _ _ _ = pr env sigma in
  let () = Genintern.register_intern0 wit glob in
  let () = Genintern.register_subst0 wit subst in
  let () = Geninterp.register_interp0 wit interp in
  let () = Geninterp.register_val0 wit (Some (Geninterp.Val.Base tag)) in
  Pptactic.declare_extra_genarg_pprule wit gen_pr gen_pr gen_pr;
  wit

open Ssrast
let pr_id = Ppconstr.pr_id
let pr_name = function Name id -> pr_id id | Anonymous -> str "_"
let pr_spc () = str " "
let pr_list = prlist_with_sep

(**************************** ssrhyp **************************************)

let pr_ssrhyp _ _ _ = pr_hyp

let wit_ssrhyprep = add_genarg "ssrhyprep" (fun env sigma -> pr_hyp)

let intern_hyp ist (SsrHyp (loc, id) as hyp) =
  let _ = Tacintern.intern_genarg ist (in_gen (rawwit wit_hyp) CAst.(make ?loc id)) in
  if not_section_id id then hyp else
  hyp_err ?loc "Can't clear section hypothesis " id

open Pcoq.Prim



let (wit_ssrhyp, ssrhyp) = Tacentries.argument_extend ~name:"ssrhyp" 
                           {
                           Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                    [(Pcoq.Production.make
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.stop)
                                                      ((Pcoq.Symbol.nterm ident)))
                                                      (fun id loc -> 
# 203 "plugins/ssr/ssrparser.mlg"
                       SsrHyp (Loc.tag ~loc id) 
                                                                    ))]);
                           Tacentries.arg_tag = Some
                                                (Geninterp.val_tag (Genarg.topwit wit_ssrhyprep));
                           Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                   
# 202 "plugins/ssr/ssrparser.mlg"
                                       intern_hyp 
                                                   ));
                           Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrhyprep);
                           Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                   
# 201 "plugins/ssr/ssrparser.mlg"
                                        interp_hyp 
                                                   );
                           Tacentries.arg_printer = ((fun env sigma -> 
                                                    
# 200 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrhyp 
                                                    ), (fun env sigma -> 
                                                    
# 200 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrhyp 
                                                    ), (fun env sigma -> 
                                                    
# 200 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrhyp 
                                                    ));
                           }
let _ = (wit_ssrhyp, ssrhyp)


# 206 "plugins/ssr/ssrparser.mlg"
 

let pr_hoi = hoik pr_hyp
let pr_ssrhoi _ _ _ = pr_hoi

let wit_ssrhoirep = add_genarg "ssrhoirep" (fun env sigma -> pr_hoi)

let intern_ssrhoi ist = function
  | Hyp h -> Hyp (intern_hyp ist h)
  | Id (SsrHyp (_, id)) as hyp ->
    let _ = Tacintern.intern_genarg ist (in_gen (rawwit wit_ident) id) in
    hyp

let interp_ssrhoi ist env sigma = function
  | Hyp h -> let h' = interp_hyp ist env sigma h in Hyp h'
  | Id (SsrHyp (loc, id)) ->
    let id' = Tacinterp.interp_ident ist env sigma id in
    Id (SsrHyp (loc, id'))



let (wit_ssrhoi_hyp, ssrhoi_hyp) = Tacentries.argument_extend ~name:"ssrhoi_hyp" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm ident)))
                                                              (fun id loc ->
                                                              
# 230 "plugins/ssr/ssrparser.mlg"
                       Hyp (SsrHyp(Loc.tag ~loc id)) 
                                                              ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrhoirep));
                                   Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                           
# 229 "plugins/ssr/ssrparser.mlg"
                                       intern_ssrhoi 
                                                           ));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrhoirep);
                                   Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                           
# 228 "plugins/ssr/ssrparser.mlg"
                                        interp_ssrhoi 
                                                           );
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 227 "plugins/ssr/ssrparser.mlg"
                                                           pr_ssrhoi 
                                                            ), (fun env sigma -> 
                                                            
# 227 "plugins/ssr/ssrparser.mlg"
                                                           pr_ssrhoi 
                                                            ), (fun env sigma -> 
                                                            
# 227 "plugins/ssr/ssrparser.mlg"
                                                           pr_ssrhoi 
                                                            ));
                                   }
let _ = (wit_ssrhoi_hyp, ssrhoi_hyp)

let (wit_ssrhoi_id, ssrhoi_id) = Tacentries.argument_extend ~name:"ssrhoi_id" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm ident)))
                                                            (fun id loc -> 
# 235 "plugins/ssr/ssrparser.mlg"
                       Id (SsrHyp(Loc.tag ~loc id)) 
                                                                    ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrhoirep));
                                 Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                         
# 234 "plugins/ssr/ssrparser.mlg"
                                       intern_ssrhoi 
                                                         ));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrhoirep);
                                 Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                         
# 233 "plugins/ssr/ssrparser.mlg"
                                        interp_ssrhoi 
                                                         );
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 232 "plugins/ssr/ssrparser.mlg"
                                                          pr_ssrhoi 
                                                          ), (fun env sigma -> 
                                                          
# 232 "plugins/ssr/ssrparser.mlg"
                                                          pr_ssrhoi 
                                                          ), (fun env sigma -> 
                                                          
# 232 "plugins/ssr/ssrparser.mlg"
                                                          pr_ssrhoi 
                                                          ));
                                 }
let _ = (wit_ssrhoi_id, ssrhoi_id)


# 240 "plugins/ssr/ssrparser.mlg"
 

let pr_rwdir = function L2R -> mt() | R2L -> str "-"

let wit_ssrdir = add_genarg "ssrdir" (fun env sigma -> pr_dir)

(** Simpl switch *)

let pr_ssrsimpl _ _ _ = pr_simpl

let wit_ssrsimplrep = add_genarg "ssrsimplrep" (fun env sigma -> pr_simpl)

let test_ssrslashnum b1 b2 strm =
  match LStream.peek_nth 0 strm with
  | Tok.KEYWORD "/" ->
      (match LStream.peek_nth 1 strm with
      | Tok.NUMBER _ when b1 ->
         (match LStream.peek_nth 2 strm with
         | Tok.KEYWORD "=" | Tok.KEYWORD "/=" when not b2 -> ()
         | Tok.KEYWORD "/" ->
             if not b2 then () else begin
               match LStream.peek_nth 3 strm with
               | Tok.NUMBER _ -> ()
               | _ -> raise Stream.Failure
             end
         | _ -> raise Stream.Failure)
      | Tok.KEYWORD "/" when not b1 ->
         (match LStream.peek_nth 2 strm with
         | Tok.KEYWORD "=" when not b2 -> ()
         | Tok.NUMBER _ when b2 ->
           (match LStream.peek_nth 3 strm with
           | Tok.KEYWORD "=" -> ()
           | _ -> raise Stream.Failure)
         | _ when not b2 -> ()
         | _ -> raise Stream.Failure)
      | Tok.KEYWORD "=" when not b1 && not b2 -> ()
      | _ -> raise Stream.Failure)
  | Tok.KEYWORD "//" when not b1 ->
         (match LStream.peek_nth 1 strm with
         | Tok.KEYWORD "=" when not b2 -> ()
         | Tok.NUMBER _ when b2 ->
           (match LStream.peek_nth 2 strm with
           | Tok.KEYWORD "=" -> ()
           | _ -> raise Stream.Failure)
         | _ when not b2 -> ()
         | _ -> raise Stream.Failure)
  | _ -> raise Stream.Failure

let test_ssrslashnum10 = test_ssrslashnum true false
let test_ssrslashnum11 = test_ssrslashnum true true
let test_ssrslashnum01 = test_ssrslashnum false true
let test_ssrslashnum00 = test_ssrslashnum false false

let negate_parser f x =
  let rc = try Some (f x) with Stream.Failure -> None in
  match rc with
  | None -> ()
  | Some _ -> raise Stream.Failure

let test_not_ssrslashnum =
  Pcoq.Entry.(of_parser
    "test_not_ssrslashnum" { parser_fun = negate_parser test_ssrslashnum10 })
let test_ssrslashnum00 =
  Pcoq.Entry.(of_parser "test_ssrslashnum01" { parser_fun = test_ssrslashnum00 })
let test_ssrslashnum10 =
  Pcoq.Entry.(of_parser "test_ssrslashnum10" { parser_fun = test_ssrslashnum10 })
let test_ssrslashnum11 =
  Pcoq.Entry.(of_parser "test_ssrslashnum11" { parser_fun = test_ssrslashnum11 })
let test_ssrslashnum01 =
  Pcoq.Entry.(of_parser "test_ssrslashnum01" { parser_fun = test_ssrslashnum01 })



let (wit_ssrsimpl_ne, ssrsimpl_ne) = Tacentries.argument_extend ~name:"ssrsimpl_ne" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "/="))))
                                                                (fun _ loc ->
                                                                
# 315 "plugins/ssr/ssrparser.mlg"
                Simpl ~-1 
                                                                ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "//="))))
                                                               (fun _ loc ->
                                                               
# 314 "plugins/ssr/ssrparser.mlg"
                 SimplCut (~-1,~-1) 
                                                               ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrsimplrep));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrsimplrep);
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrsimplrep);
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrsimplrep);
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 313 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssrsimpl 
                                                              ), (fun env sigma -> 
                                                              
# 313 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssrsimpl 
                                                              ), (fun env sigma -> 
                                                              
# 313 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssrsimpl 
                                                              ));
                                     }
let _ = (wit_ssrsimpl_ne, ssrsimpl_ne)

let _ = let () =
        Pcoq.grammar_extend ssrsimpl_ne
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm test_ssrslashnum00)))
                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("//")))))
                            (fun _ _ loc -> 
# 328 "plugins/ssr/ssrparser.mlg"
                                    Cut ~-1 
                                            );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_ssrslashnum01)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("//")))))
                                                           ((Pcoq.Symbol.nterm natural)))
                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                           (fun _ m _ _ loc -> 
# 327 "plugins/ssr/ssrparser.mlg"
                                                      SimplCut (~-1,m) 
                                               );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_ssrslashnum10)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                                           ((Pcoq.Symbol.nterm natural)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                           (fun _ _ n _ _ loc -> 
# 326 "plugins/ssr/ssrparser.mlg"
                                                          SimplCut (n,~-1) 
                                                 );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_ssrslashnum10)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                                           ((Pcoq.Symbol.nterm natural)))
                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/=")))))
                           (fun _ n _ _ loc -> 
# 325 "plugins/ssr/ssrparser.mlg"
                                                      SimplCut (n,~-1) 
                                               );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_ssrslashnum10)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                                           ((Pcoq.Symbol.nterm natural)))
                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                           (fun _ n _ _ loc -> 
# 324 "plugins/ssr/ssrparser.mlg"
                                                     Simpl n 
                                               );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_ssrslashnum10)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                                           ((Pcoq.Symbol.nterm natural)))
                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                           (fun _ n _ _ loc -> 
# 323 "plugins/ssr/ssrparser.mlg"
                                                     Cut n 
                                               );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_ssrslashnum11)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                                           ((Pcoq.Symbol.nterm natural)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                                           ((Pcoq.Symbol.nterm natural)))
                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                           (fun _ m _ n _ _ loc -> 
# 322 "plugins/ssr/ssrparser.mlg"
                                                                       SimplCut(n,m) 
                                                   )]))
        in ()


# 333 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrclear _ _ _ = pr_clear mt



let (wit_ssrclear_ne, ssrclear_ne) = Tacentries.argument_extend ~name:"ssrclear_ne" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                                ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrhyp)))))
                                                                ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                                (fun _ clr _
                                                                loc -> 
                                                                
# 340 "plugins/ssr/ssrparser.mlg"
                                       check_hyps_uniq [] clr; clr 
                                                                ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.Val.List 
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrhyp)));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                             (wit_ssrhyp));
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                            (wit_ssrhyp));
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                             (wit_ssrhyp));
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 339 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssrclear 
                                                              ), (fun env sigma -> 
                                                              
# 339 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssrclear 
                                                              ), (fun env sigma -> 
                                                              
# 339 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssrclear 
                                                              ));
                                     }
let _ = (wit_ssrclear_ne, ssrclear_ne)

let (wit_ssrclear, ssrclear) = Tacentries.argument_extend ~name:"ssrclear" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.stop)
                                                          (fun loc -> 
# 345 "plugins/ssr/ssrparser.mlg"
           [] 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm ssrclear_ne)))
                                                         (fun clr loc -> 
# 344 "plugins/ssr/ssrparser.mlg"
                            clr 
                                                                    ))]);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrclear_ne));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrclear_ne);
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrclear_ne);
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrclear_ne);
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 343 "plugins/ssr/ssrparser.mlg"
                                                           pr_ssrclear 
                                                        ), (fun env sigma -> 
                                                        
# 343 "plugins/ssr/ssrparser.mlg"
                                                           pr_ssrclear 
                                                        ), (fun env sigma -> 
                                                        
# 343 "plugins/ssr/ssrparser.mlg"
                                                           pr_ssrclear 
                                                        ));
                               }
let _ = (wit_ssrclear, ssrclear)


# 356 "plugins/ssr/ssrparser.mlg"
 

let pr_index = function
  | ArgVar {CAst.v=id} -> pr_id id
  | ArgArg n when n > 0 -> int n
  | _ -> mt ()
let pr_ssrindex _ _ _ = pr_index

let noindex = ArgArg 0

let check_index ?loc i =
  if i > 0 then i else CErrors.user_err ?loc (str"Index not positive")
let mk_index ?loc = function
  | ArgArg i -> ArgArg (check_index ?loc i)
  | iv -> iv

let interp_index ist env sigma idx =
  match idx with
  | ArgArg _ -> idx
  | ArgVar id ->
    let i =
      try
        let v = Id.Map.find id.CAst.v ist.Tacinterp.lfun in
        begin match Tacinterp.Value.to_int v with
        | Some i -> i
        | None ->
        begin match Tacinterp.Value.to_constr v with
        | Some c ->
          let rc = Detyping.detype Detyping.Now false Id.Set.empty env sigma c in
          begin match Notation.uninterp_prim_token rc (None, []) with
          | Constrexpr.Number n, _ when NumTok.Signed.is_int n ->
            int_of_string (NumTok.Signed.to_string n)
          | _ -> raise Not_found
          end
        | None -> raise Not_found
        end end
    with _ -> CErrors.user_err ?loc:id.CAst.loc (str"Index not a number") in
    ArgArg (check_index ?loc:id.CAst.loc i)

open Pltac



let (wit_ssrindex, ssrindex) = Tacentries.argument_extend ~name:"ssrindex" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        []);
                               Tacentries.arg_tag = None;
                               Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                               Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                               Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                       
# 400 "plugins/ssr/ssrparser.mlg"
                   interp_index 
                                                       );
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 399 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrindex 
                                                        ), (fun env sigma -> 
                                                        
# 399 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrindex 
                                                        ), (fun env sigma -> 
                                                        
# 399 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrindex 
                                                        ));
                               }
let _ = (wit_ssrindex, ssrindex)


# 416 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrocc _ _ _ = pr_occ

open Pcoq.Prim



let (wit_ssrocc, ssrocc) = Tacentries.argument_extend ~name:"ssrocc" 
                           {
                           Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                    [(Pcoq.Production.make
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.stop)
                                                      ((Pcoq.Symbol.token (CLexer.terminal "+"))))
                                                      ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm natural))))
                                                      (fun occ _ loc -> 
# 428 "plugins/ssr/ssrparser.mlg"
                                     Some (false, occ) 
                                                                    ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.token (CLexer.terminal "-"))))
                                                     ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm natural))))
                                                     (fun occ _ loc -> 
# 427 "plugins/ssr/ssrparser.mlg"
                                     Some (true, occ) 
                                                                    ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm natural)))
                                                     ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm natural))))
                                                     (fun occ n loc -> 
# 425 "plugins/ssr/ssrparser.mlg"
                                       
     Some (false, List.map (check_index ~loc) (n::occ)) 
                                                                    ))]);
                           Tacentries.arg_tag = Some
                                                (Geninterp.Val.Opt (Geninterp.Val.Pair (
                                                                   (Geninterp.val_tag (Genarg.topwit wit_bool)), 
                                                                   (Geninterp.Val.List 
                                                                   (Geninterp.val_tag (Genarg.topwit wit_int))))));
                           Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.OptArg 
                                                   (Genarg.PairArg ((wit_bool), 
                                                   (Genarg.ListArg (wit_int)))));
                           Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.OptArg 
                                                  (Genarg.PairArg ((wit_bool), 
                                                  (Genarg.ListArg (wit_int)))));
                           Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.OptArg 
                                                   (Genarg.PairArg ((wit_bool), 
                                                   (Genarg.ListArg (wit_int)))));
                           Tacentries.arg_printer = ((fun env sigma -> 
                                                    
# 424 "plugins/ssr/ssrparser.mlg"
                                                                      pr_ssrocc 
                                                    ), (fun env sigma -> 
                                                    
# 424 "plugins/ssr/ssrparser.mlg"
                                                                      pr_ssrocc 
                                                    ), (fun env sigma -> 
                                                    
# 424 "plugins/ssr/ssrparser.mlg"
                                                                      pr_ssrocc 
                                                    ));
                           }
let _ = (wit_ssrocc, ssrocc)


# 434 "plugins/ssr/ssrparser.mlg"
 

let pr_mmod = function May -> str "?" | Must -> str "!" | Once -> mt ()

let wit_ssrmmod = add_genarg "ssrmmod" (fun env sigma -> pr_mmod)
let ssrmmod = Pcoq.create_generic_entry2 "ssrmmod" (Genarg.rawwit wit_ssrmmod);;



let _ = let () = assert (Pcoq.Entry.is_empty ssrmmod) in
        let () =
        Pcoq.grammar_extend ssrmmod
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                  (fun _ loc -> 
# 445 "plugins/ssr/ssrparser.mlg"
                                                                May 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PLEFTQMARK))))
                                 (fun _ loc -> 
# 445 "plugins/ssr/ssrparser.mlg"
                                               May 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                 (fun _ loc -> 
# 445 "plugins/ssr/ssrparser.mlg"
                       Must 
                                               )])]))
        in ()


# 450 "plugins/ssr/ssrparser.mlg"
 

let pr_mult (n, m) =
  if n > 0 && m <> Once then int n ++ pr_mmod m else pr_mmod m

let pr_ssrmult _ _ _ = pr_mult



let (wit_ssrmult_ne, ssrmult_ne) = Tacentries.argument_extend ~name:"ssrmult_ne" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm ssrmmod)))
                                                              (fun m loc -> 
# 461 "plugins/ssr/ssrparser.mlg"
                                   notimes, m 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.nterm natural)))
                                                             ((Pcoq.Symbol.nterm ssrmmod)))
                                                             (fun m n loc ->
                                                             
# 460 "plugins/ssr/ssrparser.mlg"
                                   check_index ~loc n, m 
                                                             ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.Pair (
                                                        (Geninterp.val_tag (Genarg.topwit wit_int)), 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrmmod))));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                           (wit_int), 
                                                           (wit_ssrmmod)));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                          (wit_int), 
                                                          (wit_ssrmmod)));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                           (wit_int), 
                                                           (wit_ssrmmod)));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 459 "plugins/ssr/ssrparser.mlg"
                                                                 pr_ssrmult 
                                                            ), (fun env sigma -> 
                                                            
# 459 "plugins/ssr/ssrparser.mlg"
                                                                 pr_ssrmult 
                                                            ), (fun env sigma -> 
                                                            
# 459 "plugins/ssr/ssrparser.mlg"
                                                                 pr_ssrmult 
                                                            ));
                                   }
let _ = (wit_ssrmult_ne, ssrmult_ne)

let (wit_ssrmult, ssrmult) = Tacentries.argument_extend ~name:"ssrmult" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.stop)
                                                        (fun loc -> 
# 466 "plugins/ssr/ssrparser.mlg"
             nomult 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ssrmult_ne)))
                                                       (fun m loc -> 
# 465 "plugins/ssr/ssrparser.mlg"
                           m 
                                                                    ))]);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssrmult_ne));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrmult_ne);
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrmult_ne);
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrmult_ne);
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 464 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssrmult 
                                                      ), (fun env sigma -> 
                                                      
# 464 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssrmult 
                                                      ), (fun env sigma -> 
                                                      
# 464 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssrmult 
                                                      ));
                             }
let _ = (wit_ssrmult, ssrmult)


# 469 "plugins/ssr/ssrparser.mlg"
 

(** Discharge occ switch (combined occurrence / clear switch *)

let pr_docc = function
  | None, occ -> pr_occ occ
  | Some clr, _ -> pr_clear mt clr

let pr_ssrdocc _ _ _ = pr_docc



let (wit_ssrdocc, ssrdocc) = Tacentries.argument_extend ~name:"ssrdocc" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                        ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ssrhyp))))
                                                        ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                        (fun _ clr _ loc -> 
# 483 "plugins/ssr/ssrparser.mlg"
                                    mkclr clr 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                       ((Pcoq.Symbol.nterm ssrocc)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                       (fun _ occ _ loc -> 
# 482 "plugins/ssr/ssrparser.mlg"
                               mkocc occ 
                                                                    ))]);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.Val.Pair (
                                                  (Geninterp.Val.Opt 
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssrclear))), 
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssrocc))));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                     (Genarg.OptArg (wit_ssrclear)), 
                                                     (wit_ssrocc)));
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                    (Genarg.OptArg (wit_ssrclear)), 
                                                    (wit_ssrocc)));
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                     (Genarg.OptArg (wit_ssrclear)), 
                                                     (wit_ssrocc)));
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 481 "plugins/ssr/ssrparser.mlg"
                                                                         pr_ssrdocc 
                                                      ), (fun env sigma -> 
                                                      
# 481 "plugins/ssr/ssrparser.mlg"
                                                                         pr_ssrdocc 
                                                      ), (fun env sigma -> 
                                                      
# 481 "plugins/ssr/ssrparser.mlg"
                                                                         pr_ssrdocc 
                                                      ));
                             }
let _ = (wit_ssrdocc, ssrdocc)


# 486 "plugins/ssr/ssrparser.mlg"
 

(* Old kinds of terms *)

let input_ssrtermkind strm = match LStream.peek_nth 0 strm with
  | Tok.KEYWORD "(" -> InParens
  | Tok.KEYWORD "@" -> WithAt
  | _ -> NoFlag

let ssrtermkind = Pcoq.Entry.(of_parser "ssrtermkind" { parser_fun = input_ssrtermkind })

(* New kinds of terms *)

let input_term_annotation strm =
  match LStream.npeek 2 strm with
  | Tok.KEYWORD "(" :: Tok.KEYWORD "(" :: _ -> `DoubleParens
  | Tok.KEYWORD "(" :: _ -> `Parens
  | Tok.KEYWORD "@" :: _ -> `At
  | _ -> `None
let term_annotation =
  Pcoq.Entry.(of_parser "term_annotation" { parser_fun = input_term_annotation })

(* terms *)

(** Terms parsing. ********************************************************)

(* Because we allow wildcards in term references, we need to stage the *)
(* interpretation of terms so that it occurs at the right time during  *)
(* the execution of the tactic (e.g., so that we don't report an error *)
(* for a term that isn't actually used in the execution).              *)
(*   The term representation tracks whether the concrete initial term  *)
(* started with an opening paren, which might avoid a conflict between *)
(* the ssrreflect term syntax and Gallina notation.                    *)

(* Old terms *)
let pr_ssrterm _ _ _ = pr_term
let glob_ssrterm gs = function
  | k, (_, Some c) -> k, Tacintern.intern_constr gs c
  | ct -> ct
let subst_ssrterm s (k, c) = k, Tacsubst.subst_glob_constr_and_expr s c
let interp_ssrterm _ _ _ t = t

open Pcoq.Constr



let (wit_ssrterm, ssrterm) = Tacentries.argument_extend ~name:"ssrterm" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      []);
                             Tacentries.arg_tag = None;
                             Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                     
# 535 "plugins/ssr/ssrparser.mlg"
                     glob_ssrterm 
                                                     ));
                             Tacentries.arg_subst = Tacentries.ArgSubstFun (
# 535 "plugins/ssr/ssrparser.mlg"
                                                     subst_ssrterm 
                                                    );
                             Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                     
# 534 "plugins/ssr/ssrparser.mlg"
                      interp_ssrterm 
                                                     );
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 536 "plugins/ssr/ssrparser.mlg"
                      pr_ssrterm 
                                                      ), (fun env sigma -> 
                                                      
# 537 "plugins/ssr/ssrparser.mlg"
                       pr_ssrterm 
                                                      ), (fun env sigma -> 
                                                      
# 533 "plugins/ssr/ssrparser.mlg"
                  pr_ssrterm 
                                                      ));
                             }
let _ = (wit_ssrterm, ssrterm)

let _ = let () =
        Pcoq.grammar_extend ssrterm
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm ssrtermkind)))
                                            ((Pcoq.Symbol.nterm Pcoq.Constr.constr)))
                            (fun c k loc -> 
# 542 "plugins/ssr/ssrparser.mlg"
                                                               mk_term k c 
                                            )]))
        in ()


# 547 "plugins/ssr/ssrparser.mlg"
 

let pp_ast_closure_term _ _ _ = pr_ast_closure_term



let (wit_ast_closure_term, ast_closure_term) = Tacentries.argument_extend ~name:"ast_closure_term" 
                                               {
                                               Tacentries.arg_parsing = 
                                               Vernacextend.Arg_rules (
                                               [(Pcoq.Production.make
                                                 (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm term_annotation)))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                 (fun c a loc -> 
# 560 "plugins/ssr/ssrparser.mlg"
                                          mk_ast_closure_term a c 
                                                                 ))]);
                                               Tacentries.arg_tag = None;
                                               Tacentries.arg_intern = 
                                               Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                               
# 556 "plugins/ssr/ssrparser.mlg"
                     glob_ast_closure_term 
                                               ));
                                               Tacentries.arg_subst = 
                                               Tacentries.ArgSubstFun (
# 557 "plugins/ssr/ssrparser.mlg"
                      subst_ast_closure_term 
                                               );
                                               Tacentries.arg_interp = 
                                               Tacentries.ArgInterpSimple (
# 555 "plugins/ssr/ssrparser.mlg"
                      interp_ast_closure_term 
                                               );
                                               Tacentries.arg_printer = 
                                               ((fun env sigma -> 
# 558 "plugins/ssr/ssrparser.mlg"
                      pp_ast_closure_term 
                                               ), (fun env sigma -> 
# 559 "plugins/ssr/ssrparser.mlg"
                       pp_ast_closure_term 
                                               ), (fun env sigma -> 
# 554 "plugins/ssr/ssrparser.mlg"
                  pp_ast_closure_term 
                                               ));
                                               }
let _ = (wit_ast_closure_term, ast_closure_term)

let (wit_ast_closure_lterm, ast_closure_lterm) = Tacentries.argument_extend ~name:"ast_closure_lterm" 
                                                 {
                                                 Tacentries.arg_parsing = 
                                                 Vernacextend.Arg_rules (
                                                 [(Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.nterm term_annotation)))
                                                                   ((Pcoq.Symbol.nterm lconstr)))
                                                   (fun c a loc -> 
# 569 "plugins/ssr/ssrparser.mlg"
                                           mk_ast_closure_term a c 
                                                                   ))]);
                                                 Tacentries.arg_tag = 
                                                 None;
                                                 Tacentries.arg_intern = 
                                                 Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                 
# 565 "plugins/ssr/ssrparser.mlg"
                     glob_ast_closure_term 
                                                 ));
                                                 Tacentries.arg_subst = 
                                                 Tacentries.ArgSubstFun (
# 566 "plugins/ssr/ssrparser.mlg"
                      subst_ast_closure_term 
                                                 );
                                                 Tacentries.arg_interp = 
                                                 Tacentries.ArgInterpSimple (
                                                 
# 564 "plugins/ssr/ssrparser.mlg"
                      interp_ast_closure_term 
                                                 );
                                                 Tacentries.arg_printer = 
                                                 ((fun env sigma -> 
# 567 "plugins/ssr/ssrparser.mlg"
                      pp_ast_closure_term 
                                                 ), (fun env sigma -> 
                                                 
# 568 "plugins/ssr/ssrparser.mlg"
                       pp_ast_closure_term 
                                                 ), (fun env sigma -> 
                                                 
# 563 "plugins/ssr/ssrparser.mlg"
                  pp_ast_closure_term 
                                                 ));
                                                 }
let _ = (wit_ast_closure_lterm, ast_closure_lterm)


# 574 "plugins/ssr/ssrparser.mlg"
 

let pr_view = pr_list mt (fun c -> str "/" ++ pr_term c)

let pr_ssrbwdview _ _ _ = pr_view



let (wit_ssrbwdview, ssrbwdview) = Tacentries.argument_extend ~name:"ssrbwdview" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            []);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.List 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrterm)));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                           (wit_ssrterm));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                          (wit_ssrterm));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                           (wit_ssrterm));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 583 "plugins/ssr/ssrparser.mlg"
                pr_ssrbwdview 
                                                            ), (fun env sigma -> 
                                                            
# 583 "plugins/ssr/ssrparser.mlg"
                pr_ssrbwdview 
                                                            ), (fun env sigma -> 
                                                            
# 583 "plugins/ssr/ssrparser.mlg"
                pr_ssrbwdview 
                                                            ));
                                   }
let _ = (wit_ssrbwdview, ssrbwdview)

let _ = let () =
        Pcoq.grammar_extend ssrbwdview
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm test_not_ssrslashnum)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                                            ((Pcoq.Symbol.nterm Pcoq.Constr.constr)))
                                            ((Pcoq.Symbol.nterm ssrbwdview)))
                            (fun w c _ _ loc -> 
# 591 "plugins/ssr/ssrparser.mlg"
                                                                             
                    (mk_term NoFlag c) :: w 
                                                );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_not_ssrslashnum)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                           ((Pcoq.Symbol.nterm Pcoq.Constr.constr)))
                           (fun c _ _ loc -> 
# 590 "plugins/ssr/ssrparser.mlg"
                                                              [mk_term NoFlag c] 
                                             )]))
        in ()


# 597 "plugins/ssr/ssrparser.mlg"
 

type ssrfwdview = ast_closure_term list

let pr_ssrfwdview _ _ _ = pr_view2



let (wit_ssrfwdview, ssrfwdview) = Tacentries.argument_extend ~name:"ssrfwdview" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            []);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.List 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ast_closure_term)));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                           (wit_ast_closure_term));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                          (wit_ast_closure_term));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                           (wit_ast_closure_term));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 606 "plugins/ssr/ssrparser.mlg"
                pr_ssrfwdview 
                                                            ), (fun env sigma -> 
                                                            
# 606 "plugins/ssr/ssrparser.mlg"
                pr_ssrfwdview 
                                                            ), (fun env sigma -> 
                                                            
# 606 "plugins/ssr/ssrparser.mlg"
                pr_ssrfwdview 
                                                            ));
                                   }
let _ = (wit_ssrfwdview, ssrfwdview)

let _ = let () =
        Pcoq.grammar_extend ssrfwdview
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm test_not_ssrslashnum)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                                            ((Pcoq.Symbol.nterm ast_closure_term)))
                                            ((Pcoq.Symbol.nterm ssrfwdview)))
                            (fun w c _ _ loc -> 
# 614 "plugins/ssr/ssrparser.mlg"
                                                                            c :: w 
                                                );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_not_ssrslashnum)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                           ((Pcoq.Symbol.nterm ast_closure_term)))
                           (fun c _ _ loc -> 
# 613 "plugins/ssr/ssrparser.mlg"
                                                            [c] 
                                             )]))
        in ()


# 619 "plugins/ssr/ssrparser.mlg"
 

let remove_loc x = x.CAst.v

let ipat_of_intro_pattern p = Tactypes.(
  let rec ipat_of_intro_pattern = function
    | IntroNaming (IntroIdentifier id) -> IPatId id
    | IntroAction IntroWildcard -> IPatAnon Drop
    | IntroAction (IntroOrAndPattern (IntroOrPattern iorpat)) ->
      IPatCase (Regular(
       List.map (List.map ipat_of_intro_pattern)
         (List.map (List.map remove_loc) iorpat)))
    | IntroAction (IntroOrAndPattern (IntroAndPattern iandpat)) ->
      IPatCase
       (Regular [List.map ipat_of_intro_pattern (List.map remove_loc iandpat)])
    | IntroNaming IntroAnonymous -> IPatAnon (One None)
    | IntroAction (IntroRewrite b) -> IPatRewrite (allocc, if b then L2R else R2L)
    | IntroNaming (IntroFresh id) -> IPatAnon (One None)
    | IntroAction (IntroApplyOn _) -> (* to do *) CErrors.user_err (Pp.str "TO DO")
    | IntroAction (IntroInjection ips) ->
        IPatInj [List.map ipat_of_intro_pattern (List.map remove_loc ips)]
    | IntroForthcoming _ ->
        (* Unable to determine which kind of ipat interp_introid could
         * return [HH] *)
        assert false
  in
  ipat_of_intro_pattern p
)

let rec map_ipat map_id map_ssrhyp map_ast_closure_term = function
  | (IPatSimpl _ | IPatAnon _ | IPatRewrite _ | IPatNoop | IPatFastNondep) as x -> x
  | IPatId id -> IPatId (map_id id)
  | IPatAbstractVars l -> IPatAbstractVars (List.map map_id l)
  | IPatClear clr -> IPatClear (List.map map_ssrhyp clr)
  | IPatCase (Regular iorpat) -> IPatCase (Regular (List.map (List.map (map_ipat map_id map_ssrhyp map_ast_closure_term)) iorpat))
  | IPatCase (Block(hat)) -> IPatCase (Block(map_block map_id hat))
  | IPatDispatch (Regular iorpat) -> IPatDispatch (Regular (List.map (List.map (map_ipat map_id map_ssrhyp map_ast_closure_term)) iorpat))
  | IPatDispatch (Block (hat)) -> IPatDispatch (Block(map_block map_id hat))
  | IPatInj iorpat -> IPatInj (List.map (List.map (map_ipat map_id map_ssrhyp map_ast_closure_term)) iorpat)
  | IPatView v -> IPatView (List.map map_ast_closure_term v)
and map_block map_id = function
  | Prefix id -> Prefix (map_id id)
  | SuffixId id -> SuffixId (map_id id)
  | SuffixNum _ as x -> x

type ssripatrep = ssripat
let wit_ssripatrep = add_genarg "ssripatrep" (fun env sigma -> pr_ipat)

let pr_ssripat _ _ _ = pr_ipat
let pr_ssripats _ _ _ = pr_ipats
let pr_ssriorpat _ _ _ = pr_iorpat

let intern_ipat ist =
  map_ipat
    (fun id -> id)
    (intern_hyp ist)
    (glob_ast_closure_term ist)

let intern_ipats ist = List.map (intern_ipat ist)
let intern_ipat_option ist = Option.map (intern_ipat ist)

let interp_intro_pattern = Tacinterp.interp_intro_pattern

let interp_introid ist env sigma id =
 try IntroNaming (IntroIdentifier (hyp_id (interp_hyp ist env sigma (SsrHyp (Loc.tag id)))))
 with _ -> (interp_intro_pattern ist env sigma (CAst.make @@ IntroNaming (IntroIdentifier id))).CAst.v

let get_intro_id = function
  | IntroNaming (IntroIdentifier id) -> id
  | _ -> assert false

let rec add_intro_pattern_hyps ipat hyps =
  let {CAst.loc; v=ipat} = ipat in
  match ipat with
  | IntroNaming (IntroIdentifier id) ->
    if not_section_id id then SsrHyp (loc, id) :: hyps else
    hyp_err ?loc "Can't delete section hypothesis " id
  | IntroAction IntroWildcard -> hyps
  | IntroAction (IntroOrAndPattern (IntroOrPattern iorpat)) ->
     List.fold_right (List.fold_right add_intro_pattern_hyps) iorpat hyps
  | IntroAction (IntroOrAndPattern (IntroAndPattern iandpat)) ->
    List.fold_right add_intro_pattern_hyps iandpat hyps
  | IntroNaming IntroAnonymous -> []
  | IntroNaming (IntroFresh _) -> []
  | IntroAction (IntroRewrite _) -> hyps
  | IntroAction (IntroInjection ips) -> List.fold_right add_intro_pattern_hyps ips hyps
  | IntroAction (IntroApplyOn (c,pat)) -> add_intro_pattern_hyps pat hyps
  | IntroForthcoming _ ->
    (* As in ipat_of_intro_pattern, was unable to determine which kind
      of ipat interp_introid could return [HH] *) assert false

(* We interp the ipat using the standard ltac machinery for ids, since
 * we have no clue what a name could be bound to (maybe another ipat) *)
let interp_ipat ist env sigma =
  let ltacvar id = Id.Map.mem id ist.Tacinterp.lfun in
  let interp_block = function
    | Prefix id when ltacvar id ->
        begin match interp_introid ist env sigma id with
        | IntroNaming (IntroIdentifier id) -> Prefix id
        | _ -> Ssrcommon.errorstrm Pp.(str"Variable " ++ Id.print id ++ str" in block intro pattern should be bound to an identifier.")
        end
    | SuffixId id when ltacvar id ->
        begin match interp_introid ist env sigma id with
        | IntroNaming (IntroIdentifier id) -> SuffixId id
        | _ -> Ssrcommon.errorstrm Pp.(str"Variable " ++ Id.print id ++ str" in block intro pattern should be bound to an identifier.")
        end
    | x -> x in
  let rec interp = function
  | IPatId id when ltacvar id ->
    ipat_of_intro_pattern (interp_introid ist env sigma id)
  | IPatId _ as x -> x
  | IPatClear clr ->
    let add_hyps (SsrHyp (loc, id) as hyp) hyps =
      if not (ltacvar id) then hyp :: hyps else
      add_intro_pattern_hyps CAst.(make ?loc (interp_introid ist env sigma id)) hyps in
    let clr' = List.fold_right add_hyps clr [] in
    check_hyps_uniq [] clr';
    IPatClear clr'
  | IPatCase(Regular iorpat) ->
      IPatCase(Regular(List.map (List.map interp) iorpat))
  | IPatCase(Block(hat)) -> IPatCase(Block(interp_block hat))

  | IPatDispatch(Regular iorpat) ->
      IPatDispatch(Regular (List.map (List.map interp) iorpat))
  | IPatDispatch(Block(hat)) -> IPatDispatch(Block(interp_block hat))

  | IPatInj iorpat -> IPatInj (List.map (List.map interp) iorpat)
  | IPatAbstractVars l ->
     IPatAbstractVars (List.map get_intro_id (List.map (interp_introid ist env sigma) l))
  | IPatView l -> IPatView (List.map (fun x -> interp_ast_closure_term ist
     env sigma x) l)
  | (IPatSimpl _ | IPatAnon _ | IPatRewrite _ | IPatNoop | IPatFastNondep) as x -> x
    in
  interp

let interp_ipats ist env sigma l = List.map (interp_ipat ist env sigma) l
let interp_ipat_option ist env sigma o = Option.map (interp_ipat ist env sigma) o

let pushIPatRewrite = function
  | pats :: orpat -> (IPatRewrite (allocc, L2R) :: pats) :: orpat
  | [] -> []

let pushIPatNoop = function
  | pats :: orpat -> (IPatNoop :: pats) :: orpat
  | [] -> []

let test_ident_no_do =
  let open Pcoq.Lookahead in
  to_entry "test_ident_no_do" begin
    lk_ident_except ["do"]
  end



let (wit_ident_no_do, ident_no_do) = Tacentries.argument_extend ~name:"ident_no_do" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              []);
                                     Tacentries.arg_tag = None;
                                     Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                     Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                     Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 773 "plugins/ssr/ssrparser.mlg"
                                         fun _ _ _ -> Names.Id.print 
                                                              ), (fun env sigma -> 
                                                              
# 773 "plugins/ssr/ssrparser.mlg"
                                         fun _ _ _ -> Names.Id.print 
                                                              ), (fun env sigma -> 
                                                              
# 773 "plugins/ssr/ssrparser.mlg"
                                         fun _ _ _ -> Names.Id.print 
                                                              ));
                                     }
let _ = (wit_ident_no_do, ident_no_do)

let _ = let () =
        Pcoq.grammar_extend ident_no_do
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm test_ident_no_do)))
                                            ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                            (fun id _ loc -> 
# 779 "plugins/ssr/ssrparser.mlg"
                                                         Id.of_string id 
                                             )]))
        in ()

let (wit_ssripat, ssripat) = Tacentries.argument_extend ~name:"ssripat" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.token (CLexer.terminal "[:"))))
                                                        ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ident))))
                                                        ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                        (fun _ idl _ loc -> 
# 820 "plugins/ssr/ssrparser.mlg"
                                      [IPatAbstractVars idl] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                       ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                       ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ident))))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                       (fun _ idl _ _ loc ->
                                                       
# 819 "plugins/ssr/ssrparser.mlg"
                                         [IPatAbstractVars idl] 
                                                       ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ssrfwdview)))
                                                       (fun v loc -> 
# 818 "plugins/ssr/ssrparser.mlg"
                           [IPatView v] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-/"))))
                                                       ((Pcoq.Symbol.nterm integer)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "/"))))
                                                       ((Pcoq.Symbol.nterm integer)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "="))))
                                                       (fun _ m _ n _ loc ->
                                                       
# 817 "plugins/ssr/ssrparser.mlg"
        [IPatNoop;IPatSimpl(SimplCut(n,m))] 
                                                       ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-/"))))
                                                       ((Pcoq.Symbol.nterm integer)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "/="))))
                                                       (fun _ n _ loc -> 
# 815 "plugins/ssr/ssrparser.mlg"
                                  [IPatNoop;IPatSimpl(SimplCut (n,~-1))] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-//="))))
                                                       (fun _ loc -> 
# 814 "plugins/ssr/ssrparser.mlg"
                    [IPatNoop;IPatSimpl(SimplCut (~-1,~-1))] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-//"))))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "="))))
                                                       (fun _ _ loc -> 
# 813 "plugins/ssr/ssrparser.mlg"
                       [IPatNoop;IPatSimpl(SimplCut (~-1,~-1))] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-/"))))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "/="))))
                                                       (fun _ _ loc -> 
# 812 "plugins/ssr/ssrparser.mlg"
                       [IPatNoop;IPatSimpl(SimplCut (~-1,~-1))] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-/"))))
                                                       ((Pcoq.Symbol.nterm integer)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "/"))))
                                                       (fun _ n _ loc -> 
# 811 "plugins/ssr/ssrparser.mlg"
                                 [IPatNoop;IPatSimpl(Cut n)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-//"))))
                                                       (fun _ loc -> 
# 810 "plugins/ssr/ssrparser.mlg"
                   [IPatNoop;IPatSimpl(Cut ~-1)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-/"))))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "/"))))
                                                       (fun _ _ loc -> 
# 809 "plugins/ssr/ssrparser.mlg"
                      [IPatNoop;IPatSimpl(Cut ~-1)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-/="))))
                                                       (fun _ loc -> 
# 808 "plugins/ssr/ssrparser.mlg"
                   [IPatNoop;IPatSimpl(Simpl ~-1)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-/"))))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "="))))
                                                       (fun _ _ loc -> 
# 807 "plugins/ssr/ssrparser.mlg"
                      [IPatNoop;IPatSimpl(Simpl ~-1)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "-"))))
                                                       (fun _ loc -> 
# 806 "plugins/ssr/ssrparser.mlg"
                 [IPatNoop] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "<-"))))
                                                       (fun _ loc -> 
# 805 "plugins/ssr/ssrparser.mlg"
                  [IPatRewrite (allocc, R2L)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "->"))))
                                                       (fun _ loc -> 
# 804 "plugins/ssr/ssrparser.mlg"
                  [IPatRewrite (allocc, L2R)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ssrdocc)))
                                                       (fun occ loc -> 
# 801 "plugins/ssr/ssrparser.mlg"
                          match occ with
      | Some cl, _ -> check_hyps_uniq [] cl; [IPatClear cl]
      | _ -> CErrors.user_err ~loc (str"Only identifiers are allowed here") 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ssrdocc)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "<-"))))
                                                       (fun _ occ loc -> 
# 797 "plugins/ssr/ssrparser.mlg"
                               match occ with
      | Some [], _ -> CErrors.user_err ~loc (str"occ_switch expected")
      | None, occ ->  [IPatRewrite (occ, R2L)]
      | Some clr, _ -> [IPatClear clr; IPatRewrite (allocc, R2L)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ssrdocc)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "->"))))
                                                       (fun _ occ loc -> 
# 793 "plugins/ssr/ssrparser.mlg"
                               match occ with
      | Some [], _ -> CErrors.user_err ~loc (str"occ_switch expected")
      | None, occ -> [IPatRewrite (occ, L2R)]
      | Some clr, _ -> [IPatClear clr; IPatRewrite (allocc, L2R)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ssrsimpl_ne)))
                                                       (fun sim loc -> 
# 792 "plugins/ssr/ssrparser.mlg"
                              [IPatSimpl sim] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "++"))))
                                                       (fun _ loc -> 
# 791 "plugins/ssr/ssrparser.mlg"
                  [IPatAnon Temporary; IPatAnon Temporary] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "+"))))
                                                       (fun _ loc -> 
# 790 "plugins/ssr/ssrparser.mlg"
                 [IPatAnon Temporary] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "?"))))
                                                       (fun _ loc -> 
# 789 "plugins/ssr/ssrparser.mlg"
                 [IPatAnon (One None)] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ident_no_do)))
                                                       (fun id loc -> 
# 788 "plugins/ssr/ssrparser.mlg"
                             [IPatId id] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal ">"))))
                                                       (fun _ loc -> 
# 787 "plugins/ssr/ssrparser.mlg"
                 [IPatFastNondep] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "*"))))
                                                       (fun _ loc -> 
# 786 "plugins/ssr/ssrparser.mlg"
                 [IPatAnon All] 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "_"))))
                                                       (fun _ loc -> 
# 785 "plugins/ssr/ssrparser.mlg"
                 [IPatAnon Drop] 
                                                                    ))]);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.Val.List 
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssripatrep)));
                             Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                     
# 784 "plugins/ssr/ssrparser.mlg"
                  intern_ipats 
                                                     ));
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                    (wit_ssripatrep));
                             Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                     
# 783 "plugins/ssr/ssrparser.mlg"
                   interp_ipats 
                                                     );
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 782 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssripats 
                                                      ), (fun env sigma -> 
                                                      
# 782 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssripats 
                                                      ), (fun env sigma -> 
                                                      
# 782 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssripats 
                                                      ));
                             }
let _ = (wit_ssripat, ssripat)

let (wit_ssripats, ssripats) = Tacentries.argument_extend ~name:"ssripats" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.stop)
                                                          (fun loc -> 
# 825 "plugins/ssr/ssrparser.mlg"
             [] 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm ssripat)))
                                                         (Pcoq.Symbol.self))
                                                         (fun tl i loc -> 
# 824 "plugins/ssr/ssrparser.mlg"
                                     i @ tl 
                                                                    ))]);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssripat));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssripat);
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssripat);
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssripat);
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 823 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssripats 
                                                        ), (fun env sigma -> 
                                                        
# 823 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssripats 
                                                        ), (fun env sigma -> 
                                                        
# 823 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssripats 
                                                        ));
                               }
let _ = (wit_ssripats, ssripats)

let (wit_ssriorpat, ssriorpat) = Tacentries.argument_extend ~name:"ssriorpat" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm ssripats)))
                                                            (fun pats loc ->
                                                            
# 836 "plugins/ssr/ssrparser.mlg"
                          [pats] 
                                                            ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssripats)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "||||"))))
                                                           (Pcoq.Symbol.self))
                                                           (fun orpat _ pats
                                                           loc -> 
# 835 "plugins/ssr/ssrparser.mlg"
                                                  [pats; []; []; []] @ orpat 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssripats)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "|||"))))
                                                           (Pcoq.Symbol.self))
                                                           (fun orpat _ pats
                                                           loc -> 
# 834 "plugins/ssr/ssrparser.mlg"
                                                 pats :: [] :: [] :: orpat 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssripats)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "||"))))
                                                           (Pcoq.Symbol.self))
                                                           (fun orpat _ pats
                                                           loc -> 
# 833 "plugins/ssr/ssrparser.mlg"
                                                pats :: [] :: orpat 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssripats)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "|->"))))
                                                           (Pcoq.Symbol.self))
                                                           (fun orpat _ pats
                                                           loc -> 
# 832 "plugins/ssr/ssrparser.mlg"
                                                 pats :: pushIPatRewrite orpat 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssripats)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "|-"))))
                                                           (Pcoq.Symbol.self))
                                                           (fun orpat _ pats
                                                           loc -> 
# 831 "plugins/ssr/ssrparser.mlg"
                                                pats :: pushIPatNoop orpat 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssripats)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "|-"))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ">"))))
                                                           (Pcoq.Symbol.self))
                                                           (fun orpat _ _
                                                           pats loc -> 
                                                           
# 830 "plugins/ssr/ssrparser.mlg"
                                                    pats :: pushIPatRewrite orpat 
                                                           ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssripats)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "|"))))
                                                           (Pcoq.Symbol.self))
                                                           (fun orpat _ pats
                                                           loc -> 
# 829 "plugins/ssr/ssrparser.mlg"
                                               pats :: orpat 
                                                                  ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.Val.List 
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssripat)));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                         (wit_ssripat));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                        (wit_ssripat));
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                         (wit_ssripat));
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 828 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssriorpat 
                                                          ), (fun env sigma -> 
                                                          
# 828 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssriorpat 
                                                          ), (fun env sigma -> 
                                                          
# 828 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssriorpat 
                                                          ));
                                 }
let _ = (wit_ssriorpat, ssriorpat)


# 839 "plugins/ssr/ssrparser.mlg"
 

let reject_ssrhid strm =
  match LStream.peek_nth 0 strm with
  | Tok.KEYWORD "[" ->
      (match LStream.peek_nth 1 strm with
      | Tok.KEYWORD ":" -> raise Stream.Failure
      | _ -> ())
  | _ -> ()

let test_nohidden = Pcoq.Entry.(of_parser "test_ssrhid" { parser_fun = reject_ssrhid })

let rec reject_binder crossed_paren k s =
  match
    try Some (LStream.peek_nth k s)
    with Stream.Failure -> None
  with
  | Some (Tok.KEYWORD "(") when not crossed_paren -> reject_binder true (k+1) s
  | Some (Tok.IDENT _) when crossed_paren -> reject_binder true (k+1) s
  | Some (Tok.KEYWORD ":" | Tok.KEYWORD ":=") when crossed_paren ->
      raise Stream.Failure
  | Some (Tok.KEYWORD ")") when crossed_paren -> raise Stream.Failure
  | _ -> if crossed_paren then () else raise Stream.Failure

let _test_nobinder = Pcoq.Entry.(of_parser "test_nobinder" { parser_fun = reject_binder false 0 })



let (wit_ssrcpat, ssrcpat) = Tacentries.argument_extend ~name:"ssrcpat" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      []);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssripatrep));
                             Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                     
# 869 "plugins/ssr/ssrparser.mlg"
                  intern_ipat 
                                                     ));
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssripatrep);
                             Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                     
# 868 "plugins/ssr/ssrparser.mlg"
                   interp_ipat 
                                                     );
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 867 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssripat 
                                                      ), (fun env sigma -> 
                                                      
# 867 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssripat 
                                                      ), (fun env sigma -> 
                                                      
# 867 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssripat 
                                                      ));
                             }
let _ = (wit_ssrcpat, ssrcpat)

let _ = let hat = Pcoq.Entry.make "hat"
        in
        let () = assert (Pcoq.Entry.is_empty hat) in
        let () =
        Pcoq.grammar_extend hat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("^~")))))
                                                  ((Pcoq.Symbol.nterm natural)))
                                  (fun n _ loc -> 
# 881 "plugins/ssr/ssrparser.mlg"
                           SuffixNum n 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("^~")))))
                                                 ((Pcoq.Symbol.nterm ident)))
                                 (fun id _ loc -> 
# 880 "plugins/ssr/ssrparser.mlg"
                          SuffixId id 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("^")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("~")))))
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n _ _ loc -> 
# 879 "plugins/ssr/ssrparser.mlg"
                               SuffixNum n 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("^")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("~")))))
                                                 ((Pcoq.Symbol.nterm ident)))
                                 (fun id _ _ loc -> 
# 878 "plugins/ssr/ssrparser.mlg"
                              SuffixId id 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("^")))))
                                                 ((Pcoq.Symbol.nterm ident)))
                                 (fun id _ loc -> 
# 877 "plugins/ssr/ssrparser.mlg"
                         Prefix id 
                                                  )])]))
        in let () =
        Pcoq.grammar_extend ssrcpat
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm test_nohidden)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("[=")))))
                                                            ((Pcoq.Symbol.nterm ssriorpat)))
                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                            (fun _ iorpat _ _ loc -> 
# 888 "plugins/ssr/ssrparser.mlg"
                                                      
      IPatInj iorpat 
                                                     );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_nohidden)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                           ((Pcoq.Symbol.nterm ssriorpat)))
                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                           (fun _ iorpat _ _ loc -> 
# 886 "plugins/ssr/ssrparser.mlg"
                                                     
      IPatCase (Regular iorpat) 
                                                    );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_nohidden)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                           ((Pcoq.Symbol.nterm hat)))
                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                           (fun _ hat_id _ _ loc -> 
# 884 "plugins/ssr/ssrparser.mlg"
                                               
      IPatCase (Block(hat_id)) 
                                                    )]))
        in ()

let _ = let () =
        Pcoq.grammar_extend ssripat
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.stop)
                                            ((Pcoq.Symbol.nterm ssrcpat)))
                            (fun pat loc -> 
# 894 "plugins/ssr/ssrparser.mlg"
                                     [pat] 
                                            )]))
        in ()

let (wit_ssripats_ne, ssripats_ne) = Tacentries.argument_extend ~name:"ssripats_ne" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ssripat)))
                                                                ((Pcoq.Symbol.nterm ssripats)))
                                                                (fun tl i
                                                                loc -> 
                                                                
# 898 "plugins/ssr/ssrparser.mlg"
                                     i @ tl 
                                                                ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssripat));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssripat);
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssripat);
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssripat);
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 897 "plugins/ssr/ssrparser.mlg"
                                                          pr_ssripats 
                                                              ), (fun env sigma -> 
                                                              
# 897 "plugins/ssr/ssrparser.mlg"
                                                          pr_ssripats 
                                                              ), (fun env sigma -> 
                                                              
# 897 "plugins/ssr/ssrparser.mlg"
                                                          pr_ssripats 
                                                              ));
                                     }
let _ = (wit_ssripats_ne, ssripats_ne)


# 903 "plugins/ssr/ssrparser.mlg"
 

(* TODO: review what this function does, it looks suspicious *)
let check_ssrhpats loc w_binders ipats =
  let err_loc s = CErrors.user_err ~loc s in
  let clr, ipats =
    let opt_app = function None -> fun l -> Some l
      | Some l1 -> fun l2 -> Some (l1 @ l2) in
    let rec aux clr = function
      | IPatClear cl :: tl -> aux (opt_app clr cl) tl
      | tl -> clr, tl
    in aux None ipats in
  let simpl, ipats =
    match List.rev ipats with
    | IPatSimpl _ as s :: tl -> [s], List.rev tl
    | _ -> [],  ipats in
  if simpl <> [] && not w_binders then
    err_loc (str "No s-item allowed here: " ++ pr_ipats simpl);
  let ipat, binders =
    let rec loop ipat = function
      | [] -> ipat, []
      | ( IPatId _| IPatAnon _| IPatCase _ | IPatDispatch _ | IPatRewrite _ as i) :: tl ->
        if w_binders then
          if simpl <> [] && tl <> [] then
            err_loc(str"binders XOR s-item allowed here: "++pr_ipats(tl@simpl))
          else if not (List.for_all (function IPatId _ -> true | _ -> false) tl)
          then err_loc (str "Only binders allowed here: " ++ pr_ipats tl)
          else ipat @ [i], tl
        else
          if tl = [] then  ipat @ [i], []
          else err_loc (str "No binder or s-item allowed here: " ++ pr_ipats tl)
      | hd :: tl -> loop (ipat @ [hd]) tl
    in loop [] ipats in
  ((clr, ipat), binders), simpl

let pr_clear_opt sep = function None -> mt () | Some x -> pr_clear sep x

let pr_hpats (((clr, ipat), binders), simpl) =
   pr_clear_opt mt clr ++ pr_ipats ipat ++ pr_ipats binders ++ pr_ipats simpl
let pr_ssrhpats _ _ _ = pr_hpats
let pr_ssrhpats_wtransp _ _ _ (_, x) = pr_hpats x



let (wit_ssrhpats, ssrhpats) = Tacentries.argument_extend ~name:"ssrhpats" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.nterm ssripats)))
                                                          (fun i loc -> 
# 949 "plugins/ssr/ssrparser.mlg"
                         check_ssrhpats loc true i 
                                                                    ))]);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.Val.Opt 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrclear))), 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssripat)))), 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssripat)))), 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssripat))));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (Genarg.OptArg 
                                                       (wit_ssrclear)), 
                                                       (wit_ssripat))), 
                                                       (wit_ssripat))), 
                                                       (wit_ssripat)));
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                      (Genarg.PairArg (
                                                      (Genarg.PairArg (
                                                      (Genarg.OptArg 
                                                      (wit_ssrclear)), 
                                                      (wit_ssripat))), 
                                                      (wit_ssripat))), 
                                                      (wit_ssripat)));
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (Genarg.OptArg 
                                                       (wit_ssrclear)), 
                                                       (wit_ssripat))), 
                                                       (wit_ssripat))), 
                                                       (wit_ssripat)));
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 948 "plugins/ssr/ssrparser.mlg"
             pr_ssrhpats 
                                                        ), (fun env sigma -> 
                                                        
# 948 "plugins/ssr/ssrparser.mlg"
             pr_ssrhpats 
                                                        ), (fun env sigma -> 
                                                        
# 948 "plugins/ssr/ssrparser.mlg"
             pr_ssrhpats 
                                                        ));
                               }
let _ = (wit_ssrhpats, ssrhpats)

let (wit_ssrhpats_wtransp, ssrhpats_wtransp) = Tacentries.argument_extend ~name:"ssrhpats_wtransp" 
                                               {
                                               Tacentries.arg_parsing = 
                                               Vernacextend.Arg_rules (
                                               [(Pcoq.Production.make
                                                 (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ssripats)))
                                                                 ((Pcoq.Symbol.token (CLexer.terminal "@"))))
                                                                 ((Pcoq.Symbol.nterm ssripats)))
                                                 (fun j _ i loc -> 
# 956 "plugins/ssr/ssrparser.mlg"
                                         true,check_ssrhpats loc true (i @ j) 
                                                                   ));
                                               (Pcoq.Production.make
                                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ssripats)))
                                                (fun i loc -> 
# 955 "plugins/ssr/ssrparser.mlg"
                         false,check_ssrhpats loc true i 
                                                              ))]);
                                               Tacentries.arg_tag = Some
                                                                    (Geninterp.Val.Pair (
                                                                    (Geninterp.val_tag (Genarg.topwit wit_bool)), 
                                                                    (Geninterp.Val.Pair (
                                                                    (Geninterp.Val.Pair (
                                                                    (Geninterp.Val.Pair (
                                                                    (Geninterp.Val.Opt 
                                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrclear))), 
                                                                    (Geninterp.val_tag (Genarg.topwit wit_ssripats)))), 
                                                                    (Geninterp.val_tag (Genarg.topwit wit_ssripats)))), 
                                                                    (Geninterp.val_tag (Genarg.topwit wit_ssripats))))));
                                               Tacentries.arg_intern = 
                                               Tacentries.ArgInternWit (Genarg.PairArg (
                                               (wit_bool), (Genarg.PairArg (
                                                           (Genarg.PairArg (
                                                           (Genarg.PairArg (
                                                           (Genarg.OptArg 
                                                           (wit_ssrclear)), 
                                                           (wit_ssripats))), 
                                                           (wit_ssripats))), 
                                                           (wit_ssripats)))));
                                               Tacentries.arg_subst = 
                                               Tacentries.ArgSubstWit (Genarg.PairArg (
                                               (wit_bool), (Genarg.PairArg (
                                                           (Genarg.PairArg (
                                                           (Genarg.PairArg (
                                                           (Genarg.OptArg 
                                                           (wit_ssrclear)), 
                                                           (wit_ssripats))), 
                                                           (wit_ssripats))), 
                                                           (wit_ssripats)))));
                                               Tacentries.arg_interp = 
                                               Tacentries.ArgInterpWit (Genarg.PairArg (
                                               (wit_bool), (Genarg.PairArg (
                                                           (Genarg.PairArg (
                                                           (Genarg.PairArg (
                                                           (Genarg.OptArg 
                                                           (wit_ssrclear)), 
                                                           (wit_ssripats))), 
                                                           (wit_ssripats))), 
                                                           (wit_ssripats)))));
                                               Tacentries.arg_printer = 
                                               ((fun env sigma -> 
# 954 "plugins/ssr/ssrparser.mlg"
               pr_ssrhpats_wtransp 
                                               ), (fun env sigma -> 
# 954 "plugins/ssr/ssrparser.mlg"
               pr_ssrhpats_wtransp 
                                               ), (fun env sigma -> 
# 954 "plugins/ssr/ssrparser.mlg"
               pr_ssrhpats_wtransp 
                                               ));
                                               }
let _ = (wit_ssrhpats_wtransp, ssrhpats_wtransp)

let (wit_ssrhpats_nobs, ssrhpats_nobs) = Tacentries.argument_extend ~name:"ssrhpats_nobs" 
                                         {
                                         Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                                  [(Pcoq.Production.make
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.nterm ssripats)))
                                                                    (fun i
                                                                    loc -> 
                                                                    
# 961 "plugins/ssr/ssrparser.mlg"
                         check_ssrhpats loc false i 
                                                                    ))]);
                                         Tacentries.arg_tag = Some
                                                              (Geninterp.Val.Pair (
                                                              (Geninterp.Val.Pair (
                                                              (Geninterp.Val.Pair (
                                                              (Geninterp.Val.Opt 
                                                              (Geninterp.val_tag (Genarg.topwit wit_ssrclear))), 
                                                              (Geninterp.val_tag (Genarg.topwit wit_ssripats)))), 
                                                              (Geninterp.val_tag (Genarg.topwit wit_ssripats)))), 
                                                              (Geninterp.val_tag (Genarg.topwit wit_ssripats))));
                                         Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                                 (Genarg.PairArg (
                                                                 (Genarg.PairArg (
                                                                 (Genarg.OptArg 
                                                                 (wit_ssrclear)), 
                                                                 (wit_ssripats))), 
                                                                 (wit_ssripats))), 
                                                                 (wit_ssripats)));
                                         Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                                (Genarg.PairArg (
                                                                (Genarg.PairArg (
                                                                (Genarg.OptArg 
                                                                (wit_ssrclear)), 
                                                                (wit_ssripats))), 
                                                                (wit_ssripats))), 
                                                                (wit_ssripats)));
                                         Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                                 (Genarg.PairArg (
                                                                 (Genarg.PairArg (
                                                                 (Genarg.OptArg 
                                                                 (wit_ssrclear)), 
                                                                 (wit_ssripats))), 
                                                                 (wit_ssripats))), 
                                                                 (wit_ssripats)));
                                         Tacentries.arg_printer = ((fun env sigma -> 
                                                                  
# 960 "plugins/ssr/ssrparser.mlg"
                                                                             pr_ssrhpats 
                                                                  ), (fun env sigma -> 
                                                                  
# 960 "plugins/ssr/ssrparser.mlg"
                                                                             pr_ssrhpats 
                                                                  ), (fun env sigma -> 
                                                                  
# 960 "plugins/ssr/ssrparser.mlg"
                                                                             pr_ssrhpats 
                                                                  ));
                                         }
let _ = (wit_ssrhpats_nobs, ssrhpats_nobs)

let (wit_ssrrpat, ssrrpat) = Tacentries.argument_extend ~name:"ssrrpat" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.token (CLexer.terminal "<-"))))
                                                        (fun _ loc -> 
# 966 "plugins/ssr/ssrparser.mlg"
                  IPatRewrite (allocc, R2L) 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "->"))))
                                                       (fun _ loc -> 
# 965 "plugins/ssr/ssrparser.mlg"
                  IPatRewrite (allocc, L2R) 
                                                                    ))]);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssripatrep));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssripatrep);
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssripatrep);
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssripatrep);
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 964 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssripat 
                                                      ), (fun env sigma -> 
                                                      
# 964 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssripat 
                                                      ), (fun env sigma -> 
                                                      
# 964 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssripat 
                                                      ));
                             }
let _ = (wit_ssrrpat, ssrrpat)


# 969 "plugins/ssr/ssrparser.mlg"
 

let pr_intros sep intrs =
  if intrs = [] then mt() else sep () ++ str "=>" ++ sep () ++ pr_ipats intrs
let pr_ssrintros _ _ _ = pr_intros mt



let (wit_ssrintros_ne, ssrintros_ne) = Tacentries.argument_extend ~name:"ssrintros_ne" 
                                       {
                                       Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                                [(Pcoq.Production.make
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (CLexer.terminal "=>"))))
                                                                  ((Pcoq.Symbol.nterm ssripats_ne)))
                                                                  (fun pats _
                                                                  loc -> 
                                                                  
# 979 "plugins/ssr/ssrparser.mlg"
                                    pats 
                                                                  ))]);
                                       Tacentries.arg_tag = Some
                                                            (Geninterp.val_tag (Genarg.topwit wit_ssripat));
                                       Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssripat);
                                       Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssripat);
                                       Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssripat);
                                       Tacentries.arg_printer = ((fun env sigma -> 
                                                                
# 978 "plugins/ssr/ssrparser.mlg"
              pr_ssrintros 
                                                                ), (fun env sigma -> 
                                                                
# 978 "plugins/ssr/ssrparser.mlg"
              pr_ssrintros 
                                                                ), (fun env sigma -> 
                                                                
# 978 "plugins/ssr/ssrparser.mlg"
              pr_ssrintros 
                                                                ));
                                       }
let _ = (wit_ssrintros_ne, ssrintros_ne)

let (wit_ssrintros, ssrintros) = Tacentries.argument_extend ~name:"ssrintros" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.stop)
                                                            (fun loc -> 
# 986 "plugins/ssr/ssrparser.mlg"
             [] 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssrintros_ne)))
                                                           (fun intrs loc ->
                                                           
# 985 "plugins/ssr/ssrparser.mlg"
                                 intrs 
                                                           ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrintros_ne));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrintros_ne);
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrintros_ne);
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrintros_ne);
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 984 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssrintros 
                                                          ), (fun env sigma -> 
                                                          
# 984 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssrintros 
                                                          ), (fun env sigma -> 
                                                          
# 984 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssrintros 
                                                          ));
                                 }
let _ = (wit_ssrintros, ssrintros)


# 989 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrintrosarg env sigma _ _ prt (tac, ipats) =
  prt env sigma tacltop tac ++ pr_intros spc ipats



let (wit_ssrintrosarg, ssrintrosarg) = Tacentries.argument_extend ~name:"ssrintrosarg" 
                                       {
                                       Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                                []);
                                       Tacentries.arg_tag = Some
                                                            (Geninterp.Val.Pair (
                                                            (Geninterp.val_tag (Genarg.topwit wit_tactic)), 
                                                            (Geninterp.val_tag (Genarg.topwit wit_ssrintros))));
                                       Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                               (wit_tactic), 
                                                               (wit_ssrintros)));
                                       Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                              (wit_tactic), 
                                                              (wit_ssrintros)));
                                       Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                               (wit_tactic), 
                                                               (wit_ssrintros)));
                                       Tacentries.arg_printer = ((fun env sigma -> 
                                                                
# 997 "plugins/ssr/ssrparser.mlg"
                pr_ssrintrosarg env sigma 
                                                                ), (fun env sigma -> 
                                                                
# 997 "plugins/ssr/ssrparser.mlg"
                pr_ssrintrosarg env sigma 
                                                                ), (fun env sigma -> 
                                                                
# 997 "plugins/ssr/ssrparser.mlg"
                pr_ssrintrosarg env sigma 
                                                                ));
                                       }
let _ = (wit_ssrintrosarg, ssrintrosarg)


# 1000 "plugins/ssr/ssrparser.mlg"
 

(** Defined identifier *)
let pr_ssrfwdid id = pr_spc () ++ pr_id id

let pr_ssrfwdidx _ _ _ = pr_ssrfwdid



let (wit_ssrfwdid, ssrfwdid) = Tacentries.argument_extend ~name:"ssrfwdid" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        []);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.val_tag (Genarg.topwit wit_ident));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ident);
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ident);
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ident);
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 1011 "plugins/ssr/ssrparser.mlg"
                                                     pr_ssrfwdidx 
                                                        ), (fun env sigma -> 
                                                        
# 1011 "plugins/ssr/ssrparser.mlg"
                                                     pr_ssrfwdidx 
                                                        ), (fun env sigma -> 
                                                        
# 1011 "plugins/ssr/ssrparser.mlg"
                                                     pr_ssrfwdidx 
                                                        ));
                               }
let _ = (wit_ssrfwdid, ssrfwdid)


# 1014 "plugins/ssr/ssrparser.mlg"
 

let test_ssrfwdid =
  let open Pcoq.Lookahead in
  to_entry "test_ssrfwdid" begin
    lk_ident >> (lk_ident <+> lk_kws [":"; ":="; "("])
  end



let _ = let () =
        Pcoq.grammar_extend ssrfwdid
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm test_ssrfwdid)))
                                            ((Pcoq.Symbol.nterm Prim.ident)))
                            (fun id _ loc -> 
# 1026 "plugins/ssr/ssrparser.mlg"
                                                       id 
                                             )]))
        in ()


# 1037 "plugins/ssr/ssrparser.mlg"
 

let pr_ortacs env sigma prt =
  let rec pr_rec = function
  | [None]           -> spc() ++ str "|" ++ spc()
  | None :: tacs     -> spc() ++ str "|" ++ pr_rec tacs
  | Some tac :: tacs -> spc() ++ str "| " ++ prt env sigma tacltop tac ++  pr_rec tacs
  | []                -> mt() in
  function
  | [None]           -> spc()
  | None :: tacs     -> pr_rec tacs
  | Some tac :: tacs -> prt env sigma tacltop tac ++ pr_rec tacs
  | []                -> mt()
let pr_ssrortacs env sigma _ _ = pr_ortacs env sigma



let (wit_ssrortacs, ssrortacs) = Tacentries.argument_extend ~name:"ssrortacs" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (CLexer.terminal "|"))))
                                                            (fun _ loc -> 
# 1059 "plugins/ssr/ssrparser.mlg"
               [None; None] 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "|"))))
                                                           (Pcoq.Symbol.self))
                                                           (fun tacs _ loc ->
                                                           
# 1058 "plugins/ssr/ssrparser.mlg"
                               None :: tacs 
                                                           ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssrtacarg)))
                                                           (fun tac loc -> 
# 1057 "plugins/ssr/ssrparser.mlg"
                          [Some tac] 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssrtacarg)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "|"))))
                                                           (fun _ tac loc ->
                                                           
# 1056 "plugins/ssr/ssrparser.mlg"
                              [Some tac; None] 
                                                           ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssrtacarg)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "|"))))
                                                           (Pcoq.Symbol.self))
                                                           (fun tacs _ tac
                                                           loc -> 
# 1055 "plugins/ssr/ssrparser.mlg"
                                              Some tac :: tacs 
                                                                  ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.Val.List 
                                                      (Geninterp.Val.Opt 
                                                      (Geninterp.val_tag (Genarg.topwit wit_tactic))));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                         (Genarg.OptArg 
                                                         (wit_tactic)));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                        (Genarg.OptArg 
                                                        (wit_tactic)));
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                         (Genarg.OptArg 
                                                         (wit_tactic)));
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 1054 "plugins/ssr/ssrparser.mlg"
                                                                   pr_ssrortacs env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 1054 "plugins/ssr/ssrparser.mlg"
                                                                   pr_ssrortacs env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 1054 "plugins/ssr/ssrparser.mlg"
                                                                   pr_ssrortacs env sigma 
                                                          ));
                                 }
let _ = (wit_ssrortacs, ssrortacs)


# 1062 "plugins/ssr/ssrparser.mlg"
 

let pr_hintarg env sigma prt = function
  | true, tacs -> hv 0 (str "[ " ++ pr_ortacs env sigma prt tacs ++ str " ]")
  | false, [Some tac] -> prt env sigma tacltop tac
  | _, _ -> mt()

let pr_ssrhintarg env sigma _ _ = pr_hintarg env sigma



let (wit_ssrhintarg, ssrhintarg) = Tacentries.argument_extend ~name:"ssrhintarg" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm ssrtacarg)))
                                                              (fun arg loc ->
                                                              
# 1076 "plugins/ssr/ssrparser.mlg"
                          mk_hint arg 
                                                              ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                             ((Pcoq.Symbol.nterm ssrortacs)))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                             (fun _ tacs _
                                                             loc -> 
# 1075 "plugins/ssr/ssrparser.mlg"
                                   mk_orhint tacs 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                             (fun _ _ loc ->
                                                             
# 1074 "plugins/ssr/ssrparser.mlg"
                   nullhint 
                                                             ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.Pair (
                                                        (Geninterp.val_tag (Genarg.topwit wit_bool)), 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrortacs))));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                           (wit_bool), 
                                                           (wit_ssrortacs)));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                          (wit_bool), 
                                                          (wit_ssrortacs)));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                           (wit_bool), 
                                                           (wit_ssrortacs)));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 1073 "plugins/ssr/ssrparser.mlg"
                                                                    pr_ssrhintarg env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 1073 "plugins/ssr/ssrparser.mlg"
                                                                    pr_ssrhintarg env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 1073 "plugins/ssr/ssrparser.mlg"
                                                                    pr_ssrhintarg env sigma 
                                                            ));
                                   }
let _ = (wit_ssrhintarg, ssrhintarg)

let (wit_ssrhint3arg, ssrhint3arg) = Tacentries.argument_extend ~name:"ssrhint3arg" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ssrtac3arg)))
                                                                (fun arg
                                                                loc -> 
                                                                
# 1083 "plugins/ssr/ssrparser.mlg"
                           mk_hint arg 
                                                                ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                               ((Pcoq.Symbol.nterm ssrortacs)))
                                                               ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                               (fun _ tacs _
                                                               loc -> 
                                                               
# 1082 "plugins/ssr/ssrparser.mlg"
                                   mk_orhint tacs 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                               ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                               (fun _ _
                                                               loc -> 
                                                               
# 1081 "plugins/ssr/ssrparser.mlg"
                   nullhint 
                                                               ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.Val.Pair (
                                                          (Geninterp.val_tag (Genarg.topwit wit_bool)), 
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrortacs))));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                             (wit_bool), 
                                                             (wit_ssrortacs)));
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                            (wit_bool), 
                                                            (wit_ssrortacs)));
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                             (wit_bool), 
                                                             (wit_ssrortacs)));
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 1080 "plugins/ssr/ssrparser.mlg"
                                                                     pr_ssrhintarg env sigma 
                                                              ), (fun env sigma -> 
                                                              
# 1080 "plugins/ssr/ssrparser.mlg"
                                                                     pr_ssrhintarg env sigma 
                                                              ), (fun env sigma -> 
                                                              
# 1080 "plugins/ssr/ssrparser.mlg"
                                                                     pr_ssrhintarg env sigma 
                                                              ));
                                     }
let _ = (wit_ssrhint3arg, ssrhint3arg)

let (wit_ssrortacarg, ssrortacarg) = Tacentries.argument_extend ~name:"ssrortacarg" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                                ((Pcoq.Symbol.nterm ssrortacs)))
                                                                ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                                (fun _ tacs _
                                                                loc -> 
                                                                
# 1087 "plugins/ssr/ssrparser.mlg"
                                   mk_orhint tacs 
                                                                ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrhintarg));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrhintarg);
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrhintarg);
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrhintarg);
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 1086 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssrhintarg env sigma 
                                                              ), (fun env sigma -> 
                                                              
# 1086 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssrhintarg env sigma 
                                                              ), (fun env sigma -> 
                                                              
# 1086 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssrhintarg env sigma 
                                                              ));
                                     }
let _ = (wit_ssrortacarg, ssrortacarg)


# 1090 "plugins/ssr/ssrparser.mlg"
 

let pr_hint env sigma prt arg =
  if arg = nohint then mt() else str "by " ++ pr_hintarg env sigma prt arg
let pr_ssrhint env sigma _ _ = pr_hint env sigma



let (wit_ssrhint, ssrhint) = Tacentries.argument_extend ~name:"ssrhint" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.stop)
                                                        (fun loc -> 
# 1099 "plugins/ssr/ssrparser.mlg"
                                 nohint 
                                                                    ))]);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssrhintarg));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrhintarg);
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrhintarg);
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrhintarg);
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 1098 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssrhint env sigma 
                                                      ), (fun env sigma -> 
                                                      
# 1098 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssrhint env sigma 
                                                      ), (fun env sigma -> 
                                                      
# 1098 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssrhint env sigma 
                                                      ));
                             }
let _ = (wit_ssrhint, ssrhint)


# 1114 "plugins/ssr/ssrparser.mlg"
 

open Ssrmatching_plugin.Ssrmatching
open Ssrmatching_plugin.G_ssrmatching

let pr_wgen = function
  | (clr, Some((id,k),None)) -> spc() ++ pr_clear mt clr ++ str k ++ pr_hoi id
  | (clr, Some((id,k),Some p)) ->
      spc() ++ pr_clear mt clr ++ str"(" ++ str k ++ pr_hoi id ++ str ":=" ++
        pr_cpattern p ++ str ")"
  | (clr, None) -> spc () ++ pr_clear mt clr
let pr_ssrwgen _ _ _ = pr_wgen



let (wit_ssrwgen, ssrwgen) = Tacentries.argument_extend ~name:"ssrwgen" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                        ((Pcoq.Symbol.token (CLexer.terminal "@"))))
                                                        ((Pcoq.Symbol.nterm ssrhoi_id)))
                                                        ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                        ((Pcoq.Symbol.nterm lcpattern)))
                                                        ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                        (fun _ p _ id _ _
                                                        loc -> 
# 1142 "plugins/ssr/ssrparser.mlg"
    [], Some ((id,"@"),Some p) 
                                                               ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "(@"))))
                                                       ((Pcoq.Symbol.nterm ssrhoi_id)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                       ((Pcoq.Symbol.nterm lcpattern)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                       (fun _ p _ id _ loc ->
                                                       
# 1140 "plugins/ssr/ssrparser.mlg"
    [], Some ((id,"@"),Some p) 
                                                       ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                       ((Pcoq.Symbol.nterm ssrhoi_id)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                       (fun _ id _ loc -> 
# 1138 "plugins/ssr/ssrparser.mlg"
                                 [], Some ((id,"("), None) 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                       ((Pcoq.Symbol.nterm ssrhoi_id)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                       ((Pcoq.Symbol.nterm lcpattern)))
                                                       ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                       (fun _ p _ id _ loc ->
                                                       
# 1137 "plugins/ssr/ssrparser.mlg"
    [], Some ((id," "),Some p) 
                                                       ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "@"))))
                                                       ((Pcoq.Symbol.nterm ssrhoi_hyp)))
                                                       (fun hyp _ loc -> 
# 1135 "plugins/ssr/ssrparser.mlg"
                               [], Some((hyp, "@"), None) 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ssrhoi_hyp)))
                                                       (fun hyp loc -> 
# 1134 "plugins/ssr/ssrparser.mlg"
                           [], Some((hyp, " "), None) 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ssrclear_ne)))
                                                       (fun clr loc -> 
# 1133 "plugins/ssr/ssrparser.mlg"
                            clr, None 
                                                                    ))]);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.Val.Pair (
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssrclear)), 
                                                  (Geninterp.Val.Opt 
                                                  (Geninterp.Val.Pair (
                                                  (Geninterp.Val.Pair (
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssrhoi_hyp)), 
                                                  (Geninterp.val_tag (Genarg.topwit wit_string)))), 
                                                  (Geninterp.Val.Opt 
                                                  (Geninterp.val_tag (Genarg.topwit wit_cpattern))))))));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                     (wit_ssrclear), 
                                                     (Genarg.OptArg (Genarg.PairArg (
                                                                    (Genarg.PairArg (
                                                                    (wit_ssrhoi_hyp), 
                                                                    (wit_string))), 
                                                                    (Genarg.OptArg 
                                                                    (wit_cpattern)))))));
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                    (wit_ssrclear), (Genarg.OptArg 
                                                                    (Genarg.PairArg (
                                                                    (Genarg.PairArg (
                                                                    (wit_ssrhoi_hyp), 
                                                                    (wit_string))), 
                                                                    (Genarg.OptArg 
                                                                    (wit_cpattern)))))));
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                     (wit_ssrclear), 
                                                     (Genarg.OptArg (Genarg.PairArg (
                                                                    (Genarg.PairArg (
                                                                    (wit_ssrhoi_hyp), 
                                                                    (wit_string))), 
                                                                    (Genarg.OptArg 
                                                                    (wit_cpattern)))))));
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 1132 "plugins/ssr/ssrparser.mlg"
               pr_ssrwgen 
                                                      ), (fun env sigma -> 
                                                      
# 1132 "plugins/ssr/ssrparser.mlg"
               pr_ssrwgen 
                                                      ), (fun env sigma -> 
                                                      
# 1132 "plugins/ssr/ssrparser.mlg"
               pr_ssrwgen 
                                                      ));
                             }
let _ = (wit_ssrwgen, ssrwgen)


# 1145 "plugins/ssr/ssrparser.mlg"
 

let pr_clseq = function
  | InGoal | InHyps -> mt ()
  | InSeqGoal       -> str "|- *"
  | InHypsSeqGoal   -> str " |- *"
  | InHypsGoal      -> str " *"
  | InAll           -> str "*"
  | InHypsSeq       -> str " |-"
  | InAllHyps       -> str "* |-"

let wit_ssrclseq = add_genarg "ssrclseq" (fun env sigma -> pr_clseq)
let pr_clausehyps = pr_list pr_spc pr_wgen
let pr_ssrclausehyps _ _ _ = pr_clausehyps



let (wit_ssrclausehyps, ssrclausehyps) = Tacentries.argument_extend ~name:"ssrclausehyps" 
                                         {
                                         Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                                  [(Pcoq.Production.make
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.nterm ssrwgen)))
                                                                    (fun hyp
                                                                    loc -> 
                                                                    
# 1166 "plugins/ssr/ssrparser.mlg"
                        [hyp] 
                                                                    ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.nterm ssrwgen)))
                                                                   (Pcoq.Symbol.self))
                                                                   (fun hyps
                                                                   hyp loc ->
                                                                   
# 1165 "plugins/ssr/ssrparser.mlg"
                                            hyp :: hyps 
                                                                   ));
                                                                  (Pcoq.Production.make
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.nterm ssrwgen)))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal ","))))
                                                                   (Pcoq.Symbol.self))
                                                                   (fun hyps
                                                                   _ hyp
                                                                   loc -> 
                                                                   
# 1164 "plugins/ssr/ssrparser.mlg"
                                                hyp :: hyps 
                                                                   ))]);
                                         Tacentries.arg_tag = Some
                                                              (Geninterp.Val.List 
                                                              (Geninterp.val_tag (Genarg.topwit wit_ssrwgen)));
                                         Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                                 (wit_ssrwgen));
                                         Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                                (wit_ssrwgen));
                                         Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                                 (wit_ssrwgen));
                                         Tacentries.arg_printer = ((fun env sigma -> 
                                                                  
# 1163 "plugins/ssr/ssrparser.mlg"
                                   pr_ssrclausehyps 
                                                                  ), (fun env sigma -> 
                                                                  
# 1163 "plugins/ssr/ssrparser.mlg"
                                   pr_ssrclausehyps 
                                                                  ), (fun env sigma -> 
                                                                  
# 1163 "plugins/ssr/ssrparser.mlg"
                                   pr_ssrclausehyps 
                                                                  ));
                                         }
let _ = (wit_ssrclausehyps, ssrclausehyps)


# 1169 "plugins/ssr/ssrparser.mlg"
 

(* type ssrclauses = ssrahyps * ssrclseq *)

let pr_clauses (hyps, clseq) =
  if clseq = InGoal then mt ()
  else str "in " ++ pr_clausehyps hyps ++ pr_clseq clseq
let pr_ssrclauses _ _ _ = pr_clauses



let (wit_ssrclauses, ssrclauses) = Tacentries.argument_extend ~name:"ssrclauses" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.stop)
                                                              (fun loc -> 
# 1189 "plugins/ssr/ssrparser.mlg"
                                               [], InGoal 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "*"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "|-"))))
                                                             (fun _ _ _
                                                             loc -> 
# 1188 "plugins/ssr/ssrparser.mlg"
                                               [], InAllHyps 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "*"))))
                                                             (fun _ _ loc ->
                                                             
# 1187 "plugins/ssr/ssrparser.mlg"
                                               [], InAll 
                                                             ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "|-"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "*"))))
                                                             (fun _ _ _
                                                             loc -> 
# 1186 "plugins/ssr/ssrparser.mlg"
                                               [], InSeqGoal 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                             ((Pcoq.Symbol.nterm ssrclausehyps)))
                                                             (fun hyps _
                                                             loc -> 
# 1185 "plugins/ssr/ssrparser.mlg"
                                               hyps, InHyps 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                             ((Pcoq.Symbol.nterm ssrclausehyps)))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "*"))))
                                                             (fun _ hyps _
                                                             loc -> 
# 1184 "plugins/ssr/ssrparser.mlg"
                                               hyps, InHypsGoal 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                             ((Pcoq.Symbol.nterm ssrclausehyps)))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "|-"))))
                                                             (fun _ hyps _
                                                             loc -> 
# 1183 "plugins/ssr/ssrparser.mlg"
                                               hyps, InHypsSeq 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                             ((Pcoq.Symbol.nterm ssrclausehyps)))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "|-"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "*"))))
                                                             (fun _ _ hyps _
                                                             loc -> 
# 1182 "plugins/ssr/ssrparser.mlg"
                                               hyps, InHypsSeqGoal 
                                                                    ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.Pair (
                                                        (Geninterp.Val.List 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrwgen))), 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrclseq))));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                           (Genarg.ListArg 
                                                           (wit_ssrwgen)), 
                                                           (wit_ssrclseq)));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                          (Genarg.ListArg 
                                                          (wit_ssrwgen)), 
                                                          (wit_ssrclseq)));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                           (Genarg.ListArg 
                                                           (wit_ssrwgen)), 
                                                           (wit_ssrclseq)));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 1181 "plugins/ssr/ssrparser.mlg"
                 pr_ssrclauses 
                                                            ), (fun env sigma -> 
                                                            
# 1181 "plugins/ssr/ssrparser.mlg"
                 pr_ssrclauses 
                                                            ), (fun env sigma -> 
                                                            
# 1181 "plugins/ssr/ssrparser.mlg"
                 pr_ssrclauses 
                                                            ));
                                   }
let _ = (wit_ssrclauses, ssrclauses)


# 1193 "plugins/ssr/ssrparser.mlg"
 

(** Definition value formatting *)

(* We use an intermediate structure to correctly render the binder list  *)
(* abbreviations. We use a list of hints to extract the binders and      *)
(* base term from a term, for the two first levels of representation of  *)
(* of constr terms.                                                      *)

let pr_binder prl = function
  | Bvar x ->
    pr_name x
  | Bdecl (xs, t) ->
    str "(" ++ pr_list pr_spc pr_name xs ++ str " : " ++ prl t ++ str ")"
  | Bdef (x, None, v) ->
    str "(" ++ pr_name x ++ str " := " ++ prl v ++ str ")"
  | Bdef (x, Some t, v) ->
    str "(" ++ pr_name x ++ str " : " ++ prl t ++
                            str " := " ++ prl v ++ str ")"
  | Bstruct x ->
    str "{struct " ++ pr_name x ++ str "}"
  | Bcast t ->
    str ": " ++ prl t

let rec format_local_binders h0 bl0 = match h0, bl0 with
  | BFvar :: h, CLocalAssum ([{CAst.v=x}], _,  _) :: bl ->
    Bvar x :: format_local_binders h bl
  | BFdecl _ :: h, CLocalAssum (lxs, _, t) :: bl ->
    Bdecl (List.map (fun x -> x.CAst.v) lxs, t) :: format_local_binders h bl
  | BFdef :: h, CLocalDef ({CAst.v=x}, v, oty) :: bl ->
    Bdef (x, oty, v) :: format_local_binders h bl
  | _ -> []

let rec format_constr_expr h0 c0 = let open CAst in match h0, c0 with
  | BFvar :: h, { v = CLambdaN ([CLocalAssum([{CAst.v=x}], _, _)], c) } ->
    let bs, c' = format_constr_expr h c in
    Bvar x :: bs, c'
  | BFdecl _:: h, { v = CLambdaN ([CLocalAssum(lxs, _, t)], c) } ->
    let bs, c' = format_constr_expr h c in
    Bdecl (List.map (fun x -> x.CAst.v) lxs, t) :: bs, c'
  | BFdef :: h, { v = CLetIn({CAst.v=x}, v, oty, c) } ->
    let bs, c' = format_constr_expr h c in
    Bdef (x, oty, v) :: bs, c'
  | [BFcast], { v = CCast (c, defaultCast, t) } ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h,
    { v = CFix ( _, [_, Some {CAst.v = CStructRec locn}, bl, t, c]) } ->
    let bs = format_local_binders h bl in
    let bstr = if has_str then [Bstruct (Name locn.CAst.v)] else [] in
    bs @ bstr @ (if has_cast then [Bcast t] else []), c
  | BFrec (_, has_cast) :: h, { v = CCoFix ( _, [_, bl, t, c]) } ->
    format_local_binders h bl @ (if has_cast then [Bcast t] else []), c
  | _, c ->
    [], c

(** Forward chaining argument *)

(* There are three kinds of forward definitions:           *)
(*   - Hint: type only, cast to Type, may have proof hint. *)
(*   - Have: type option + value, no space before type     *)
(*   - Pose: binders + value, space before binders.        *)

let pr_fwdkind = function
  | FwdHint (s,_) -> str (s ^ " ") | _ -> str " :=" ++ spc ()
let pr_fwdfmt (fk, _ : ssrfwdfmt) = pr_fwdkind fk

let wit_ssrfwdfmt = add_genarg "ssrfwdfmt" (fun env sigma -> pr_fwdfmt)

(* type ssrfwd = ssrfwdfmt * ssrterm *)

let mkFwdVal fk c = ((fk, []), c)
let mkssrFwdVal fk c = ((fk, []), (c,None))

let same_ist { interp_env = x } { interp_env = y } =
  match x,y with
  | None, None -> true
  | Some a, Some b -> a == b
  | _ -> false

let mkFwdCast fk ?loc ?c t =
  let c = match c with
    | None -> mkCHole loc
    | Some c -> assert (same_ist t c); c.body in
  ((fk, [BFcast]),
   { t with annotation = `None;
            body = (CAst.make ?loc @@ CCast (c, defaultCast, t.body)) })

let mkssrFwdCast fk loc t c = ((fk, [BFcast]), (c, Some t))

let mkFwdHint s t =
  let loc =  Constrexpr_ops.constr_loc t.body in
  mkFwdCast (FwdHint (s,false)) ?loc t
let mkFwdHintNoTC s t =
  let loc =  Constrexpr_ops.constr_loc t.body in
  mkFwdCast (FwdHint (s,true)) ?loc t

let pr_gen_fwd prval prc prlc fk (bs, c) =
  let prc s = str s ++ spc () ++ prval prc prlc c in
  match fk, bs with
  | FwdHint (s,_), [Bcast t] -> str s ++ spc () ++ prlc t
  | FwdHint (s,_), _ ->  prc (s ^ "(* typeof *)")
  | FwdHave, [Bcast t] -> str ":" ++ spc () ++ prlc t ++ prc " :="
  | _, [] -> prc " :="
  | _, _ -> spc () ++ pr_list spc (pr_binder prlc) bs ++ prc " :="

let pr_fwd_guarded prval prval' = function
| (fk, h), c ->
  pr_gen_fwd prval pr_constr_expr prl_constr_expr fk (format_constr_expr h c.body)

let pr_unguarded prc prlc = prlc

let pr_fwd = pr_fwd_guarded pr_unguarded pr_unguarded
let pr_ssrfwd _ _ _ = pr_fwd



let (wit_ssrfwd, ssrfwd) = Tacentries.argument_extend ~name:"ssrfwd" 
                           {
                           Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                    [(Pcoq.Production.make
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.stop)
                                                      ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                      ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                      ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                      ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                      (fun c _ t _ loc -> 
# 1311 "plugins/ssr/ssrparser.mlg"
                                                                 mkFwdCast FwdPose ~loc t ~c 
                                                                    ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                     ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                     (fun c _ loc -> 
# 1310 "plugins/ssr/ssrparser.mlg"
                                       mkFwdVal FwdPose c 
                                                                    ))]);
                           Tacentries.arg_tag = Some
                                                (Geninterp.Val.Pair (
                                                (Geninterp.val_tag (Genarg.topwit wit_ssrfwdfmt)), 
                                                (Geninterp.val_tag (Genarg.topwit wit_ast_closure_lterm))));
                           Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                   (wit_ssrfwdfmt), (wit_ast_closure_lterm)));
                           Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                  (wit_ssrfwdfmt), (wit_ast_closure_lterm)));
                           Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                   (wit_ssrfwdfmt), (wit_ast_closure_lterm)));
                           Tacentries.arg_printer = ((fun env sigma -> 
                                                    
# 1309 "plugins/ssr/ssrparser.mlg"
                                                                             pr_ssrfwd 
                                                    ), (fun env sigma -> 
                                                    
# 1309 "plugins/ssr/ssrparser.mlg"
                                                                             pr_ssrfwd 
                                                    ), (fun env sigma -> 
                                                    
# 1309 "plugins/ssr/ssrparser.mlg"
                                                                             pr_ssrfwd 
                                                    ));
                           }
let _ = (wit_ssrfwd, ssrfwd)


# 1319 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrbvar env sigma prc _ _ v = prc env sigma v



let (wit_ssrbvar, ssrbvar) = Tacentries.argument_extend ~name:"ssrbvar" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.token (CLexer.terminal "_"))))
                                                        (fun _ loc -> 
# 1327 "plugins/ssr/ssrparser.mlg"
               mkCHole (Some loc) 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ident)))
                                                       (fun id loc -> 
# 1326 "plugins/ssr/ssrparser.mlg"
                     mkCVar ~loc id 
                                                                    ))]);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.val_tag (Genarg.topwit wit_constr));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (wit_constr);
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_constr);
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_constr);
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 1325 "plugins/ssr/ssrparser.mlg"
                                                     pr_ssrbvar env sigma 
                                                      ), (fun env sigma -> 
                                                      
# 1325 "plugins/ssr/ssrparser.mlg"
                                                     pr_ssrbvar env sigma 
                                                      ), (fun env sigma -> 
                                                      
# 1325 "plugins/ssr/ssrparser.mlg"
                                                     pr_ssrbvar env sigma 
                                                      ));
                             }
let _ = (wit_ssrbvar, ssrbvar)


# 1330 "plugins/ssr/ssrparser.mlg"
 

let bvar_lname = let open CAst in function
  | { v = CRef (qid, _) } when qualid_is_ident qid ->
    CAst.make ?loc:qid.CAst.loc @@ Name (qualid_basename qid)
  | { loc = loc } -> CAst.make ?loc Anonymous

let pr_ssrbinder env sigma prc _ _ (_, c) = prc env sigma c



let (wit_ssrbinder, ssrbinder) = Tacentries.argument_extend ~name:"ssrbinder" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                            ((Pcoq.Symbol.nterm ssrbvar)))
                                                            ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                            ((Pcoq.Symbol.nterm lconstr)))
                                                            ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                            (fun _ v _ id _
                                                            loc -> 
# 1362 "plugins/ssr/ssrparser.mlg"
     (FwdPose,[BFdef]), CAst.make ~loc @@ CLetIn (bvar_lname id, v, None, mkCHole (Some loc)) 
                                                                   ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                           ((Pcoq.Symbol.nterm ssrbvar)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                           ((Pcoq.Symbol.nterm lconstr)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                           ((Pcoq.Symbol.nterm lconstr)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                           (fun _ v _ t _ id
                                                           _ loc -> 
# 1360 "plugins/ssr/ssrparser.mlg"
     (FwdPose,[BFdef]), CAst.make ~loc @@ CLetIn (bvar_lname id, v, Some t, mkCHole (Some loc)) 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                           ((Pcoq.Symbol.nterm ssrbvar)))
                                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrbvar)))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                           ((Pcoq.Symbol.nterm lconstr)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                           (fun _ t _ bvs bv
                                                           _ loc -> 
# 1355 "plugins/ssr/ssrparser.mlg"
     let xs = List.map bvar_lname (bv :: bvs) in
     let n = List.length xs in
     (FwdPose, [BFdecl n]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum (xs, Default Glob_term.Explicit, t)], mkCHole (Some loc)) 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                           ((Pcoq.Symbol.nterm ssrbvar)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                           ((Pcoq.Symbol.nterm lconstr)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                           (fun _ t _ bv _
                                                           loc -> 
# 1351 "plugins/ssr/ssrparser.mlg"
     let x = bvar_lname bv in
     (FwdPose, [BFdecl 1]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum([x], Default Glob_term.Explicit, t)], mkCHole (Some loc)) 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                           ((Pcoq.Symbol.nterm ssrbvar)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                           (fun _ bv _ loc ->
                                                           
# 1347 "plugins/ssr/ssrparser.mlg"
     let { CAst.loc=xloc } as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum([x],Default Glob_term.Explicit,mkCHole xloc)],mkCHole (Some loc)) 
                                                           ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssrbvar)))
                                                           (fun bv loc -> 
# 1343 "plugins/ssr/ssrparser.mlg"
     let { CAst.loc=xloc } as x = bvar_lname bv in
     (FwdPose, [BFvar]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum([x],Default Glob_term.Explicit,mkCHole xloc)],mkCHole (Some loc)) 
                                                                    ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.Val.Pair (
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrfwdfmt)), 
                                                      (Geninterp.val_tag (Genarg.topwit wit_constr))));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                         (wit_ssrfwdfmt), 
                                                         (wit_constr)));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                        (wit_ssrfwdfmt), 
                                                        (wit_constr)));
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                         (wit_ssrfwdfmt), 
                                                         (wit_constr)));
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 1341 "plugins/ssr/ssrparser.mlg"
                                                                     pr_ssrbinder env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 1341 "plugins/ssr/ssrparser.mlg"
                                                                     pr_ssrbinder env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 1341 "plugins/ssr/ssrparser.mlg"
                                                                     pr_ssrbinder env sigma 
                                                          ));
                                 }
let _ = (wit_ssrbinder, ssrbinder)

let _ = let () =
        Pcoq.grammar_extend ssrbinder
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.rules 
                                                            [Pcoq.Rules.make 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("&")))))
                                                            (fun _ loc -> 
                                                            
# 1368 "plugins/ssr/ssrparser.mlg"
                                () 
                                                            );
                                                            Pcoq.Rules.make 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("of")))))
                                                            (fun _ loc -> 
                                                            
# 1368 "plugins/ssr/ssrparser.mlg"
                () 
                                                            )])))
                                            ((Pcoq.Symbol.nterml term ("99"))))
                            (fun c _ loc -> 
# 1368 "plugins/ssr/ssrparser.mlg"
                                                                
     (FwdPose, [BFvar]),
     CAst.make ~loc @@ CLambdaN ([CLocalAssum ([CAst.make ~loc Anonymous],Default Glob_term.Explicit,c)],mkCHole (Some loc)) 
                                            )]))
        in ()


# 1374 "plugins/ssr/ssrparser.mlg"
 

let rec binders_fmts = function
  | ((_, h), _) :: bs -> h @ binders_fmts bs
  | _ -> []

let push_binders c2 bs =
  let loc2 = constr_loc c2 in let mkloc loc1 = Loc.merge_opt loc1 loc2 in
  let open CAst in
  let rec loop ty c = function
  | (_, { loc = loc1; v = CLambdaN (b, _) } ) :: bs when ty ->
      CAst.make ?loc:(mkloc loc1) @@ CProdN (b, loop ty c bs)
  | (_, { loc = loc1; v = CLambdaN (b, _) } ) :: bs ->
      CAst.make ?loc:(mkloc loc1) @@ CLambdaN (b, loop ty c bs)
  | (_, { loc = loc1; v = CLetIn (x, v, oty, _) } ) :: bs ->
      CAst.make ?loc:(mkloc loc1) @@ CLetIn (x, v, oty, loop ty c bs)
  | [] -> c
  | _ -> anomaly "binder not a lambda nor a let in" in
  match c2 with
  | { loc; v = CCast (ct, defaultCast, cty) } ->
      CAst.make ?loc @@ (CCast (loop false ct bs, defaultCast, (loop true cty bs)))
  | ct -> loop false ct bs

let rec fix_binders = let open CAst in function
  | (_, { v = CLambdaN ([CLocalAssum(xs, _, t)], _) } ) :: bs ->
      CLocalAssum (xs, Default Glob_term.Explicit, t) :: fix_binders bs
  | (_, { v = CLetIn (x, v, oty, _) } ) :: bs ->
    CLocalDef (x, v, oty) :: fix_binders bs
  | _ -> []

let pr_ssrstruct _ _ _ = function
  | Some id -> str "{struct " ++ pr_id id ++ str "}"
  | None -> mt ()



let (wit_ssrstruct, ssrstruct) = Tacentries.argument_extend ~name:"ssrstruct" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.stop)
                                                            (fun loc -> 
# 1412 "plugins/ssr/ssrparser.mlg"
           None 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "struct"))))
                                                           ((Pcoq.Symbol.nterm ident)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                           (fun _ id _ _
                                                           loc -> 
# 1411 "plugins/ssr/ssrparser.mlg"
                                      Some id 
                                                                  ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.Val.Opt 
                                                      (Geninterp.val_tag (Genarg.topwit wit_ident)));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.OptArg 
                                                         (wit_ident));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.OptArg 
                                                        (wit_ident));
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.OptArg 
                                                         (wit_ident));
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 1410 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssrstruct 
                                                          ), (fun env sigma -> 
                                                          
# 1410 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssrstruct 
                                                          ), (fun env sigma -> 
                                                          
# 1410 "plugins/ssr/ssrparser.mlg"
                                                             pr_ssrstruct 
                                                          ));
                                 }
let _ = (wit_ssrstruct, ssrstruct)


# 1419 "plugins/ssr/ssrparser.mlg"
 

let bind_fwd bs ((fk, h), c) =
 (fk,binders_fmts bs @ h), { c with body = push_binders c.body bs }



let (wit_ssrposefwd, ssrposefwd) = Tacentries.argument_extend ~name:"ssrposefwd" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ssrbinder))))
                                                              ((Pcoq.Symbol.nterm ssrfwd)))
                                                              (fun fwd bs
                                                              loc -> 
                                                              
# 1427 "plugins/ssr/ssrparser.mlg"
                                            bind_fwd bs fwd 
                                                              ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrfwd));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrfwd);
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrfwd);
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrfwd);
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 1426 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrfwd 
                                                            ), (fun env sigma -> 
                                                            
# 1426 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrfwd 
                                                            ), (fun env sigma -> 
                                                            
# 1426 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrfwd 
                                                            ));
                                   }
let _ = (wit_ssrposefwd, ssrposefwd)


# 1432 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrfixfwd _ _ _ (id, fwd) = str " fix " ++ pr_id id ++ pr_fwd fwd

let bvar_locid = function
  | { CAst.v = CRef (qid, _) } when qualid_is_ident qid ->
    CAst.make ?loc:qid.CAst.loc (qualid_basename qid)
  | _ -> CErrors.user_err (Pp.str "Missing identifier after \"(co)fix\"")



let (wit_ssrfixfwd, ssrfixfwd) = Tacentries.argument_extend ~name:"ssrfixfwd" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (CLexer.terminal "fix"))))
                                                            ((Pcoq.Symbol.nterm ssrbvar)))
                                                            ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ssrbinder))))
                                                            ((Pcoq.Symbol.nterm ssrstruct)))
                                                            ((Pcoq.Symbol.nterm ssrfwd)))
                                                            (fun fwd sid bs
                                                            bv _ loc -> 
                                                            
# 1445 "plugins/ssr/ssrparser.mlg"
      let { CAst.v=id } as lid = bvar_locid bv in
      let (fk, h), ac = fwd in
      let c = ac.body in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, mkCHole (constr_loc c), c in
      let lb = fix_binders bs in
      let has_struct, i =
        let rec loop = function
          | {CAst.loc=l'; v=Name id'} :: _ when Option.equal Id.equal sid (Some id') ->
            true, CAst.make ?loc:l' id'
          | [{CAst.loc=l';v=Name id'}] when sid = None ->
            false, CAst.make ?loc:l' id'
          | _ :: bn -> loop bn
          | [] -> CErrors.user_err (Pp.str "Bad structural argument") in
        loop (names_of_local_assums lb) in
      let h' = BFrec (has_struct, has_cast) :: binders_fmts bs in
      let fix = CAst.make ~loc @@ CFix (lid, [lid, (Some (CAst.make (CStructRec i))), lb, t', c']) in
      id, ((fk, h'),  { ac with body = fix }) 
                                                            ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.Val.Pair (
                                                      (Geninterp.val_tag (Genarg.topwit wit_ident)), 
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrfwd))));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                         (wit_ident), 
                                                         (wit_ssrfwd)));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                        (wit_ident), 
                                                        (wit_ssrfwd)));
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                         (wit_ident), 
                                                         (wit_ssrfwd)));
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 1443 "plugins/ssr/ssrparser.mlg"
                                                                 pr_ssrfixfwd 
                                                          ), (fun env sigma -> 
                                                          
# 1443 "plugins/ssr/ssrparser.mlg"
                                                                 pr_ssrfixfwd 
                                                          ), (fun env sigma -> 
                                                          
# 1443 "plugins/ssr/ssrparser.mlg"
                                                                 pr_ssrfixfwd 
                                                          ));
                                 }
let _ = (wit_ssrfixfwd, ssrfixfwd)


# 1469 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrcofixfwd _ _ _ (id, fwd) = str " cofix " ++ pr_id id ++ pr_fwd fwd



let (wit_ssrcofixfwd, ssrcofixfwd) = Tacentries.argument_extend ~name:"ssrcofixfwd" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "cofix"))))
                                                                ((Pcoq.Symbol.nterm ssrbvar)))
                                                                ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ssrbinder))))
                                                                ((Pcoq.Symbol.nterm ssrfwd)))
                                                                (fun fwd bs
                                                                bv _ loc -> 
                                                                
# 1477 "plugins/ssr/ssrparser.mlg"
      let { CAst.v=id } as lid = bvar_locid bv in
      let (fk, h), ac = fwd in
      let c = ac.body in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, mkCHole (constr_loc c), c in
      let h' = BFrec (false, has_cast) :: binders_fmts bs in
      let cofix = CAst.make ~loc @@ CCoFix (lid, [lid, fix_binders bs, t', c']) in
      id, ((fk, h'), { ac with body = cofix })
    
                                                                ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrfixfwd));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrfixfwd);
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrfixfwd);
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrfixfwd);
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 1475 "plugins/ssr/ssrparser.mlg"
                                                            pr_ssrcofixfwd 
                                                              ), (fun env sigma -> 
                                                              
# 1475 "plugins/ssr/ssrparser.mlg"
                                                            pr_ssrcofixfwd 
                                                              ), (fun env sigma -> 
                                                              
# 1475 "plugins/ssr/ssrparser.mlg"
                                                            pr_ssrcofixfwd 
                                                              ));
                                     }
let _ = (wit_ssrcofixfwd, ssrcofixfwd)


# 1489 "plugins/ssr/ssrparser.mlg"
 

(* This does not print the type, it should be fixed... *)
let pr_ssrsetfwd _ _ _ (((fk,_),(t,_)), docc) =
  pr_gen_fwd (fun _ _ -> pr_cpattern)
    (fun _ -> mt()) (fun _ -> mt()) fk ([Bcast ()],t)



let (wit_ssrsetfwd, ssrsetfwd) = Tacentries.argument_extend ~name:"ssrsetfwd" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          [(Pcoq.Production.make
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                            ((Pcoq.Symbol.nterm lcpattern)))
                                                            (fun c _ loc -> 
# 1507 "plugins/ssr/ssrparser.mlg"
                             mkssrFwdVal FwdPose c, nodocc 
                                                                    ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                           ((Pcoq.Symbol.nterm ssrocc)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                           ((Pcoq.Symbol.nterm cpattern)))
                                                           (fun c _ occ _ _
                                                           loc -> 
# 1506 "plugins/ssr/ssrparser.mlg"
    mkssrFwdVal FwdPose c, mkocc occ 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                           ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                           ((Pcoq.Symbol.nterm lcpattern)))
                                                           (fun c _ t _
                                                           loc -> 
# 1504 "plugins/ssr/ssrparser.mlg"
    mkssrFwdCast FwdPose loc t c, nodocc 
                                                                  ));
                                                          (Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                           ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                           ((Pcoq.Symbol.nterm ssrocc)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                           ((Pcoq.Symbol.nterm cpattern)))
                                                           (fun c _ occ _ _ t
                                                           _ loc -> 
# 1502 "plugins/ssr/ssrparser.mlg"
    mkssrFwdCast FwdPose loc t c, mkocc occ 
                                                                    ))]);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.Val.Pair (
                                                      (Geninterp.Val.Pair (
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrfwdfmt)), 
                                                      (Geninterp.Val.Pair (
                                                      (Geninterp.val_tag (Genarg.topwit wit_lcpattern)), 
                                                      (Geninterp.Val.Opt 
                                                      (Geninterp.val_tag (Genarg.topwit wit_ast_closure_lterm))))))), 
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrdocc))));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                         (Genarg.PairArg (
                                                         (wit_ssrfwdfmt), 
                                                         (Genarg.PairArg (
                                                         (wit_lcpattern), 
                                                         (Genarg.OptArg 
                                                         (wit_ast_closure_lterm)))))), 
                                                         (wit_ssrdocc)));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                        (Genarg.PairArg (
                                                        (wit_ssrfwdfmt), 
                                                        (Genarg.PairArg (
                                                        (wit_lcpattern), 
                                                        (Genarg.OptArg 
                                                        (wit_ast_closure_lterm)))))), 
                                                        (wit_ssrdocc)));
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                         (Genarg.PairArg (
                                                         (wit_ssrfwdfmt), 
                                                         (Genarg.PairArg (
                                                         (wit_lcpattern), 
                                                         (Genarg.OptArg 
                                                         (wit_ast_closure_lterm)))))), 
                                                         (wit_ssrdocc)));
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 1500 "plugins/ssr/ssrparser.mlg"
             pr_ssrsetfwd 
                                                          ), (fun env sigma -> 
                                                          
# 1500 "plugins/ssr/ssrparser.mlg"
             pr_ssrsetfwd 
                                                          ), (fun env sigma -> 
                                                          
# 1500 "plugins/ssr/ssrparser.mlg"
             pr_ssrsetfwd 
                                                          ));
                                 }
let _ = (wit_ssrsetfwd, ssrsetfwd)


# 1510 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrhavefwd env sigma _ _ prt (fwd, hint) = pr_fwd fwd ++ pr_hint env sigma prt hint



let (wit_ssrhavefwd, ssrhavefwd) = Tacentries.argument_extend ~name:"ssrhavefwd" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                              ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                              (fun c _ loc ->
                                                              
# 1520 "plugins/ssr/ssrparser.mlg"
                                     mkFwdVal FwdHave c, nohint 
                                                              ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                             ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                             ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                             (fun _ t _
                                                             loc -> 
# 1519 "plugins/ssr/ssrparser.mlg"
                                         mkFwdHintNoTC ":" t, nohint 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                             ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                             ((Pcoq.Symbol.token (CLexer.terminal ":="))))
                                                             ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                             (fun c _ t _
                                                             loc -> 
# 1518 "plugins/ssr/ssrparser.mlg"
                                                              mkFwdCast FwdHave ~loc t ~c, nohint 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                             ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                             ((Pcoq.Symbol.nterm ssrhint)))
                                                             (fun hint t _
                                                             loc -> 
# 1517 "plugins/ssr/ssrparser.mlg"
                                                  mkFwdHint ":" t, hint 
                                                                    ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.Pair (
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrfwd)), 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrhint))));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                           (wit_ssrfwd), 
                                                           (wit_ssrhint)));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                          (wit_ssrfwd), 
                                                          (wit_ssrhint)));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                           (wit_ssrfwd), 
                                                           (wit_ssrhint)));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 1516 "plugins/ssr/ssrparser.mlg"
                                                                    pr_ssrhavefwd env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 1516 "plugins/ssr/ssrparser.mlg"
                                                                    pr_ssrhavefwd env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 1516 "plugins/ssr/ssrparser.mlg"
                                                                    pr_ssrhavefwd env sigma 
                                                            ));
                                   }
let _ = (wit_ssrhavefwd, ssrhavefwd)


# 1523 "plugins/ssr/ssrparser.mlg"
 

let intro_id_to_binder = List.map (function
  | IPatId id ->
      let { CAst.loc=xloc } as x = bvar_lname (mkCVar id) in
      (FwdPose, [BFvar]),
        CAst.make @@ CLambdaN ([CLocalAssum([x], Default Glob_term.Explicit, mkCHole xloc)],
          mkCHole None)
  | _ -> anomaly "non-id accepted as binder")

let binder_to_intro_id = CAst.(List.map (function
  | (FwdPose, [BFvar]), { v = CLambdaN ([CLocalAssum(ids,_,_)],_) }
  | (FwdPose, [BFdecl _]), { v = CLambdaN ([CLocalAssum(ids,_,_)],_) } ->
      List.map (function {v=Name id} -> IPatId id | _ -> IPatAnon (One None)) ids
  | (FwdPose, [BFdef]), { v = CLetIn ({v=Name id},_,_,_) } -> [IPatId id]
  | (FwdPose, [BFdef]), { v = CLetIn ({v=Anonymous},_,_,_) } -> [IPatAnon (One None)]
  | _ -> anomaly "ssrbinder is not a binder"))

let pr_ssrhavefwdwbinders env sigma _ _ prt (tr,((hpats, (fwd, hint)))) =
  pr_hpats hpats ++ pr_fwd fwd ++ pr_hint env sigma prt hint



let (wit_ssrhavefwdwbinders, ssrhavefwdwbinders) = Tacentries.argument_extend ~name:"ssrhavefwdwbinders" 
                                                   {
                                                   Tacentries.arg_parsing = 
                                                   Vernacextend.Arg_rules (
                                                   [(Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm ssrhpats_wtransp)))
                                                     ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ssrbinder))))
                                                     ((Pcoq.Symbol.nterm ssrhavefwd)))
                                                     (fun fwd bs trpats
                                                     loc -> 
# 1550 "plugins/ssr/ssrparser.mlg"
    let tr, pats = trpats in
    let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    let hint = bind_fwd allbs (fst fwd), snd fwd in
    tr, ((((clr, pats), allbinders), simpl), hint) 
                                                            ))]);
                                                   Tacentries.arg_tag = 
                                                   Some
                                                   (Geninterp.Val.Pair (
                                                   (Geninterp.val_tag (Genarg.topwit wit_bool)), 
                                                   (Geninterp.Val.Pair (
                                                   (Geninterp.val_tag (Genarg.topwit wit_ssrhpats)), 
                                                   (Geninterp.Val.Pair (
                                                   (Geninterp.val_tag (Genarg.topwit wit_ssrfwd)), 
                                                   (Geninterp.val_tag (Genarg.topwit wit_ssrhint))))))));
                                                   Tacentries.arg_intern = 
                                                   Tacentries.ArgInternWit (Genarg.PairArg (
                                                   (wit_bool), (Genarg.PairArg (
                                                               (wit_ssrhpats), 
                                                               (Genarg.PairArg (
                                                               (wit_ssrfwd), 
                                                               (wit_ssrhint)))))));
                                                   Tacentries.arg_subst = 
                                                   Tacentries.ArgSubstWit (Genarg.PairArg (
                                                   (wit_bool), (Genarg.PairArg (
                                                               (wit_ssrhpats), 
                                                               (Genarg.PairArg (
                                                               (wit_ssrfwd), 
                                                               (wit_ssrhint)))))));
                                                   Tacentries.arg_interp = 
                                                   Tacentries.ArgInterpWit (Genarg.PairArg (
                                                   (wit_bool), (Genarg.PairArg (
                                                               (wit_ssrhpats), 
                                                               (Genarg.PairArg (
                                                               (wit_ssrfwd), 
                                                               (wit_ssrhint)))))));
                                                   Tacentries.arg_printer = 
                                                   ((fun env sigma -> 
                                                   
# 1548 "plugins/ssr/ssrparser.mlg"
               pr_ssrhavefwdwbinders env sigma 
                                                   ), (fun env sigma -> 
                                                   
# 1548 "plugins/ssr/ssrparser.mlg"
               pr_ssrhavefwdwbinders env sigma 
                                                   ), (fun env sigma -> 
                                                   
# 1548 "plugins/ssr/ssrparser.mlg"
               pr_ssrhavefwdwbinders env sigma 
                                                   ));
                                                   }
let _ = (wit_ssrhavefwdwbinders, ssrhavefwdwbinders)


# 1558 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrdoarg env sigma prc _ prt (((n, m), tac), clauses) =
  pr_index n ++ pr_mmod m ++ pr_hintarg env sigma prt tac ++ pr_clauses clauses



let (wit_ssrdoarg, ssrdoarg) = Tacentries.argument_extend ~name:"ssrdoarg" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        []);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrindex)), 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrmmod)))), 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrhintarg)))), 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrclauses))));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (wit_ssrindex), 
                                                       (wit_ssrmmod))), 
                                                       (wit_ssrhintarg))), 
                                                       (wit_ssrclauses)));
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                      (Genarg.PairArg (
                                                      (Genarg.PairArg (
                                                      (wit_ssrindex), 
                                                      (wit_ssrmmod))), 
                                                      (wit_ssrhintarg))), 
                                                      (wit_ssrclauses)));
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (wit_ssrindex), 
                                                       (wit_ssrmmod))), 
                                                       (wit_ssrhintarg))), 
                                                       (wit_ssrclauses)));
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 1567 "plugins/ssr/ssrparser.mlg"
               pr_ssrdoarg env sigma 
                                                        ), (fun env sigma -> 
                                                        
# 1567 "plugins/ssr/ssrparser.mlg"
               pr_ssrdoarg env sigma 
                                                        ), (fun env sigma -> 
                                                        
# 1567 "plugins/ssr/ssrparser.mlg"
               pr_ssrdoarg env sigma 
                                                        ));
                               }
let _ = (wit_ssrdoarg, ssrdoarg)


# 1570 "plugins/ssr/ssrparser.mlg"
 

(* type ssrseqarg = ssrindex * (ssrtacarg * ssrtac option) *)

let pr_seqtacarg env sigma prt = function
  | (is_first, []), _ -> str (if is_first then "first" else "last")
  | tac, Some dtac ->
    hv 0 (pr_hintarg env sigma prt tac ++ spc() ++ str "|| " ++ prt env sigma tacltop dtac)
  | tac, _ -> pr_hintarg env sigma prt tac

let pr_ssrseqarg env sigma _ _ prt = function
  | ArgArg 0, tac -> pr_seqtacarg env sigma prt tac
  | i, tac -> pr_index i ++ str " " ++ pr_seqtacarg env sigma prt tac



let (wit_ssrseqarg, ssrseqarg) = Tacentries.argument_extend ~name:"ssrseqarg" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          []);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.Val.Pair (
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrindex)), 
                                                      (Geninterp.Val.Pair (
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrhintarg)), 
                                                      (Geninterp.Val.Opt 
                                                      (Geninterp.val_tag (Genarg.topwit wit_tactic)))))));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                         (wit_ssrindex), 
                                                         (Genarg.PairArg (
                                                         (wit_ssrhintarg), 
                                                         (Genarg.OptArg 
                                                         (wit_tactic))))));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                        (wit_ssrindex), 
                                                        (Genarg.PairArg (
                                                        (wit_ssrhintarg), 
                                                        (Genarg.OptArg 
                                                        (wit_tactic))))));
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                         (wit_ssrindex), 
                                                         (Genarg.PairArg (
                                                         (wit_ssrhintarg), 
                                                         (Genarg.OptArg 
                                                         (wit_tactic))))));
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 1589 "plugins/ssr/ssrparser.mlg"
                                       pr_ssrseqarg env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 1589 "plugins/ssr/ssrparser.mlg"
                                       pr_ssrseqarg env sigma 
                                                          ), (fun env sigma -> 
                                                          
# 1589 "plugins/ssr/ssrparser.mlg"
                                       pr_ssrseqarg env sigma 
                                                          ));
                                 }
let _ = (wit_ssrseqarg, ssrseqarg)


# 1593 "plugins/ssr/ssrparser.mlg"
 

let sq_brace_tacnames =
   ["first"; "solve"; "do"; "rewrite"; "have"; "suffices"; "wlog"]
   (* "by" is a keyword *)

let test_ssrseqvar =
  let open Pcoq.Lookahead in
  to_entry "test_ssrseqvar" begin
    lk_ident_except sq_brace_tacnames >> (lk_kws ["[";"first";"last"])
  end

let swaptacarg (loc, b) = (b, []), Some (CAst.make ~loc (TacId []))

let check_seqtacarg dir arg = match snd arg, dir with
  | ((true, []), Some { CAst.loc; v=(TacAtom _)}), L2R ->
    CErrors.user_err ?loc (str "expected \"last\"")
  | ((false, []), Some { CAst.loc; v=(TacAtom _) }), R2L ->
    CErrors.user_err ?loc (str "expected \"first\"")
  | _, _ -> arg

let ssrorelse = Entry.create "ssrorelse"



let _ = let ssrseqidx = Pcoq.Entry.make "ssrseqidx"
        and ssrswap = Pcoq.Entry.make "ssrswap"
        in
        let () = assert (Pcoq.Entry.is_empty ssrseqidx) in
        let () =
        Pcoq.grammar_extend ssrseqidx
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.natural)))
                                  (fun n loc -> 
# 1622 "plugins/ssr/ssrparser.mlg"
                            ArgArg (check_index ~loc n) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_ssrseqvar)))
                                                 ((Pcoq.Symbol.nterm Prim.ident)))
                                 (fun id _ loc -> 
# 1621 "plugins/ssr/ssrparser.mlg"
                                           ArgVar (CAst.make ~loc id) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty ssrswap) in
        let () =
        Pcoq.grammar_extend ssrswap
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("last"))))))
                                  (fun _ loc -> 
# 1624 "plugins/ssr/ssrparser.mlg"
                                                                 loc, false 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("first"))))))
                                 (fun _ loc -> 
# 1624 "plugins/ssr/ssrparser.mlg"
                                 loc, true 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty ssrorelse) in
        let () =
        Pcoq.grammar_extend ssrorelse
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("||")))))
                                                  ((Pcoq.Symbol.nterml ltac_expr ("2"))))
                                  (fun tac _ loc -> 
# 1625 "plugins/ssr/ssrparser.mlg"
                                                     tac 
                                                    )])]))
        in let () =
        Pcoq.grammar_extend ssrseqarg
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.stop)
                                            ((Pcoq.Symbol.nterml ltac_expr ("3"))))
                            (fun tac loc -> 
# 1630 "plugins/ssr/ssrparser.mlg"
                                     noindex, (mk_hint tac, None) 
                                            );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssrseqidx)))
                                           ((Pcoq.Symbol.nterm ssrswap)))
                           (fun arg i loc -> 
# 1629 "plugins/ssr/ssrparser.mlg"
                                        i, swaptacarg arg 
                                             );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm ssrseqidx)))
                                                           ((Pcoq.Symbol.nterm ssrortacarg)))
                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ssrorelse))))
                           (fun def tac i loc -> 
# 1628 "plugins/ssr/ssrparser.mlg"
                                                                 i, (tac, def) 
                                                 );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.nterm ssrswap)))
                           (fun arg loc -> 
# 1627 "plugins/ssr/ssrparser.mlg"
                         noindex, swaptacarg arg 
                                           )]))
        in ()


# 1634 "plugins/ssr/ssrparser.mlg"
 

let ltac_expr = Pltac.ltac_expr




# 1653 "plugins/ssr/ssrparser.mlg"
 

let ssr_reserved_ids = Summary.ref ~name:"SSR:idents" true

let () =
  Goptions.(declare_bool_option
    { optkey   = ["SsrIdents"];
      optdepr  = false;
      optread  = (fun _ -> !ssr_reserved_ids);
      optwrite = (fun b -> ssr_reserved_ids := b)
    })

let is_ssr_reserved s =
  let n = String.length s in n > 2 && s.[0] = '_' && s.[n - 1] = '_'

let ssr_id_of_string loc s =
  if is_ssr_reserved s && is_ssr_loaded () then begin
    if !ssr_reserved_ids then
      CErrors.user_err ~loc (str ("The identifier " ^ s ^ " is reserved."))
    else if is_internal_name s then
      Feedback.msg_warning (str ("Conflict between " ^ s ^ " and ssreflect internal names."))
    else Feedback.msg_warning (str (
     "The name " ^ s ^ " fits the _xxx_ format used for anonymous variables.\n"
  ^ "Scripts with explicit references to anonymous variables are fragile."))
    end; Id.of_string s

let ssr_null_entry = Pcoq.Entry.(of_parser "ssr_null" { parser_fun = fun _ -> () })



let _ = let () =
        Pcoq.grammar_extend Prim.ident
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                            ((Pcoq.Symbol.nterm ssr_null_entry)))
                            (fun _ s loc -> 
# 1685 "plugins/ssr/ssrparser.mlg"
                                                    ssr_id_of_string loc s 
                                            )]))
        in ()


# 1688 "plugins/ssr/ssrparser.mlg"
 

let perm_tag = "_perm_Hyp_"
let _ = add_internal_name (is_tagged perm_tag)




# 1699 "plugins/ssr/ssrparser.mlg"
 

  let ssrtac_expr ?loc key args =
    CAst.make ?loc (TacAlias (key, (List.map (fun x -> Tacexpr.TacGeneric (None, x)) args)))

let mk_non_term wit id =
  let open Pptactic in
  TacNonTerm (None, (Extend.Uentry (Genarg.ArgT.Any (Genarg.get_arg_tag wit)), Some id))

let tclintroskey =
  let prods =
    [ mk_non_term wit_ssrintrosarg (Names.Id.of_string "arg") ] in
  let tac = begin fun args ist -> match args with
    | [arg] ->
      let arg = cast_arg wit_ssrintrosarg arg in
      let tac, intros = arg in
      ssrevaltac ist tac <*> tclIPATssr intros
    | _ -> assert false
  end in
  register_ssrtac "tclintros" tac prods

let tclintros_expr ?loc tac ipats =
  let args = [in_gen (rawwit wit_ssrintrosarg) (tac, ipats)] in
  ssrtac_expr ?loc tclintroskey args



let _ = let () =
        Pcoq.grammar_extend ltac_expr
        (Pcoq.Reuse (Some
        ("1"), [Pcoq.Production.make
                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                ((Pcoq.Symbol.nterm ssrintros_ne)))
                (fun intros tac loc -> 
# 1729 "plugins/ssr/ssrparser.mlg"
                                                  tclintros_expr ~loc tac intros 
                                       )]))
        in ()

let _ = let ssrparentacarg = Pcoq.Entry.make "ssrparentacarg"
        in
        let () = assert (Pcoq.Entry.is_empty ssrparentacarg) in
        let () =
        Pcoq.grammar_extend ssrparentacarg
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm ltac_expr)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ tac _ loc -> 
# 1744 "plugins/ssr/ssrparser.mlg"
                                                    CAst.make ~loc (Tacexp tac) 
                                                      )])]))
        in let () =
        Pcoq.grammar_extend ltac_expr
        (Pcoq.Reuse (Some
        ("0"), [Pcoq.Production.make
                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                ((Pcoq.Symbol.nterm ssrparentacarg)))
                (fun arg loc -> 
# 1745 "plugins/ssr/ssrparser.mlg"
                                                    CAst.make ~loc (TacArg CAst.(arg.v)) 
                                )]))
        in ()


# 1757 "plugins/ssr/ssrparser.mlg"
 

let ssrautoprop =
  Proofview.Goal.enter begin fun gl ->
  try
    let tacname =
      try Tacenv.locate_tactic (qualid_of_ident (Id.of_string "ssrautoprop"))
      with Not_found -> Tacenv.locate_tactic (ssrqid "ssrautoprop") in
    let tacexpr = CAst.make @@ Tacexpr.Reference (ArgArg (Loc.tag @@ tacname)) in
    eval_tactic (CAst.make @@ Tacexpr.TacArg CAst.(tacexpr.v))
  with Not_found -> Auto.full_trivial []
  end

let () = ssrautoprop_tac := ssrautoprop

let tclBY tac = Tacticals.tclTHEN tac (donetac ~-1)

(** Tactical arguments. *)

(* We have four kinds: simple tactics, [|]-bracketed lists, hints, and swaps *)
(* The latter two are used in forward-chaining tactics (have, suffice, wlog) *)
(* and subgoal reordering tacticals (; first & ; last), respectively.        *)

(* Force use of the ltac_expr parsing entry, to rule out tick marks. *)

(** The "by" tactical. *)


open Ssrfwd



let () = Tacentries.tactic_extend __coq_plugin_name "ssrtclby" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("by", Tacentries.TyArg (
                                                      Extend.TUentry (Genarg.get_arg_tag wit_ssrhintarg), 
                                                      Tacentries.TyNil)), 
           (fun tac ist -> 
# 1790 "plugins/ssr/ssrparser.mlg"
                                hinttac ist true tac 
           )))]

let _ = let () =
        Pcoq.grammar_extend ssrhint
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("by")))))
                                            ((Pcoq.Symbol.nterm ssrhintarg)))
                            (fun arg _ loc -> 
# 1798 "plugins/ssr/ssrparser.mlg"
                                              arg 
                                              )]))
        in ()


# 1803 "plugins/ssr/ssrparser.mlg"
 

let tcldokey =
  let open Pptactic in
  let prods = [ TacTerm "do"; mk_non_term wit_ssrdoarg (Names.Id.of_string "arg") ] in
  let tac = begin fun args ist -> match args with
    | [arg] ->
      let arg = cast_arg wit_ssrdoarg arg in
      ssrdotac ist arg
    | _ -> assert false
  end in
  register_ssrtac "tcldo" tac prods

let ssrdotac_expr ?loc n m tac clauses =
  let arg = ((n, m), tac), clauses in
  ssrtac_expr ?loc tcldokey [in_gen (rawwit wit_ssrdoarg) arg]



let _ = let ssrdotac = Pcoq.Entry.make "ssrdotac"
        in
        let () = assert (Pcoq.Entry.is_empty ssrdotac) in
        let () =
        Pcoq.grammar_extend ssrdotac
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ssrortacarg)))
                                  (fun tacs loc -> 
# 1826 "plugins/ssr/ssrparser.mlg"
                              tacs 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterml ltac_expr ("3"))))
                                 (fun tac loc -> 
# 1825 "plugins/ssr/ssrparser.mlg"
                                     mk_hint tac 
                                                 )])]))
        in let () =
        Pcoq.grammar_extend ltac_expr
        (Pcoq.Reuse (Some
        ("3"), [Pcoq.Production.make
                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("do"))))))
                                                                ((Pcoq.Symbol.nterm nat_or_var)))
                                                                ((Pcoq.Symbol.nterm ssrmmod)))
                                                ((Pcoq.Symbol.nterm ssrdotac)))
                                ((Pcoq.Symbol.nterm ssrclauses)))
                (fun clauses tac m n _ loc -> 
# 1835 "plugins/ssr/ssrparser.mlg"
        ssrdotac_expr ~loc (mk_index ~loc n) m tac clauses 
                                              );
               Pcoq.Production.make
               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                               ("do"))))))
                                               ((Pcoq.Symbol.nterm ssrortacarg)))
                               ((Pcoq.Symbol.nterm ssrclauses)))
               (fun clauses tac _ loc -> 
# 1832 "plugins/ssr/ssrparser.mlg"
        ssrdotac_expr ~loc noindex Once tac clauses 
                                         );
               Pcoq.Production.make
               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                               ("do"))))))
                                                               ((Pcoq.Symbol.nterm ssrmmod)))
                                               ((Pcoq.Symbol.nterm ssrdotac)))
                               ((Pcoq.Symbol.nterm ssrclauses)))
               (fun clauses tac m _ loc -> 
# 1830 "plugins/ssr/ssrparser.mlg"
        ssrdotac_expr ~loc noindex m tac clauses 
                                           )]))
        in ()


# 1839 "plugins/ssr/ssrparser.mlg"
 

(* We can't actually parse the direction separately because this   *)
(* would introduce conflicts with the basic ltac syntax.           *)
let pr_ssrseqdir _ _ _ = function
  | L2R -> str ";" ++ spc () ++ str "first "
  | R2L -> str ";" ++ spc () ++ str "last "



let (wit_ssrseqdir, ssrseqdir) = Tacentries.argument_extend ~name:"ssrseqdir" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          []);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrdir));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrdir);
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrdir);
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrdir);
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 1849 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrseqdir 
                                                          ), (fun env sigma -> 
                                                          
# 1849 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrseqdir 
                                                          ), (fun env sigma -> 
                                                          
# 1849 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrseqdir 
                                                          ));
                                 }
let _ = (wit_ssrseqdir, ssrseqdir)


# 1852 "plugins/ssr/ssrparser.mlg"
 

let tclseqkey =
  let prods =
    [ mk_non_term wit_ssrtclarg (Names.Id.of_string "tac")
    ; mk_non_term wit_ssrseqdir (Names.Id.of_string "dir")
    ; mk_non_term wit_ssrseqarg (Names.Id.of_string "arg") ] in
  let tac =  begin fun args ist -> match args with
    | [tac; dir; arg] ->
      let tac = cast_arg wit_ssrtclarg tac in
      let dir = cast_arg wit_ssrseqdir dir in
      let arg = cast_arg wit_ssrseqarg arg in
      tclSEQAT ist tac dir arg
    | _ -> assert false
  end in
  register_ssrtac "tclseq" tac prods

let tclseq_expr ?loc tac dir arg =
  let arg1 = in_gen (rawwit wit_ssrtclarg) tac in
  let arg2 = in_gen (rawwit wit_ssrseqdir) dir in
  let arg3 = in_gen (rawwit wit_ssrseqarg) (check_seqtacarg dir arg) in
  ssrtac_expr ?loc tclseqkey [arg1; arg2; arg3]



let _ = let ssr_first = Pcoq.Entry.make "ssr_first"
        and ssr_first_else = Pcoq.Entry.make "ssr_first_else"
        in
        let () = assert (Pcoq.Entry.is_empty ssr_first) in
        let () =
        Pcoq.grammar_extend ssr_first
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm ltac_expr)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                  (fun _ tacl _ loc -> 
# 1881 "plugins/ssr/ssrparser.mlg"
                                                    CAst.make ~loc (TacFirst tacl) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ssr_first)))
                                                 ((Pcoq.Symbol.nterm ssrintros_ne)))
                                 (fun ipats tac loc -> 
# 1880 "plugins/ssr/ssrparser.mlg"
                                                 tclintros_expr ~loc tac ipats 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty ssr_first_else) in
        let () =
        Pcoq.grammar_extend ssr_first_else
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ssr_first)))
                                  (fun tac loc -> 
# 1885 "plugins/ssr/ssrparser.mlg"
                           tac 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ssr_first)))
                                                 ((Pcoq.Symbol.nterm ssrorelse)))
                                 (fun tac2 tac1 loc -> 
# 1884 "plugins/ssr/ssrparser.mlg"
                                              CAst.make ~loc (TacOrelse (tac1, tac2)) 
                                                       )])]))
        in let () =
        Pcoq.grammar_extend ltac_expr
        (Pcoq.Reuse (Some
        ("4"), [Pcoq.Production.make
                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                ("last"))))))
                                ((Pcoq.Symbol.nterm ssrseqarg)))
                (fun arg _ _ tac loc -> 
# 1892 "plugins/ssr/ssrparser.mlg"
        tclseq_expr ~loc tac R2L arg 
                                        );
               Pcoq.Production.make
               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ltac_expr)))
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                               ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                               ("first"))))))
                               ((Pcoq.Symbol.nterm ssrseqarg)))
               (fun arg _ _ tac loc -> 
# 1890 "plugins/ssr/ssrparser.mlg"
        tclseq_expr ~loc tac L2R arg 
                                       );
               Pcoq.Production.make
               (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ltac_expr)))
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                               ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                               ("first"))))))
                               ((Pcoq.Symbol.nterm ssr_first_else)))
               (fun tac2 _ _ tac1 loc -> 
# 1888 "plugins/ssr/ssrparser.mlg"
        CAst.make ~loc (TacThen (tac1, tac2)) 
                                         )]))
        in ()


# 1904 "plugins/ssr/ssrparser.mlg"
 

let pr_gen (docc, dt) = pr_docc docc ++ pr_cpattern dt

let pr_ssrgen _ _ _ = pr_gen



let (wit_ssrgen, ssrgen) = Tacentries.argument_extend ~name:"ssrgen" 
                           {
                           Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                    [(Pcoq.Production.make
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.stop)
                                                      ((Pcoq.Symbol.nterm cpattern)))
                                                      (fun dt loc -> 
# 1917 "plugins/ssr/ssrparser.mlg"
                        nodocc, dt 
                                                                    ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm ssrdocc)))
                                                     ((Pcoq.Symbol.nterm cpattern)))
                                                     (fun dt docc loc -> 
# 1913 "plugins/ssr/ssrparser.mlg"
                                     
     match docc with
     | Some [], _ -> CErrors.user_err ~loc (str"Clear flag {} not allowed here")
     | _ -> docc, dt 
                                                                    ))]);
                           Tacentries.arg_tag = Some
                                                (Geninterp.Val.Pair (
                                                (Geninterp.val_tag (Genarg.topwit wit_ssrdocc)), 
                                                (Geninterp.val_tag (Genarg.topwit wit_cpattern))));
                           Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                   (wit_ssrdocc), (wit_cpattern)));
                           Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                  (wit_ssrdocc), (wit_cpattern)));
                           Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                   (wit_ssrdocc), (wit_cpattern)));
                           Tacentries.arg_printer = ((fun env sigma -> 
                                                    
# 1912 "plugins/ssr/ssrparser.mlg"
                                                                  pr_ssrgen 
                                                    ), (fun env sigma -> 
                                                    
# 1912 "plugins/ssr/ssrparser.mlg"
                                                                  pr_ssrgen 
                                                    ), (fun env sigma -> 
                                                    
# 1912 "plugins/ssr/ssrparser.mlg"
                                                                  pr_ssrgen 
                                                    ));
                           }
let _ = (wit_ssrgen, ssrgen)


# 1920 "plugins/ssr/ssrparser.mlg"
 

let has_occ ((_, occ), _) = occ <> None

(** Generalization (discharge) sequence *)

(* A discharge sequence is represented as a list of up to two   *)
(* lists of d-items, plus an ident list set (the possibly empty *)
(* final clear switch). The main list is empty iff the command  *)
(* is defective, and has length two if there is a sequence of   *)
(* dependent terms (and in that case it is the first of the two *)
(* lists). Thus, the first of the two lists is never empty.     *)

(* type ssrgens = ssrgen list *)
(* type ssrdgens = ssrgens list * ssrclear *)

let gens_sep = function [], [] -> mt | _ -> spc

let pr_dgens pr_gen (gensl, clr) =
  let prgens s gens =
  if CList.is_empty gens then mt () else str s ++ pr_list spc pr_gen gens in
  let prdeps deps = prgens ": " deps ++ spc () ++ str "/" in
  match gensl with
  | [deps; []] -> prdeps deps ++ pr_clear pr_spc clr
  | [deps; gens] -> prdeps deps ++ prgens " " gens ++ pr_clear spc clr
  | [gens] -> prgens ": " gens ++ pr_clear spc clr
  | _ -> pr_clear pr_spc clr

let pr_ssrdgens _ _ _ = pr_dgens pr_gen

let cons_gen gen = function
  | gens :: gensl, clr -> (gen :: gens) :: gensl, clr
  | _ -> anomaly "missing gen list"

let cons_dep (gensl, clr) =
  if List.length gensl = 1 then ([] :: gensl, clr) else
  CErrors.user_err (Pp.str "multiple dependents switches '/'")



let (wit_ssrdgens_tl, ssrdgens_tl) = Tacentries.argument_extend ~name:"ssrdgens_tl" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.stop)
                                                                (fun loc -> 
# 1973 "plugins/ssr/ssrparser.mlg"
    [[]], [] 
                                                                    ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm cpattern)))
                                                               (Pcoq.Symbol.self))
                                                               (fun dgens dt
                                                               loc -> 
                                                               
# 1971 "plugins/ssr/ssrparser.mlg"
    cons_gen (nodocc, dt) dgens 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "/"))))
                                                               (Pcoq.Symbol.self))
                                                               (fun dgens _
                                                               loc -> 
                                                               
# 1969 "plugins/ssr/ssrparser.mlg"
    cons_dep dgens 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                               ((Pcoq.Symbol.nterm ssrocc)))
                                                               ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                               ((Pcoq.Symbol.nterm cpattern)))
                                                               (Pcoq.Symbol.self))
                                                               (fun dgens dt
                                                               _ occ _ loc ->
                                                               
# 1967 "plugins/ssr/ssrparser.mlg"
    cons_gen (mkocc occ, dt) dgens 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                               ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrhyp)))))
                                                               ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                               (fun _ clr _
                                                               loc -> 
                                                               
# 1965 "plugins/ssr/ssrparser.mlg"
    [[]], clr 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                               ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrhyp)))))
                                                               ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                               ((Pcoq.Symbol.nterm cpattern)))
                                                               (Pcoq.Symbol.self))
                                                               (fun dgens dt
                                                               _ clr _ loc ->
                                                               
# 1963 "plugins/ssr/ssrparser.mlg"
    cons_gen (mkclr clr, dt) dgens 
                                                               ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.Val.Pair (
                                                          (Geninterp.Val.List 
                                                          (Geninterp.Val.List 
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrgen)))), 
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrclear))));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                             (Genarg.ListArg 
                                                             (Genarg.ListArg 
                                                             (wit_ssrgen))), 
                                                             (wit_ssrclear)));
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                            (Genarg.ListArg 
                                                            (Genarg.ListArg 
                                                            (wit_ssrgen))), 
                                                            (wit_ssrclear)));
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                             (Genarg.ListArg 
                                                             (Genarg.ListArg 
                                                             (wit_ssrgen))), 
                                                             (wit_ssrclear)));
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 1961 "plugins/ssr/ssrparser.mlg"
                                         pr_ssrdgens 
                                                              ), (fun env sigma -> 
                                                              
# 1961 "plugins/ssr/ssrparser.mlg"
                                         pr_ssrdgens 
                                                              ), (fun env sigma -> 
                                                              
# 1961 "plugins/ssr/ssrparser.mlg"
                                         pr_ssrdgens 
                                                              ));
                                     }
let _ = (wit_ssrdgens_tl, ssrdgens_tl)

let (wit_ssrdgens, ssrdgens) = Tacentries.argument_extend ~name:"ssrdgens" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                          ((Pcoq.Symbol.nterm ssrgen)))
                                                          ((Pcoq.Symbol.nterm ssrdgens_tl)))
                                                          (fun dgens gen _
                                                          loc -> 
# 1977 "plugins/ssr/ssrparser.mlg"
                                              cons_gen gen dgens 
                                                                 ))]);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrdgens_tl));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrdgens_tl);
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrdgens_tl);
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrdgens_tl);
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 1976 "plugins/ssr/ssrparser.mlg"
                                                           pr_ssrdgens 
                                                        ), (fun env sigma -> 
                                                        
# 1976 "plugins/ssr/ssrparser.mlg"
                                                           pr_ssrdgens 
                                                        ), (fun env sigma -> 
                                                        
# 1976 "plugins/ssr/ssrparser.mlg"
                                                           pr_ssrdgens 
                                                        ));
                               }
let _ = (wit_ssrdgens, ssrdgens)


# 1984 "plugins/ssr/ssrparser.mlg"
 
type ssreqid = ssripatrep option

let pr_eqid = function Some pat -> str " " ++ pr_ipat pat | None -> mt ()
let pr_ssreqid _ _ _ = pr_eqid



let (wit_ssreqid, ssreqid) = Tacentries.argument_extend ~name:"ssreqid" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      []);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.Val.Opt 
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssripatrep)));
                             Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                     
# 1996 "plugins/ssr/ssrparser.mlg"
                  intern_ipat_option 
                                                     ));
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.OptArg 
                                                    (wit_ssripatrep));
                             Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                     
# 1995 "plugins/ssr/ssrparser.mlg"
                   interp_ipat_option 
                                                     );
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 1994 "plugins/ssr/ssrparser.mlg"
                                                                pr_ssreqid 
                                                      ), (fun env sigma -> 
                                                      
# 1994 "plugins/ssr/ssrparser.mlg"
                                                                pr_ssreqid 
                                                      ), (fun env sigma -> 
                                                      
# 1994 "plugins/ssr/ssrparser.mlg"
                                                                pr_ssreqid 
                                                      ));
                             }
let _ = (wit_ssreqid, ssreqid)


# 2000 "plugins/ssr/ssrparser.mlg"
 

let test_ssreqid =
  let open Pcoq.Lookahead in
  to_entry "test_ssreqid" begin
    ((lk_ident <+> lk_kws ["_"; "?"; "->"; "<-"]) >> lk_kw ":") <+> lk_kw ":"
  end



let _ = let ssreqpat = Pcoq.Entry.make "ssreqpat"
        in
        let () = assert (Pcoq.Entry.is_empty ssreqpat) in
        let () =
        Pcoq.grammar_extend ssreqpat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("<-")))))
                                  (fun _ loc -> 
# 2024 "plugins/ssr/ssrparser.mlg"
                IPatRewrite (allocc, R2L) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("->")))))
                                 (fun _ loc -> 
# 2023 "plugins/ssr/ssrparser.mlg"
                IPatRewrite (allocc, L2R) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ssrdocc)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("<-")))))
                                 (fun _ occ loc -> 
# 2020 "plugins/ssr/ssrparser.mlg"
                               match occ with
      | None, occ ->  IPatRewrite (occ, R2L)
      | _ -> CErrors.user_err ~loc (str "Only occurrences are allowed here") 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ssrdocc)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("->")))))
                                 (fun _ occ loc -> 
# 2017 "plugins/ssr/ssrparser.mlg"
                               match occ with
      | None, occ -> IPatRewrite (occ, L2R)
      | _ -> CErrors.user_err ~loc (str"Only occurrences are allowed here") 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                 (fun _ loc -> 
# 2016 "plugins/ssr/ssrparser.mlg"
               IPatAnon Temporary 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                 (fun _ loc -> 
# 2015 "plugins/ssr/ssrparser.mlg"
               IPatAnon (One None) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                 (fun _ loc -> 
# 2014 "plugins/ssr/ssrparser.mlg"
               IPatAnon Drop 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.ident)))
                                 (fun id loc -> 
# 2013 "plugins/ssr/ssrparser.mlg"
                           IPatId id 
                                                )])]))
        in let () =
        Pcoq.grammar_extend ssreqid
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.stop)
                                            ((Pcoq.Symbol.nterm test_ssreqid)))
                            (fun _ loc -> 
# 2028 "plugins/ssr/ssrparser.mlg"
                        None 
                                          );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_ssreqid)))
                                           ((Pcoq.Symbol.nterm ssreqpat)))
                           (fun pat _ loc -> 
# 2027 "plugins/ssr/ssrparser.mlg"
                                        Some pat 
                                             )]))
        in ()


# 2039 "plugins/ssr/ssrparser.mlg"
 

type ssrarg = ssrfwdview * (ssreqid * (cpattern ssragens * ssripats))

(* type ssrarg = ssrbwdview * (ssreqid * (ssrdgens * ssripats)) *)

let pr_ssrarg _ _ _ (view, (eqid, (dgens, ipats))) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view2 view ++ pr_eqid eqid ++ pr_dgens pr_gen dgens ++ pri ipats



let (wit_ssrarg, ssrarg) = Tacentries.argument_extend ~name:"ssrarg" 
                           {
                           Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                    [(Pcoq.Production.make
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.stop)
                                                      ((Pcoq.Symbol.nterm ssrintros_ne)))
                                                      (fun ipats loc -> 
# 2062 "plugins/ssr/ssrparser.mlg"
    [], (None, (([], []), ipats)) 
                                                                    ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm ssrclear_ne)))
                                                     ((Pcoq.Symbol.nterm ssrintros)))
                                                     (fun ipats clr loc -> 
# 2060 "plugins/ssr/ssrparser.mlg"
    [], (None, (([], clr), ipats)) 
                                                                    ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm ssreqid)))
                                                     ((Pcoq.Symbol.nterm ssrdgens)))
                                                     ((Pcoq.Symbol.nterm ssrintros)))
                                                     (fun ipats dgens eqid
                                                     loc -> 
# 2058 "plugins/ssr/ssrparser.mlg"
    [], (eqid, (dgens, ipats)) 
                                                            ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm ssrfwdview)))
                                                     ((Pcoq.Symbol.nterm ssrclear)))
                                                     ((Pcoq.Symbol.nterm ssrintros)))
                                                     (fun ipats clr view
                                                     loc -> 
# 2056 "plugins/ssr/ssrparser.mlg"
    view, (None, (([], clr), ipats)) 
                                                            ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm ssrfwdview)))
                                                     ((Pcoq.Symbol.nterm ssreqid)))
                                                     ((Pcoq.Symbol.nterm ssrdgens)))
                                                     ((Pcoq.Symbol.nterm ssrintros)))
                                                     (fun ipats dgens eqid
                                                     view loc -> 
# 2054 "plugins/ssr/ssrparser.mlg"
    view, (eqid, (dgens, ipats)) 
                                                                 ))]);
                           Tacentries.arg_tag = Some
                                                (Geninterp.Val.Pair (
                                                (Geninterp.val_tag (Genarg.topwit wit_ssrfwdview)), 
                                                (Geninterp.Val.Pair (
                                                (Geninterp.val_tag (Genarg.topwit wit_ssreqid)), 
                                                (Geninterp.Val.Pair (
                                                (Geninterp.val_tag (Genarg.topwit wit_ssrdgens)), 
                                                (Geninterp.val_tag (Genarg.topwit wit_ssrintros))))))));
                           Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                   (wit_ssrfwdview), 
                                                   (Genarg.PairArg ((wit_ssreqid), 
                                                   (Genarg.PairArg ((wit_ssrdgens), 
                                                   (wit_ssrintros)))))));
                           Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                  (wit_ssrfwdview), (Genarg.PairArg (
                                                                    (wit_ssreqid), 
                                                                    (Genarg.PairArg (
                                                                    (wit_ssrdgens), 
                                                                    (wit_ssrintros)))))));
                           Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                   (wit_ssrfwdview), 
                                                   (Genarg.PairArg ((wit_ssreqid), 
                                                   (Genarg.PairArg ((wit_ssrdgens), 
                                                   (wit_ssrintros)))))));
                           Tacentries.arg_printer = ((fun env sigma -> 
                                                    
# 2052 "plugins/ssr/ssrparser.mlg"
                pr_ssrarg 
                                                    ), (fun env sigma -> 
                                                    
# 2052 "plugins/ssr/ssrparser.mlg"
                pr_ssrarg 
                                                    ), (fun env sigma -> 
                                                    
# 2052 "plugins/ssr/ssrparser.mlg"
                pr_ssrarg 
                                                    ));
                           }
let _ = (wit_ssrarg, ssrarg)

let () = Tacentries.tactic_extend __coq_plugin_name "ssrclear" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("clear", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_natural), 
                                                         Tacentries.TyNil)), 
           (fun n ist -> 
# 2070 "plugins/ssr/ssrparser.mlg"
                                tclIPAT (List.init n (fun _ -> IOpDrop)) 
           )))]


# 2075 "plugins/ssr/ssrparser.mlg"
 

(* TODO: review this, in particular the => _ and => [] cases *)
let rec improper_intros = function
  | IPatSimpl _ :: ipats -> improper_intros ipats
  | (IPatId _ | IPatAnon _ | IPatCase _ | IPatDispatch _) :: _ -> false
  | _ -> true (* FIXME *)

let check_movearg = function
  | view, (eqid, _) when view <> [] && eqid <> None ->
    CErrors.user_err (Pp.str "incompatible view and equation in move tactic")
  | view, (_, (([gen :: _], _), _)) when view <> [] && has_occ gen ->
    CErrors.user_err (Pp.str "incompatible view and occurrence switch in move tactic")
  | _, (_, ((dgens, _), _)) when List.length dgens > 1 ->
    CErrors.user_err (Pp.str "dependents switch `/' in move tactic")
  | _, (eqid, (_, ipats)) when eqid <> None && improper_intros ipats ->
    CErrors.user_err (Pp.str "no proper intro pattern for equation in move tactic")
  | arg -> arg



let (wit_ssrmovearg, ssrmovearg) = Tacentries.argument_extend ~name:"ssrmovearg" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm ssrarg)))
                                                              (fun arg loc ->
                                                              
# 2097 "plugins/ssr/ssrparser.mlg"
                       check_movearg arg 
                                                              ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrarg));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrarg);
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrarg);
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrarg);
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 2096 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrarg 
                                                            ), (fun env sigma -> 
                                                            
# 2096 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrarg 
                                                            ), (fun env sigma -> 
                                                            
# 2096 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrarg 
                                                            ));
                                   }
let _ = (wit_ssrmovearg, ssrmovearg)


# 2100 "plugins/ssr/ssrparser.mlg"
 

let movearg_of_parsed_movearg (v,(eq,(dg,ip))) =
  (v,(eq,(ssrdgens_of_parsed_dgens dg,ip)))



let () = Tacentries.tactic_extend __coq_plugin_name "ssrmove" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("move", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrmovearg), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrrpat), 
                                                        Tacentries.TyNil))), 
           (fun arg pat ist -> 
# 2109 "plugins/ssr/ssrparser.mlg"
    ssrmovetac (movearg_of_parsed_movearg arg) <*> tclIPAT (tclCompileIPats [pat]) 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("move", Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrmovearg), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrclauses), 
                                                       Tacentries.TyNil))), 
          (fun arg clauses ist -> 
# 2111 "plugins/ssr/ssrparser.mlg"
    tclCLAUSES (ssrmovetac (movearg_of_parsed_movearg arg)) clauses 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("move", Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrrpat), 
                                                       Tacentries.TyNil)), 
          (fun pat ist -> 
# 2112 "plugins/ssr/ssrparser.mlg"
                               tclIPAT (tclCompileIPats [pat]) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("move", Tacentries.TyNil), 
          (fun ist -> 
# 2113 "plugins/ssr/ssrparser.mlg"
                  ssrsmovetac 
          )))]


# 2116 "plugins/ssr/ssrparser.mlg"
 

let check_casearg = function
| view, (_, (([_; gen :: _], _), _)) when view <> [] && has_occ gen ->
  CErrors.user_err (Pp.str "incompatible view and occurrence switch in dependent case tactic")
| arg -> arg



let (wit_ssrcasearg, ssrcasearg) = Tacentries.argument_extend ~name:"ssrcasearg" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm ssrarg)))
                                                              (fun arg loc ->
                                                              
# 2126 "plugins/ssr/ssrparser.mlg"
                       check_casearg arg 
                                                              ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrarg));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrarg);
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrarg);
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrarg);
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 2125 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrarg 
                                                            ), (fun env sigma -> 
                                                            
# 2125 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrarg 
                                                            ), (fun env sigma -> 
                                                            
# 2125 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrarg 
                                                            ));
                                   }
let _ = (wit_ssrcasearg, ssrcasearg)

let () = Tacentries.tactic_extend __coq_plugin_name "ssrcase" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("case", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrcasearg), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrclauses), 
                                                        Tacentries.TyNil))), 
           (fun arg clauses ist -> 
# 2131 "plugins/ssr/ssrparser.mlg"
    tclCLAUSES (ssrcasetac (movearg_of_parsed_movearg arg)) clauses 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("case", Tacentries.TyNil), 
          (fun ist -> 
# 2132 "plugins/ssr/ssrparser.mlg"
                  ssrscasetoptac 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrelim" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("elim", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrarg), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrclauses), 
                                                        Tacentries.TyNil))), 
           (fun arg clauses ist -> 
# 2139 "plugins/ssr/ssrparser.mlg"
    tclCLAUSES (ssrelimtac (movearg_of_parsed_movearg arg)) clauses 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("elim", Tacentries.TyNil), 
          (fun ist -> 
# 2140 "plugins/ssr/ssrparser.mlg"
                  ssrselimtoptac 
          )))]


# 2147 "plugins/ssr/ssrparser.mlg"
 

let pr_agen (docc, dt) = pr_docc docc ++ pr_term dt
let pr_ssragen _ _ _ = pr_agen
let pr_ssragens _ _ _ = pr_dgens pr_agen



let (wit_ssragen, ssragen) = Tacentries.argument_extend ~name:"ssragen" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.nterm ssrterm)))
                                                        (fun dt loc -> 
# 2157 "plugins/ssr/ssrparser.mlg"
                       nodocc, dt 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                       ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrhyp)))))
                                                       ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                       ((Pcoq.Symbol.nterm ssrterm)))
                                                       (fun dt _ clr _ loc ->
                                                       
# 2156 "plugins/ssr/ssrparser.mlg"
                                                   mkclr clr, dt 
                                                       ))]);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.Val.Pair (
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssrdocc)), 
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssrterm))));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                     (wit_ssrdocc), (wit_ssrterm)));
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                    (wit_ssrdocc), (wit_ssrterm)));
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                     (wit_ssrdocc), (wit_ssrterm)));
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 2155 "plugins/ssr/ssrparser.mlg"
                                                                  pr_ssragen 
                                                      ), (fun env sigma -> 
                                                      
# 2155 "plugins/ssr/ssrparser.mlg"
                                                                  pr_ssragen 
                                                      ), (fun env sigma -> 
                                                      
# 2155 "plugins/ssr/ssrparser.mlg"
                                                                  pr_ssragen 
                                                      ));
                             }
let _ = (wit_ssragen, ssragen)

let (wit_ssragens, ssragens) = Tacentries.argument_extend ~name:"ssragens" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.stop)
                                                          (fun loc -> 
# 2167 "plugins/ssr/ssrparser.mlg"
           [[]], [] 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm ssrterm)))
                                                         (Pcoq.Symbol.self))
                                                         (fun agens dt loc ->
                                                         
# 2166 "plugins/ssr/ssrparser.mlg"
    cons_gen (nodocc, dt) agens 
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrhyp)))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         (fun _ clr _ loc ->
                                                         
# 2164 "plugins/ssr/ssrparser.mlg"
                                       [[]], clr
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrhyp)))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         ((Pcoq.Symbol.nterm ssrterm)))
                                                         (Pcoq.Symbol.self))
                                                         (fun agens dt _ clr
                                                         _ loc -> 
# 2163 "plugins/ssr/ssrparser.mlg"
    cons_gen (mkclr clr, dt) agens 
                                                                  ))]);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.Val.List 
                                                    (Geninterp.Val.List 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssragen)))), 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrclear))));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                       (Genarg.ListArg 
                                                       (Genarg.ListArg 
                                                       (wit_ssragen))), 
                                                       (wit_ssrclear)));
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                      (Genarg.ListArg 
                                                      (Genarg.ListArg 
                                                      (wit_ssragen))), 
                                                      (wit_ssrclear)));
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                       (Genarg.ListArg 
                                                       (Genarg.ListArg 
                                                       (wit_ssragen))), 
                                                       (wit_ssrclear)));
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 2161 "plugins/ssr/ssrparser.mlg"
             pr_ssragens 
                                                        ), (fun env sigma -> 
                                                        
# 2161 "plugins/ssr/ssrparser.mlg"
             pr_ssragens 
                                                        ), (fun env sigma -> 
                                                        
# 2161 "plugins/ssr/ssrparser.mlg"
             pr_ssragens 
                                                        ));
                               }
let _ = (wit_ssragens, ssragens)


# 2170 "plugins/ssr/ssrparser.mlg"
 

let mk_applyarg views agens intros = views, (agens, intros)

let pr_ssraarg _ _ _ (view, (dgens, ipats)) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view view ++ pr_dgens pr_agen dgens ++ pri ipats



let (wit_ssrapplyarg, ssrapplyarg) = Tacentries.argument_extend ~name:"ssrapplyarg" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ssrbwdview)))
                                                                ((Pcoq.Symbol.nterm ssrclear)))
                                                                ((Pcoq.Symbol.nterm ssrintros)))
                                                                (fun intros
                                                                clr view
                                                                loc -> 
                                                                
# 2192 "plugins/ssr/ssrparser.mlg"
    mk_applyarg view ([], clr) intros 
                                                                ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ssrbwdview)))
                                                               ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                               ((Pcoq.Symbol.nterm ssragen)))
                                                               ((Pcoq.Symbol.nterm ssragens)))
                                                               ((Pcoq.Symbol.nterm ssrintros)))
                                                               (fun intros
                                                               dgens gen _
                                                               view loc -> 
                                                               
# 2190 "plugins/ssr/ssrparser.mlg"
    mk_applyarg view (cons_gen gen dgens) intros 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ssrintros_ne)))
                                                               (fun intros
                                                               loc -> 
                                                               
# 2188 "plugins/ssr/ssrparser.mlg"
    mk_applyarg [] ([], []) intros 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ssrclear_ne)))
                                                               ((Pcoq.Symbol.nterm ssrintros)))
                                                               (fun intros
                                                               clr loc -> 
                                                               
# 2186 "plugins/ssr/ssrparser.mlg"
    mk_applyarg [] ([], clr) intros 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                               ((Pcoq.Symbol.nterm ssragen)))
                                                               ((Pcoq.Symbol.nterm ssragens)))
                                                               ((Pcoq.Symbol.nterm ssrintros)))
                                                               (fun intros
                                                               dgens gen _
                                                               loc -> 
                                                               
# 2184 "plugins/ssr/ssrparser.mlg"
    mk_applyarg [] (cons_gen gen dgens) intros 
                                                               ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.Val.Pair (
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrbwdview)), 
                                                          (Geninterp.Val.Pair (
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssragens)), 
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrintros))))));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                             (wit_ssrbwdview), 
                                                             (Genarg.PairArg (
                                                             (wit_ssragens), 
                                                             (wit_ssrintros)))));
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                            (wit_ssrbwdview), 
                                                            (Genarg.PairArg (
                                                            (wit_ssragens), 
                                                            (wit_ssrintros)))));
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                             (wit_ssrbwdview), 
                                                             (Genarg.PairArg (
                                                             (wit_ssragens), 
                                                             (wit_ssrintros)))));
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 2182 "plugins/ssr/ssrparser.mlg"
             pr_ssraarg 
                                                              ), (fun env sigma -> 
                                                              
# 2182 "plugins/ssr/ssrparser.mlg"
             pr_ssraarg 
                                                              ), (fun env sigma -> 
                                                              
# 2182 "plugins/ssr/ssrparser.mlg"
             pr_ssraarg 
                                                              ));
                                     }
let _ = (wit_ssrapplyarg, ssrapplyarg)

let () = Tacentries.tactic_extend __coq_plugin_name "ssrapply" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("apply", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_ssrapplyarg), 
                                                         Tacentries.TyNil)), 
           (fun arg ist -> 
# 2196 "plugins/ssr/ssrparser.mlg"
                                   
     let views, (gens_clr, intros) = arg in
     inner_ssrapplytac views gens_clr ist <*> tclIPATssr intros 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("apply", Tacentries.TyNil), 
          (fun ist -> 
# 2199 "plugins/ssr/ssrparser.mlg"
                   apply_top_tac 
          )))]


# 2204 "plugins/ssr/ssrparser.mlg"
 

let mk_exactarg views dgens = mk_applyarg views dgens []



let (wit_ssrexactarg, ssrexactarg) = Tacentries.argument_extend ~name:"ssrexactarg" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ssrclear_ne)))
                                                                (fun clr
                                                                loc -> 
                                                                
# 2216 "plugins/ssr/ssrparser.mlg"
    mk_exactarg [] ([], clr) 
                                                                ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ssrbwdview)))
                                                               ((Pcoq.Symbol.nterm ssrclear)))
                                                               (fun clr view
                                                               loc -> 
                                                               
# 2214 "plugins/ssr/ssrparser.mlg"
    mk_exactarg view ([], clr) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                               ((Pcoq.Symbol.nterm ssragen)))
                                                               ((Pcoq.Symbol.nterm ssragens)))
                                                               (fun dgens gen
                                                               _ loc -> 
                                                               
# 2212 "plugins/ssr/ssrparser.mlg"
    mk_exactarg [] (cons_gen gen dgens) 
                                                               ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrapplyarg));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrapplyarg);
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrapplyarg);
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrapplyarg);
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 2210 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssraarg 
                                                              ), (fun env sigma -> 
                                                              
# 2210 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssraarg 
                                                              ), (fun env sigma -> 
                                                              
# 2210 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssraarg 
                                                              ));
                                     }
let _ = (wit_ssrexactarg, ssrexactarg)


# 2219 "plugins/ssr/ssrparser.mlg"
 

let vmexacttac pf =
  Goal.enter begin fun gl ->
  exact_no_check (EConstr.mkCast (pf, vmCast, Tacmach.pf_concl gl))
  end



let () = Tacentries.tactic_extend __coq_plugin_name "ssrexact" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("exact", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_ssrexactarg), 
                                                         Tacentries.TyNil)), 
           (fun arg ist -> 
# 2229 "plugins/ssr/ssrparser.mlg"
                                   
     let views, (gens_clr, _) = arg in
     tclBY (inner_ssrapplytac views gens_clr ist) 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("exact", Tacentries.TyNil), 
          (fun ist -> 
# 2232 "plugins/ssr/ssrparser.mlg"
                  
     Tacticals.tclORELSE (donetac ~-1) (tclBY apply_top_tac) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("exact", Tacentries.TyIdent ("<:", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_lconstr), 
                                                        Tacentries.TyNil))), 
          (fun pf ist -> 
# 2234 "plugins/ssr/ssrparser.mlg"
                                    vmexacttac pf 
          )))]


# 2239 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrcongrarg _ _ _ ((n, f), dgens) =
  (if n <= 0 then mt () else str " " ++ int n) ++
  pr_term f ++ pr_dgens pr_gen dgens



let (wit_ssrcongrarg, ssrcongrarg) = Tacentries.argument_extend ~name:"ssrcongrarg" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm constr)))
                                                                (fun c loc ->
                                                                
# 2252 "plugins/ssr/ssrparser.mlg"
                     (0, mk_term NoFlag c), ([[]],[]) 
                                                                ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm constr)))
                                                               ((Pcoq.Symbol.nterm ssrdgens)))
                                                               (fun dgens c
                                                               loc -> 
                                                               
# 2251 "plugins/ssr/ssrparser.mlg"
                                     (0, mk_term NoFlag c), dgens 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm natural)))
                                                               ((Pcoq.Symbol.nterm constr)))
                                                               (fun c n
                                                               loc -> 
                                                               
# 2250 "plugins/ssr/ssrparser.mlg"
                                (n, mk_term NoFlag c),([[]],[]) 
                                                               ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm natural)))
                                                               ((Pcoq.Symbol.nterm constr)))
                                                               ((Pcoq.Symbol.nterm ssrdgens)))
                                                               (fun dgens c n
                                                               loc -> 
                                                               
# 2249 "plugins/ssr/ssrparser.mlg"
                                                (n, mk_term NoFlag c), dgens 
                                                               ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.Val.Pair (
                                                          (Geninterp.Val.Pair (
                                                          (Geninterp.val_tag (Genarg.topwit wit_int)), 
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrterm)))), 
                                                          (Geninterp.val_tag (Genarg.topwit wit_ssrdgens))));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                             (Genarg.PairArg (
                                                             (wit_int), 
                                                             (wit_ssrterm))), 
                                                             (wit_ssrdgens)));
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                            (Genarg.PairArg (
                                                            (wit_int), 
                                                            (wit_ssrterm))), 
                                                            (wit_ssrdgens)));
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                             (Genarg.PairArg (
                                                             (wit_int), 
                                                             (wit_ssrterm))), 
                                                             (wit_ssrdgens)));
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 2248 "plugins/ssr/ssrparser.mlg"
               pr_ssrcongrarg 
                                                              ), (fun env sigma -> 
                                                              
# 2248 "plugins/ssr/ssrparser.mlg"
               pr_ssrcongrarg 
                                                              ), (fun env sigma -> 
                                                              
# 2248 "plugins/ssr/ssrparser.mlg"
               pr_ssrcongrarg 
                                                              ));
                                     }
let _ = (wit_ssrcongrarg, ssrcongrarg)

let () = Tacentries.tactic_extend __coq_plugin_name "ssrcongr" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("congr", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_ssrcongrarg), 
                                                         Tacentries.TyNil)), 
           (fun arg ist -> 
# 2259 "plugins/ssr/ssrparser.mlg"
  let arg, dgens = arg in
  Proofview.Goal.enter begin fun _ ->
    match dgens with
    | [gens], clr -> Tacticals.tclTHEN (genstac (gens,clr)) (newssrcongrtac arg ist)
    | _ -> errorstrm (str"Dependent family abstractions not allowed in congr")
  end 
           )))]


# 2273 "plugins/ssr/ssrparser.mlg"
 

let pr_rwocc = function
  | None, None -> mt ()
  | None, occ -> pr_occ occ
  | Some clr,  _ ->  pr_clear_ne clr

let pr_ssrrwocc _ _ _ = pr_rwocc



let (wit_ssrrwocc, ssrrwocc) = Tacentries.argument_extend ~name:"ssrrwocc" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.stop)
                                                          (fun loc -> 
# 2287 "plugins/ssr/ssrparser.mlg"
           noclr 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.nterm ssrocc)))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         (fun _ occ _ loc ->
                                                         
# 2286 "plugins/ssr/ssrparser.mlg"
                               mkocc occ 
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ssrhyp))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         (fun _ clr _ loc ->
                                                         
# 2285 "plugins/ssr/ssrparser.mlg"
                                    mkclr clr 
                                                         ))]);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrdocc));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrdocc);
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrdocc);
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrdocc);
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 2284 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrrwocc 
                                                        ), (fun env sigma -> 
                                                        
# 2284 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrrwocc 
                                                        ), (fun env sigma -> 
                                                        
# 2284 "plugins/ssr/ssrparser.mlg"
                                                       pr_ssrrwocc 
                                                        ));
                               }
let _ = (wit_ssrrwocc, ssrrwocc)


# 2292 "plugins/ssr/ssrparser.mlg"
 

let pr_rwkind = function
  | RWred s -> pr_simpl s
  | RWdef -> str "/"
  | RWeq -> mt ()

let wit_ssrrwkind = add_genarg "ssrrwkind" (fun env sigma -> pr_rwkind)

let pr_rule = function
  | RWred s, _ -> pr_simpl s
  | RWdef, r-> str "/" ++ pr_term r
  | RWeq, r -> pr_term r

let pr_ssrrule _ _ _ = pr_rule

let noruleterm loc = mk_term NoFlag (mkCProp loc)



let (wit_ssrrule_ne, ssrrule_ne) = Tacentries.argument_extend ~name:"ssrrule_ne" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            []);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.Pair (
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrrwkind)), 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrterm))));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                           (wit_ssrrwkind), 
                                                           (wit_ssrterm)));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                          (wit_ssrrwkind), 
                                                          (wit_ssrterm)));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                           (wit_ssrrwkind), 
                                                           (wit_ssrterm)));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 2312 "plugins/ssr/ssrparser.mlg"
                                                                       pr_ssrrule 
                                                            ), (fun env sigma -> 
                                                            
# 2312 "plugins/ssr/ssrparser.mlg"
                                                                       pr_ssrrule 
                                                            ), (fun env sigma -> 
                                                            
# 2312 "plugins/ssr/ssrparser.mlg"
                                                                       pr_ssrrule 
                                                            ));
                                   }
let _ = (wit_ssrrule_ne, ssrrule_ne)

let _ = let () =
        Pcoq.grammar_extend ssrrule_ne
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.stop)
                                            ((Pcoq.Symbol.nterm ssrsimpl_ne)))
                            (fun s loc -> 
# 2323 "plugins/ssr/ssrparser.mlg"
                           RWred s, noruleterm (Some loc) 
                                          );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm test_not_ssrslashnum)))
                                           ((Pcoq.Symbol.rules [Pcoq.Rules.make 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ssrsimpl_ne)))
                                                               (fun s loc ->
                                                               
# 2321 "plugins/ssr/ssrparser.mlg"
                               RWred s, noruleterm (Some loc) 
                                                               );
                                                               Pcoq.Rules.make 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.nterm ssrterm)))
                                                               (fun t loc ->
                                                               
# 2320 "plugins/ssr/ssrparser.mlg"
                           RWeq, t 
                                                               );
                                                               Pcoq.Rules.make 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                                               ((Pcoq.Symbol.nterm ssrterm)))
                                                               (fun t _
                                                               loc -> 
                                                               
# 2319 "plugins/ssr/ssrparser.mlg"
                                RWdef, t 
                                                               )])))
                           (fun x _ loc -> 
# 2322 "plugins/ssr/ssrparser.mlg"
               x 
                                           )]))
        in ()

let (wit_ssrrule, ssrrule) = Tacentries.argument_extend ~name:"ssrrule" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                      [(Pcoq.Production.make
                                                        (Pcoq.Rule.stop)
                                                        (fun loc -> 
# 2329 "plugins/ssr/ssrparser.mlg"
             RWred Nop, noruleterm (Some loc) 
                                                                    ));
                                                      (Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.nterm ssrrule_ne)))
                                                       (fun r loc -> 
# 2328 "plugins/ssr/ssrparser.mlg"
                           r 
                                                                    ))]);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.val_tag (Genarg.topwit wit_ssrrule_ne));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrrule_ne);
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrrule_ne);
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrrule_ne);
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 2327 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssrrule 
                                                      ), (fun env sigma -> 
                                                      
# 2327 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssrrule 
                                                      ), (fun env sigma -> 
                                                      
# 2327 "plugins/ssr/ssrparser.mlg"
                                                         pr_ssrrule 
                                                      ));
                             }
let _ = (wit_ssrrule, ssrrule)


# 2334 "plugins/ssr/ssrparser.mlg"
 

let pr_option f = function None -> mt() | Some x -> f x
let pr_pattern_squarep= pr_option (fun r -> str "[" ++ pr_rpattern r ++ str "]")
let pr_ssrpattern_squarep _ _ _ = pr_pattern_squarep
let pr_rwarg ((d, m), ((docc, rx), r)) =
  pr_rwdir d ++ pr_mult m ++ pr_rwocc docc ++ pr_pattern_squarep rx ++ pr_rule r

let pr_ssrrwarg _ _ _ = pr_rwarg



let (wit_ssrpattern_squarep, ssrpattern_squarep) = Tacentries.argument_extend ~name:"ssrpattern_squarep" 
                                                   {
                                                   Tacentries.arg_parsing = 
                                                   Vernacextend.Arg_rules (
                                                   [(Pcoq.Production.make
                                                     (Pcoq.Rule.stop)
                                                     (fun loc -> 
# 2349 "plugins/ssr/ssrparser.mlg"
             None 
                                                                 ));
                                                   (Pcoq.Production.make
                                                    (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                                    ((Pcoq.Symbol.nterm rpattern)))
                                                                    ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                    (fun _ rdx _ loc -> 
# 2348 "plugins/ssr/ssrparser.mlg"
                                   Some rdx 
                                                                    ))]);
                                                   Tacentries.arg_tag = 
                                                   Some
                                                   (Geninterp.Val.Opt 
                                                   (Geninterp.val_tag (Genarg.topwit wit_rpattern)));
                                                   Tacentries.arg_intern = 
                                                   Tacentries.ArgInternWit (Genarg.OptArg 
                                                   (wit_rpattern));
                                                   Tacentries.arg_subst = 
                                                   Tacentries.ArgSubstWit (Genarg.OptArg 
                                                   (wit_rpattern));
                                                   Tacentries.arg_interp = 
                                                   Tacentries.ArgInterpWit (Genarg.OptArg 
                                                   (wit_rpattern));
                                                   Tacentries.arg_printer = 
                                                   ((fun env sigma -> 
                                                   
# 2347 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrpattern_squarep 
                                                   ), (fun env sigma -> 
                                                   
# 2347 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrpattern_squarep 
                                                   ), (fun env sigma -> 
                                                   
# 2347 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrpattern_squarep 
                                                   ));
                                                   }
let _ = (wit_ssrpattern_squarep, ssrpattern_squarep)

let (wit_ssrpattern_ne_squarep, ssrpattern_ne_squarep) = Tacentries.argument_extend ~name:"ssrpattern_ne_squarep" 
                                                         {
                                                         Tacentries.arg_parsing = 
                                                         Vernacextend.Arg_rules (
                                                         [(Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (CLexer.terminal "["))))
                                                           ((Pcoq.Symbol.nterm rpattern)))
                                                           ((Pcoq.Symbol.token (CLexer.terminal "]"))))
                                                           (fun _ rdx _
                                                           loc -> 
# 2354 "plugins/ssr/ssrparser.mlg"
                                   Some rdx 
                                                                  ))]);
                                                         Tacentries.arg_tag = 
                                                         Some
                                                         (Geninterp.Val.Opt 
                                                         (Geninterp.val_tag (Genarg.topwit wit_rpattern)));
                                                         Tacentries.arg_intern = 
                                                         Tacentries.ArgInternWit (Genarg.OptArg 
                                                         (wit_rpattern));
                                                         Tacentries.arg_subst = 
                                                         Tacentries.ArgSubstWit (Genarg.OptArg 
                                                         (wit_rpattern));
                                                         Tacentries.arg_interp = 
                                                         Tacentries.ArgInterpWit (Genarg.OptArg 
                                                         (wit_rpattern));
                                                         Tacentries.arg_printer = 
                                                         ((fun env sigma -> 
                                                         
# 2353 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrpattern_squarep 
                                                         ), (fun env sigma -> 
                                                         
# 2353 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrpattern_squarep 
                                                         ), (fun env sigma -> 
                                                         
# 2353 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrpattern_squarep 
                                                         ));
                                                         }
let _ = (wit_ssrpattern_ne_squarep, ssrpattern_ne_squarep)

let (wit_ssrrwarg, ssrrwarg) = Tacentries.argument_extend ~name:"ssrrwarg" 
                               {
                               Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                        [(Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.nterm ssrrule_ne)))
                                                          (fun r loc -> 
# 2378 "plugins/ssr/ssrparser.mlg"
      mk_rwarg norwmult norwocc r 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm ssrpattern_ne_squarep)))
                                                         ((Pcoq.Symbol.nterm ssrrule_ne)))
                                                         (fun r rx loc -> 
# 2376 "plugins/ssr/ssrparser.mlg"
      mk_rwarg norwmult (noclr, rx) r 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         ((Pcoq.Symbol.nterm ssrpattern_squarep)))
                                                         ((Pcoq.Symbol.nterm ssrrule_ne)))
                                                         (fun r rx _ _ loc ->
                                                         
# 2374 "plugins/ssr/ssrparser.mlg"
      mk_rwarg norwmult (nodocc, rx) r 
                                                         ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.nterm ssrocc)))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         ((Pcoq.Symbol.nterm ssrpattern_squarep)))
                                                         ((Pcoq.Symbol.nterm ssrrule_ne)))
                                                         (fun r rx _ occ _
                                                         loc -> 
# 2372 "plugins/ssr/ssrparser.mlg"
      mk_rwarg norwmult (mkocc occ, rx) r 
                                                                ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrhyp)))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         ((Pcoq.Symbol.nterm ssrrule)))
                                                         (fun r _ clr _
                                                         loc -> 
# 2370 "plugins/ssr/ssrparser.mlg"
      mk_rwarg norwmult (mkclr clr, None) r 
                                                                ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                         ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrhyp)))))
                                                         ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                         ((Pcoq.Symbol.nterm ssrpattern_ne_squarep)))
                                                         ((Pcoq.Symbol.nterm ssrrule_ne)))
                                                         (fun r rx _ clr _
                                                         loc -> 
# 2368 "plugins/ssr/ssrparser.mlg"
      mk_rwarg norwmult (mkclr clr, rx) r 
                                                                ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm ssrmult_ne)))
                                                         ((Pcoq.Symbol.nterm ssrrwocc)))
                                                         ((Pcoq.Symbol.nterm ssrpattern_squarep)))
                                                         ((Pcoq.Symbol.nterm ssrrule_ne)))
                                                         (fun r rx docc m
                                                         loc -> 
# 2366 "plugins/ssr/ssrparser.mlg"
      mk_rwarg (L2R, m) (docc, rx) r 
                                                                ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "-/"))))
                                                         ((Pcoq.Symbol.nterm ssrterm)))
                                                         (fun t _ loc -> 
# 2364 "plugins/ssr/ssrparser.mlg"
      mk_rwarg (R2L, nomult) norwocc (RWdef, t) 
                                                                    ));
                                                        (Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.token (CLexer.terminal "-"))))
                                                         ((Pcoq.Symbol.nterm ssrmult)))
                                                         ((Pcoq.Symbol.nterm ssrrwocc)))
                                                         ((Pcoq.Symbol.nterm ssrpattern_squarep)))
                                                         ((Pcoq.Symbol.nterm ssrrule_ne)))
                                                         (fun r rx docc m _
                                                         loc -> 
# 2362 "plugins/ssr/ssrparser.mlg"
      mk_rwarg (R2L, m) (docc, rx) r 
                                                                ))]);
                               Tacentries.arg_tag = Some
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrdir)), 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrmult)))), 
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.Val.Pair (
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrdocc)), 
                                                    (Geninterp.Val.Opt 
                                                    (Geninterp.val_tag (Genarg.topwit wit_rpattern))))), 
                                                    (Geninterp.val_tag (Genarg.topwit wit_ssrrule))))));
                               Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (wit_ssrdir), 
                                                       (wit_ssrmult))), 
                                                       (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (wit_ssrdocc), 
                                                       (Genarg.OptArg 
                                                       (wit_rpattern)))), 
                                                       (wit_ssrrule)))));
                               Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                      (Genarg.PairArg (
                                                      (wit_ssrdir), (wit_ssrmult))), 
                                                      (Genarg.PairArg (
                                                      (Genarg.PairArg (
                                                      (wit_ssrdocc), 
                                                      (Genarg.OptArg 
                                                      (wit_rpattern)))), 
                                                      (wit_ssrrule)))));
                               Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (wit_ssrdir), 
                                                       (wit_ssrmult))), 
                                                       (Genarg.PairArg (
                                                       (Genarg.PairArg (
                                                       (wit_ssrdocc), 
                                                       (Genarg.OptArg 
                                                       (wit_rpattern)))), 
                                                       (wit_ssrrule)))));
                               Tacentries.arg_printer = ((fun env sigma -> 
                                                        
# 2360 "plugins/ssr/ssrparser.mlg"
               pr_ssrrwarg 
                                                        ), (fun env sigma -> 
                                                        
# 2360 "plugins/ssr/ssrparser.mlg"
               pr_ssrrwarg 
                                                        ), (fun env sigma -> 
                                                        
# 2360 "plugins/ssr/ssrparser.mlg"
               pr_ssrrwarg 
                                                        ));
                               }
let _ = (wit_ssrrwarg, ssrrwarg)

let () = Tacentries.tactic_extend __coq_plugin_name "ssrinstofruleL2R" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ssrinstancesofruleL2R", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ssrterm), 
                            Tacentries.TyNil)), (fun arg ist -> 
# 2382 "plugins/ssr/ssrparser.mlg"
                                                ssrinstancesofrule ist L2R arg 
                                                )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrinstofruleR2L" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ssrinstancesofruleR2L", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ssrterm), 
                            Tacentries.TyNil)), (fun arg ist -> 
# 2385 "plugins/ssr/ssrparser.mlg"
                                                ssrinstancesofrule ist R2L arg 
                                                )))]


# 2392 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrrwargs _ _ _ rwargs = pr_list spc pr_rwarg rwargs



let (wit_ssrrwargs, ssrrwargs) = Tacentries.argument_extend ~name:"ssrrwargs" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                          []);
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.Val.List 
                                                      (Geninterp.val_tag (Genarg.topwit wit_ssrrwarg)));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                         (wit_ssrrwarg));
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                        (wit_ssrrwarg));
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                         (wit_ssrrwarg));
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 2398 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssrrwargs 
                                                          ), (fun env sigma -> 
                                                          
# 2398 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssrrwargs 
                                                          ), (fun env sigma -> 
                                                          
# 2398 "plugins/ssr/ssrparser.mlg"
                                                              pr_ssrrwargs 
                                                          ));
                                 }
let _ = (wit_ssrrwargs, ssrrwargs)


# 2401 "plugins/ssr/ssrparser.mlg"
 

let ssr_rw_syntax = Summary.ref ~name:"SSR:rewrite" true

let () =
  Goptions.(declare_bool_option
    { optkey   = ["SsrRewrite"];
      optread  = (fun _ -> !ssr_rw_syntax);
      optdepr  = false;
      optwrite = (fun b -> ssr_rw_syntax := b) })

let lbrace = Char.chr 123
(** Workaround to a limitation of coqpp *)

let test_ssr_rw_syntax =
  let test strm =
    if not !ssr_rw_syntax then raise Stream.Failure else
    if is_ssr_loaded () then () else
    match LStream.peek_nth 0 strm with
    | Tok.KEYWORD key when List.mem key.[0] [lbrace; '['; '/'] -> ()
    | _ -> raise Stream.Failure in
  Pcoq.Entry.(of_parser "test_ssr_rw_syntax" { parser_fun = test })



let _ = let () =
        Pcoq.grammar_extend ssrrwargs
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm test_ssr_rw_syntax)))
                                            ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ssrrwarg)))))
                            (fun a _ loc -> 
# 2428 "plugins/ssr/ssrparser.mlg"
                                                                a 
                                            )]))
        in ()

let () = Tacentries.tactic_extend __coq_plugin_name "ssrrewrite" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("rewrite", Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrrwargs), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrclauses), 
                                                           Tacentries.TyNil))), 
           (fun args clauses ist -> 
# 2435 "plugins/ssr/ssrparser.mlg"
      tclCLAUSES (ssrrewritetac ist args) clauses 
           )))]


# 2440 "plugins/ssr/ssrparser.mlg"
 

let pr_unlockarg (occ, t) = pr_occ occ ++ pr_term t
let pr_ssrunlockarg _ _ _ = pr_unlockarg



let (wit_ssrunlockarg, ssrunlockarg) = Tacentries.argument_extend ~name:"ssrunlockarg" 
                                       {
                                       Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                                [(Pcoq.Production.make
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ssrterm)))
                                                                  (fun t
                                                                  loc -> 
                                                                  
# 2450 "plugins/ssr/ssrparser.mlg"
                         None, t 
                                                                  ));
                                                                (Pcoq.Production.make
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (CLexer.terminal "{"))))
                                                                 ((Pcoq.Symbol.nterm ssrocc)))
                                                                 ((Pcoq.Symbol.token (CLexer.terminal "}"))))
                                                                 ((Pcoq.Symbol.nterm ssrterm)))
                                                                 (fun t _ occ
                                                                 _ loc -> 
                                                                 
# 2449 "plugins/ssr/ssrparser.mlg"
                                             occ, t 
                                                                 ))]);
                                       Tacentries.arg_tag = Some
                                                            (Geninterp.Val.Pair (
                                                            (Geninterp.val_tag (Genarg.topwit wit_ssrocc)), 
                                                            (Geninterp.val_tag (Genarg.topwit wit_ssrterm))));
                                       Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                               (wit_ssrocc), 
                                                               (wit_ssrterm)));
                                       Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                              (wit_ssrocc), 
                                                              (wit_ssrterm)));
                                       Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                               (wit_ssrocc), 
                                                               (wit_ssrterm)));
                                       Tacentries.arg_printer = ((fun env sigma -> 
                                                                
# 2448 "plugins/ssr/ssrparser.mlg"
               pr_ssrunlockarg 
                                                                ), (fun env sigma -> 
                                                                
# 2448 "plugins/ssr/ssrparser.mlg"
               pr_ssrunlockarg 
                                                                ), (fun env sigma -> 
                                                                
# 2448 "plugins/ssr/ssrparser.mlg"
               pr_ssrunlockarg 
                                                                ));
                                       }
let _ = (wit_ssrunlockarg, ssrunlockarg)


# 2453 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrunlockargs _ _ _ args = pr_list spc pr_unlockarg args



let (wit_ssrunlockargs, ssrunlockargs) = Tacentries.argument_extend ~name:"ssrunlockargs" 
                                         {
                                         Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                                  [(Pcoq.Production.make
                                                                    (Pcoq.Rule.next 
                                                                    (Pcoq.Rule.stop)
                                                                    ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ssrunlockarg))))
                                                                    (fun args
                                                                    loc -> 
                                                                    
# 2461 "plugins/ssr/ssrparser.mlg"
                                      args 
                                                                    ))]);
                                         Tacentries.arg_tag = Some
                                                              (Geninterp.Val.List 
                                                              (Geninterp.val_tag (Genarg.topwit wit_ssrunlockarg)));
                                         Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.ListArg 
                                                                 (wit_ssrunlockarg));
                                         Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.ListArg 
                                                                (wit_ssrunlockarg));
                                         Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.ListArg 
                                                                 (wit_ssrunlockarg));
                                         Tacentries.arg_printer = ((fun env sigma -> 
                                                                  
# 2460 "plugins/ssr/ssrparser.mlg"
               pr_ssrunlockargs 
                                                                  ), (fun env sigma -> 
                                                                  
# 2460 "plugins/ssr/ssrparser.mlg"
               pr_ssrunlockargs 
                                                                  ), (fun env sigma -> 
                                                                  
# 2460 "plugins/ssr/ssrparser.mlg"
               pr_ssrunlockargs 
                                                                  ));
                                         }
let _ = (wit_ssrunlockargs, ssrunlockargs)

let () = Tacentries.tactic_extend __coq_plugin_name "ssrunlock" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("unlock", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_ssrunlockargs), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_ssrclauses), 
                                                          Tacentries.TyNil))), 
           (fun args clauses ist -> 
# 2466 "plugins/ssr/ssrparser.mlg"
      tclCLAUSES (unlocktac ist args) clauses 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrpose" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("pose", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrfixfwd), 
                                                        Tacentries.TyNil)), 
           (fun ffwd ist -> 
# 2473 "plugins/ssr/ssrparser.mlg"
                                  ssrposetac ffwd 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("pose", Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrcofixfwd), 
                                                       Tacentries.TyNil)), 
          (fun ffwd ist -> 
# 2474 "plugins/ssr/ssrparser.mlg"
                                    ssrposetac ffwd 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("pose", Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrfwdid), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrposefwd), 
                                                       Tacentries.TyNil))), 
          (fun id fwd ist -> 
# 2475 "plugins/ssr/ssrparser.mlg"
                                               ssrposetac (id, fwd) 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrset" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("set", Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrfwdid), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrsetfwd), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrclauses), 
                                                       Tacentries.TyNil)))), 
           (fun id fwd clauses ist -> 
# 2484 "plugins/ssr/ssrparser.mlg"
    tclCLAUSES (ssrsettac id fwd) clauses 
           )))]

let _ = let () =
        Pcoq.grammar_extend ltac_expr
        (Pcoq.Reuse (Some
        ("3"), [Pcoq.Production.make
                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                ("abstract"))))))
                                ((Pcoq.Symbol.nterm ssrdgens)))
                (fun gens _ loc -> 
# 2499 "plugins/ssr/ssrparser.mlg"
                 CAst.make ~loc (TacML (
                     ssrtac_entry "abstract", [Tacexpr.TacGeneric (None, Genarg.in_gen (Genarg.rawwit wit_ssrdgens) gens)]))
                 
                                   )]))
        in ()

let () = Tacentries.tactic_extend __coq_plugin_name "ssrabstract" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("abstract", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_ssrdgens), 
                                                            Tacentries.TyNil)), 
           (fun gens ist -> 
# 2504 "plugins/ssr/ssrparser.mlg"
                                    
    if List.length (fst gens) <> 1 then
      errorstrm (str"dependents switches '/' not allowed here");
    Ssripats.ssrabstract (ssrdgens_of_parsed_dgens gens) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrhave" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("have", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhavefwdwbinders), 
                                                        Tacentries.TyNil)), 
           (fun fwd ist -> 
# 2512 "plugins/ssr/ssrparser.mlg"
    havetac ist fwd false false 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrhavesuff" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("have", Tacentries.TyIdent ("suff", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhavefwd), 
                                                        Tacentries.TyNil)))), 
           (fun pats fwd ist -> 
# 2517 "plugins/ssr/ssrparser.mlg"
    havetac ist (false,(pats,fwd)) true false 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrhavesuffices" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("have", Tacentries.TyIdent ("suffices", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhavefwd), 
                                                        Tacentries.TyNil)))), 
           (fun pats fwd ist -> 
# 2522 "plugins/ssr/ssrparser.mlg"
    havetac ist (false,(pats,fwd)) true false 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrsuffhave" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("suff", Tacentries.TyIdent ("have", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhavefwd), 
                                                        Tacentries.TyNil)))), 
           (fun pats fwd ist -> 
# 2527 "plugins/ssr/ssrparser.mlg"
    havetac ist (false,(pats,fwd)) true true 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrsufficeshave" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("suffices", Tacentries.TyIdent ("have", 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                            Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_ssrhavefwd), 
                                                            Tacentries.TyNil)))), 
           (fun pats fwd ist -> 
# 2532 "plugins/ssr/ssrparser.mlg"
    havetac ist (false,(pats,fwd)) true true 
           )))]


# 2537 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrsufffwdwbinders env sigma _ _ prt (hpats, (fwd, hint)) =
  pr_hpats hpats ++ pr_fwd fwd ++ pr_hint env sigma prt hint



let (wit_ssrsufffwd, ssrsufffwd) = Tacentries.argument_extend ~name:"ssrsufffwd" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm ssrhpats)))
                                                              ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ssrbinder))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                              ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                              ((Pcoq.Symbol.nterm ssrhint)))
                                                              (fun hint t _
                                                              bs pats loc ->
                                                              
# 2547 "plugins/ssr/ssrparser.mlg"
    let ((clr, pats), binders), simpl = pats in
    let allbs = intro_id_to_binder binders @ bs in
    let allbinders = binders @ List.flatten (binder_to_intro_id bs) in
    let fwd = mkFwdHint ":" t in
    (((clr, pats), allbinders), simpl), (bind_fwd allbs fwd, hint) 
                                                              ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.Pair (
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrhpats)), 
                                                        (Geninterp.Val.Pair (
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrfwd)), 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrhint))))));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                           (wit_ssrhpats), 
                                                           (Genarg.PairArg (
                                                           (wit_ssrfwd), 
                                                           (wit_ssrhint)))));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                          (wit_ssrhpats), 
                                                          (Genarg.PairArg (
                                                          (wit_ssrfwd), 
                                                          (wit_ssrhint)))));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                           (wit_ssrhpats), 
                                                           (Genarg.PairArg (
                                                           (wit_ssrfwd), 
                                                           (wit_ssrhint)))));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 2545 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrsufffwdwbinders env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 2545 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrsufffwdwbinders env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 2545 "plugins/ssr/ssrparser.mlg"
                                                        pr_ssrsufffwdwbinders env sigma 
                                                            ));
                                   }
let _ = (wit_ssrsufffwd, ssrsufffwd)

let () = Tacentries.tactic_extend __coq_plugin_name "ssrsuff" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("suff", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrsufffwd), 
                                                        Tacentries.TyNil)), 
           (fun fwd ist -> 
# 2556 "plugins/ssr/ssrparser.mlg"
                                  sufftac ist fwd 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrsuffices" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("suffices", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_ssrsufffwd), 
                                                            Tacentries.TyNil)), 
           (fun fwd ist -> 
# 2560 "plugins/ssr/ssrparser.mlg"
                                      sufftac ist fwd 
           )))]


# 2567 "plugins/ssr/ssrparser.mlg"
 

let pr_ssrwlogfwd _ _ _ (gens, t) =
  str ":" ++ pr_list mt pr_wgen gens ++ spc() ++ pr_fwd t



let (wit_ssrwlogfwd, ssrwlogfwd) = Tacentries.argument_extend ~name:"ssrwlogfwd" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal ":"))))
                                                              ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ssrwgen))))
                                                              ((Pcoq.Symbol.token (CLexer.terminal "/"))))
                                                              ((Pcoq.Symbol.nterm ast_closure_lterm)))
                                                              (fun t _ gens _
                                                              loc -> 
                                                              
# 2576 "plugins/ssr/ssrparser.mlg"
                                                           gens, mkFwdHint "/" t
                                                              ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.Pair (
                                                        (Geninterp.Val.List 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrwgen))), 
                                                        (Geninterp.val_tag (Genarg.topwit wit_ssrfwd))));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                           (Genarg.ListArg 
                                                           (wit_ssrwgen)), 
                                                           (wit_ssrfwd)));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                          (Genarg.ListArg 
                                                          (wit_ssrwgen)), 
                                                          (wit_ssrfwd)));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                           (Genarg.ListArg 
                                                           (wit_ssrwgen)), 
                                                           (wit_ssrfwd)));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 2575 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrwlogfwd 
                                                            ), (fun env sigma -> 
                                                            
# 2575 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrwlogfwd 
                                                            ), (fun env sigma -> 
                                                            
# 2575 "plugins/ssr/ssrparser.mlg"
                                      pr_ssrwlogfwd 
                                                            ));
                                   }
let _ = (wit_ssrwlogfwd, ssrwlogfwd)

let () = Tacentries.tactic_extend __coq_plugin_name "ssrwlog" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wlog", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrwlogfwd), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhint), 
                                                        Tacentries.TyNil)))), 
           (fun pats fwd hint ist -> 
# 2582 "plugins/ssr/ssrparser.mlg"
    wlogtac ist pats fwd hint false `NoGen 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrwlogs" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wlog", Tacentries.TyIdent ("suff", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrwlogfwd), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhint), 
                                                        Tacentries.TyNil))))), 
           (fun pats fwd hint ist -> 
# 2587 "plugins/ssr/ssrparser.mlg"
    wlogtac ist pats fwd hint true `NoGen 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrwlogss" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("wlog", Tacentries.TyIdent ("suffices", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrwlogfwd), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhint), 
                                                        Tacentries.TyNil))))), 
           (fun pats fwd hint ist -> 
# 2592 "plugins/ssr/ssrparser.mlg"
    wlogtac ist pats fwd hint true `NoGen 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrwithoutloss" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("without", Tacentries.TyIdent ("loss", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrwlogfwd), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrhint), 
                                                           Tacentries.TyNil))))), 
           (fun pats fwd hint ist -> 
# 2597 "plugins/ssr/ssrparser.mlg"
    wlogtac ist pats fwd hint false `NoGen 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrwithoutlosss" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("without", Tacentries.TyIdent ("loss", 
                                                           Tacentries.TyIdent ("suff", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrwlogfwd), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrhint), 
                                                           Tacentries.TyNil)))))), 
           (fun pats fwd hint ist -> 
# 2603 "plugins/ssr/ssrparser.mlg"
    wlogtac ist pats fwd hint true `NoGen 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrwithoutlossss" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("without", Tacentries.TyIdent ("loss", 
                                                           Tacentries.TyIdent ("suffices", 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrwlogfwd), 
                                                           Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_ssrhint), 
                                                           Tacentries.TyNil)))))), 
           (fun pats fwd hint ist -> 
# 2609 "plugins/ssr/ssrparser.mlg"
    wlogtac ist pats fwd hint true `NoGen 
           )))]


# 2612 "plugins/ssr/ssrparser.mlg"
 

(* Generally have *)
let pr_idcomma _ _ _ = function
  | None -> mt()
  | Some None -> str"_, "
  | Some (Some id) -> pr_id id ++ str", "



let (wit_ssr_idcomma, ssr_idcomma) = Tacentries.argument_extend ~name:"ssr_idcomma" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.stop)
                                                                (fun loc -> 
# 2623 "plugins/ssr/ssrparser.mlg"
             None 
                                                                    ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.Val.Opt 
                                                          (Geninterp.Val.Opt 
                                                          (Geninterp.val_tag (Genarg.topwit wit_ident))));
                                     Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.OptArg 
                                                             (Genarg.OptArg 
                                                             (wit_ident)));
                                     Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.OptArg 
                                                            (Genarg.OptArg 
                                                            (wit_ident)));
                                     Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.OptArg 
                                                             (Genarg.OptArg 
                                                             (wit_ident)));
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 2622 "plugins/ssr/ssrparser.mlg"
                                                                      pr_idcomma 
                                                              ), (fun env sigma -> 
                                                              
# 2622 "plugins/ssr/ssrparser.mlg"
                                                                      pr_idcomma 
                                                              ), (fun env sigma -> 
                                                              
# 2622 "plugins/ssr/ssrparser.mlg"
                                                                      pr_idcomma 
                                                              ));
                                     }
let _ = (wit_ssr_idcomma, ssr_idcomma)


# 2626 "plugins/ssr/ssrparser.mlg"
 

let test_idcomma =
  let open Pcoq.Lookahead in
  to_entry "test_idcomma" begin
    (lk_ident <+> lk_kw "_") >> lk_kw ","
  end



let _ = let () =
        Pcoq.grammar_extend ssr_idcomma
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm test_idcomma)))
                                                            ((Pcoq.Symbol.rules 
                                                            [Pcoq.Rules.make 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                                            (fun _ loc -> 
                                                            
# 2639 "plugins/ssr/ssrparser.mlg"
                                                               None 
                                                            );
                                                            Pcoq.Rules.make 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                            (fun id loc -> 
                                                            
# 2639 "plugins/ssr/ssrparser.mlg"
                           Some (Id.of_string id) 
                                                            )])))
                                            ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                            (fun _ ip _ loc -> 
# 2640 "plugins/ssr/ssrparser.mlg"
      Some ip 
                                               )]))
        in ()


# 2644 "plugins/ssr/ssrparser.mlg"
 

let augment_preclr clr1 (((clr0, x),y),z) =
  let cl = match clr0 with
    | None -> if clr1 = [] then None else Some clr1
    | Some clr0 -> Some (clr1 @ clr0) in
  (((cl, x),y),z)



let () = Tacentries.tactic_extend __coq_plugin_name "ssrgenhave" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("gen", Tacentries.TyIdent ("have", 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrclear), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssr_idcomma), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrwlogfwd), 
                                                       Tacentries.TyArg (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ssrhint), 
                                                       Tacentries.TyNil))))))), 
           (fun clr id pats fwd hint ist -> 
# 2657 "plugins/ssr/ssrparser.mlg"
    let pats = augment_preclr clr pats in
    wlogtac ist pats fwd hint false (`Gen id) 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ssrgenhave2" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("generally", Tacentries.TyIdent ("have", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_ssrclear), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_ssr_idcomma), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_ssrhpats_nobs), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_ssrwlogfwd), 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_ssrhint), 
                                                             Tacentries.TyNil))))))), 
           (fun clr id pats fwd hint ist -> 
# 2664 "plugins/ssr/ssrparser.mlg"
    let pats = augment_preclr clr pats in
    wlogtac ist pats fwd hint false (`Gen id) 
           )))]


# 2668 "plugins/ssr/ssrparser.mlg"
 

let check_under_arg ((_dir,mult),((_occ,_rpattern),_rule)) =
  if mult <> nomult then
    CErrors.user_err Pp.(str"under does not support multipliers")



let () = Tacentries.tactic_extend __coq_plugin_name "under" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("under", Tacentries.TyArg (
                                                         Extend.TUentry (Genarg.get_arg_tag wit_ssrrwarg), 
                                                         Tacentries.TyNil)), 
           (fun arg ist -> 
# 2678 "plugins/ssr/ssrparser.mlg"
                                  
    check_under_arg arg;
    Ssrfwd.undertac ist None arg nohint
    
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("under", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrrwarg), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrintros_ne), 
                                                        Tacentries.TyNil))), 
          (fun arg ipats ist -> 
# 2682 "plugins/ssr/ssrparser.mlg"
                                                      
    check_under_arg arg;
    Ssrfwd.undertac ist (Some ipats) arg nohint
    
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("under", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrrwarg), 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrintros_ne), 
                                                        Tacentries.TyIdent ("do", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhint3arg), 
                                                        Tacentries.TyNil))))), 
          (fun arg ipats h ist -> 
# 2686 "plugins/ssr/ssrparser.mlg"
                                                                          
    check_under_arg arg;
    Ssrfwd.undertac ist (Some ipats) arg h
    
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("under", Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrrwarg), 
                                                        Tacentries.TyIdent ("do", 
                                                        Tacentries.TyArg (
                                                        Extend.TUentry (Genarg.get_arg_tag wit_ssrhint3arg), 
                                                        Tacentries.TyNil)))), 
          (fun arg h ist -> 
# 2690 "plugins/ssr/ssrparser.mlg"
                                                       (* implicit "=> [*|*]" *)
    check_under_arg arg;
    Ssrfwd.undertac ~pad_intro:true ist (Some [IPatAnon All]) arg h
    
          )))]


# 2696 "plugins/ssr/ssrparser.mlg"
 

(* We wipe out all the keywords generated by the grammar rules we defined. *)
(* The user is supposed to Require Import ssreflect or Require ssreflect   *)
(* and Import ssreflect.SsrSyntax to obtain these keywords and as a         *)
(* consequence the extended ssreflect grammar.                             *)
let () = CLexer.set_keyword_state frozen_lexer ;;



