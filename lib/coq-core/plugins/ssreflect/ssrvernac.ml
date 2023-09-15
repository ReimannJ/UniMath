
# 13 "plugins/ssr/ssrvernac.mlg"
 

open Names
module CoqConstr = Constr
open CoqConstr
open Constrexpr
open Constrexpr_ops
open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pvernac.Vernac_
open Ltac_plugin
open Glob_term
open Stdarg
open Pp
open Ppconstr
open Printer
open Util
open Ssrprinters
open Ssrcommon



let __coq_plugin_name = "coq-core.plugins.ssreflect"
let _ = Mltop.add_known_module __coq_plugin_name

# 38 "plugins/ssr/ssrvernac.mlg"
 

(* Defining grammar rules with "xx" in it automatically declares keywords too,
 * we thus save the lexer to restore it at the end of the file *)
let frozen_lexer = CLexer.get_keyword_state () ;;

(* global syntactic changes and vernacular commands *)

(** Alternative notations for "match" and anonymous arguments. *)(* ************)

(* Syntax:                                                        *)
(*  if <term> is <pattern> then ... else ...                      *)
(*  if <term> is <pattern> [in ..] return ... then ... else ...   *)
(*  let: <pattern> := <term> in ...                               *)
(*  let: <pattern> [in ...] := <term> return ... in ...           *)
(* The scope of a top-level 'as' in the pattern extends over the  *)
(* 'return' type (dependent if/let).                              *)
(* Note that the optional "in ..." appears next to the <pattern>  *)
(* rather than the <term> in then "let:" syntax. The alternative  *)
(* would lead to ambiguities in, e.g.,                            *)
(* let: p1 := (*v---INNER LET:---v *)                             *)
(*   let: p2 := let: p3 := e3 in k return t in k2 in k1 return t' *)
(* in b       (*^--ALTERNATIVE INNER LET--------^ *)              *)

(* Caveat : There is no pretty-printing support, since this would *)
(* require a modification to the Coq kernel (adding a new match   *)
(* display style -- why aren't these strings?); also, the v8.1    *)
(* pretty-printer only allows extension hooks for printing        *)
(* integer or string literals.                                    *)
(*   Also note that in the v8 grammar "is" needs to be a keyword; *)
(* as this can't be done from an ML extension file, the new       *)
(* syntax will only work when ssreflect.v is imported.            *)

let no_ct = None, None and no_rt = None
let aliasvar = function
  | [[{ CAst.v = CPatAlias (_, na); loc }]] -> Some na
  | _ -> None
let mk_cnotype mp = aliasvar mp, None
let mk_ctype mp t = aliasvar mp, Some t
let mk_rtype t = Some t
let mk_dthen ?loc (mp, ct, rt) c = (CAst.make ?loc (mp, c)), ct, rt
let mk_let ?loc rt ct mp c1 =
  CAst.make ?loc @@ CCases (LetPatternStyle, rt, ct, [CAst.make ?loc (mp, c1)])
let mk_pat c (na, t) = (c, na, t)



let _ = let ssr_rtype = Pcoq.Entry.make "ssr_rtype"
        and ssr_mpat = Pcoq.Entry.make "ssr_mpat"
        and ssr_dpat = Pcoq.Entry.make "ssr_dpat"
        and ssr_dthen = Pcoq.Entry.make "ssr_dthen"
        and ssr_elsepat = Pcoq.Entry.make "ssr_elsepat"
        and ssr_else = Pcoq.Entry.make "ssr_else"
        in
        let () = assert (Pcoq.Entry.is_empty ssr_rtype) in
        let () =
        Pcoq.grammar_extend ssr_rtype
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("return")))))
                                                  ((Pcoq.Symbol.nterml term ("100"))))
                                  (fun t _ loc -> 
# 87 "plugins/ssr/ssrvernac.mlg"
                                                    mk_rtype t 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty ssr_mpat) in
        let () =
        Pcoq.grammar_extend ssr_mpat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm pattern)))
                                  (fun p loc -> 
# 88 "plugins/ssr/ssrvernac.mlg"
                                [[p]] 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty ssr_dpat) in
        let () =
        Pcoq.grammar_extend ssr_dpat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ssr_mpat)))
                                  (fun mp loc -> 
# 92 "plugins/ssr/ssrvernac.mlg"
                         mp, no_ct, no_rt 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ssr_mpat)))
                                                 ((Pcoq.Symbol.nterm ssr_rtype)))
                                 (fun rt mp loc -> 
# 91 "plugins/ssr/ssrvernac.mlg"
                                         mp, mk_cnotype mp, rt 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ssr_mpat)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                                 ((Pcoq.Symbol.nterm pattern)))
                                                 ((Pcoq.Symbol.nterm ssr_rtype)))
                                 (fun rt t _ mp loc -> 
# 90 "plugins/ssr/ssrvernac.mlg"
                                                            mp, mk_ctype mp t, rt 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty ssr_dthen) in
        let () =
        Pcoq.grammar_extend ssr_dthen
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ssr_dpat)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("then")))))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun c _ dp loc -> 
# 94 "plugins/ssr/ssrvernac.mlg"
                                                        mk_dthen ~loc dp c 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty ssr_elsepat) in
        let () =
        Pcoq.grammar_extend ssr_elsepat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("else")))))
                                  (fun _ loc -> 
# 95 "plugins/ssr/ssrvernac.mlg"
                              [[CAst.make ~loc @@ CPatAtom None]] 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty ssr_else) in
        let () =
        Pcoq.grammar_extend ssr_else
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ssr_elsepat)))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun c mp loc -> 
# 96 "plugins/ssr/ssrvernac.mlg"
                                                  CAst.make ~loc (mp, c) 
                                                   )])]))
        in let () =
        Pcoq.grammar_extend binder_constr
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("let")))))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                            ((Pcoq.Symbol.nterm ssr_mpat)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                            ((Pcoq.Symbol.nterm pattern)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                            ((Pcoq.Symbol.nterm lconstr)))
                                                            ((Pcoq.Symbol.nterm ssr_rtype)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                            ((Pcoq.Symbol.nterm lconstr)))
                            (fun c1 _ rt c _ t _ mp _ _ loc -> 
# 114 "plugins/ssr/ssrvernac.mlg"
        mk_let ~loc rt [mk_pat c (mk_ctype mp t)] mp c1 
                                                               );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("let")))))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                           ((Pcoq.Symbol.nterm ssr_mpat)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                           ((Pcoq.Symbol.nterm lconstr)))
                                                           ((Pcoq.Symbol.nterm ssr_rtype)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                           ((Pcoq.Symbol.nterm lconstr)))
                           (fun c1 _ rt c _ mp _ _ loc -> 
# 111 "plugins/ssr/ssrvernac.mlg"
        mk_let ~loc rt [mk_pat c (mk_cnotype mp)] mp c1 
                                                          );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("let")))))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                           ((Pcoq.Symbol.nterm ssr_mpat)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                           ((Pcoq.Symbol.nterm lconstr)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                           ((Pcoq.Symbol.nterm lconstr)))
                           (fun c1 _ c _ mp _ _ loc -> 
# 108 "plugins/ssr/ssrvernac.mlg"
        mk_let ~loc no_rt [mk_pat c no_ct] mp c1 
                                                       );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("if")))))
                                                           ((Pcoq.Symbol.nterml term ("200"))))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("isn't")))))
                                                           ((Pcoq.Symbol.nterm ssr_dthen)))
                                           ((Pcoq.Symbol.nterm ssr_else)))
                           (fun b2 db1 _ c _ loc -> 
# 101 "plugins/ssr/ssrvernac.mlg"
        let b1, ct, rt = db1 in
      let b1, b2 = let open CAst in
        let {loc=l1; v=(p1, r1)}, {loc=l2; v=(p2, r2)} = b1, b2 in
        (make ?loc:l1 (p1, r2), make ?loc:l2 (p2, r1))
      in
      CAst.make ~loc @@ CCases (MatchStyle, rt, [mk_pat c ct], [b1; b2]) 
                                                    );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("if")))))
                                                           ((Pcoq.Symbol.nterml term ("200"))))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("is")))))
                                                           ((Pcoq.Symbol.nterm ssr_dthen)))
                                           ((Pcoq.Symbol.nterm ssr_else)))
                           (fun b2 db1 _ c _ loc -> 
# 99 "plugins/ssr/ssrvernac.mlg"
        let b1, ct, rt = db1 in CAst.make ~loc @@ CCases (MatchStyle, rt, [mk_pat c ct], [b1; b2]) 
                                                    )]))
        in ()

let _ = let () =
        Pcoq.grammar_extend closed_binder
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.rules 
                                                            [Pcoq.Rules.make 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("&")))))
                                                            (fun _ loc -> 
                                                            
# 121 "plugins/ssr/ssrvernac.mlg"
                                 () 
                                                            );
                                                            Pcoq.Rules.make 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("of")))))
                                                            (fun _ loc -> 
                                                            
# 121 "plugins/ssr/ssrvernac.mlg"
                 () 
                                                            )])))
                                            ((Pcoq.Symbol.nterml term ("99"))))
                            (fun c _ loc -> 
# 122 "plugins/ssr/ssrvernac.mlg"
        [CLocalAssum ([CAst.make ~loc Anonymous], Default Explicit, c)] 
                                            )]))
        in ()


# 140 "plugins/ssr/ssrvernac.mlg"
 

let declare_one_prenex_implicit locality f =
  let fref =
    try Smartlocate.global_with_alias f
    with _ -> errorstrm (pr_qualid f ++ str " is not declared") in
  let rec loop = function
  | a :: args' when Impargs.is_status_implicit a ->
    MaxImplicit :: loop args'
  | args' when List.exists Impargs.is_status_implicit args' ->
      errorstrm (str "Expected prenex implicits for " ++ pr_qualid f)
  | _ -> [] in
  let impls =
    match Impargs.implicits_of_global fref  with
    | [cond,impls] -> impls
    | [] -> errorstrm (str "Expected some implicits for " ++ pr_qualid f)
    | _ -> errorstrm (str "Multiple implicits not supported") in
  match loop impls  with
  | [] ->
    errorstrm (str "Expected some implicits for " ++ pr_qualid f)
  | impls ->
    Impargs.set_implicits locality fref [List.map (fun imp -> (Anonymous,imp)) impls]



let () = Vernacextend.vernac_extend ~command:"Ssrpreneximplicits" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Prenex", 
                                     Vernacextend.TyTerminal ("Implicits", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_global)), 
                                     Vernacextend.TyNil))), (let coqpp_body fl
                                                            locality = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 167 "plugins/ssr/ssrvernac.mlg"
      
         let locality = Locality.make_section_locality locality in
         List.iter (declare_one_prenex_implicit locality) fl;
     
                                                            ) in fun fl
                                                            ?loc ~atts ()
                                                            -> coqpp_body fl
                                                            (Attributes.parse Attributes.locality atts)), None))]

let _ = let () =
        Pcoq.grammar_extend gallina_ext
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Import"))))))
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Prenex"))))))
                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                            ("Implicits"))))))
                            (fun _ _ _ loc -> 
# 179 "plugins/ssr/ssrvernac.mlg"
        Vernacexpr.VernacSetOption (false, ["Printing"; "Implicit"; "Defensive"], Vernacexpr.OptionUnset) 
                                              )]))
        in ()


# 192 "plugins/ssr/ssrvernac.mlg"
 

let pr_raw_ssrhintref env sigma prc _ _ = let open CAst in function
  | { v = CAppExpl ((r,x), args) } when isCHoles args ->
    prc env sigma (CAst.make @@ CRef (r,x)) ++ str "|" ++ int (List.length args)
  | { v = CApp ({ v = CRef _ }, _) } as c -> prc env sigma c
  | { v = CApp (c, args) } when isCxHoles args ->
    prc env sigma c ++ str "|" ++ int (List.length args)
  | c -> prc env sigma c

let pr_rawhintref env sigma c =
  match DAst.get c with
  | GApp (f, args) when isRHoles args ->
    pr_glob_constr_env env sigma f ++ str "|" ++ int (List.length args)
  | _ -> pr_glob_constr_env env sigma c

let pr_glob_ssrhintref env sigma _ _ _ (c, _) = pr_rawhintref env sigma c

let pr_ssrhintref env sigma prc _ _ = prc env sigma

let mkhintref ?loc c n = match c.CAst.v with
  | CRef (r,x) -> CAst.make ?loc @@ CAppExpl ((r, x), mkCHoles ?loc n)
  | _ -> mkAppC (c, mkCHoles ?loc n)



let (wit_ssrhintref, ssrhintref) = Tacentries.argument_extend ~name:"ssrhintref" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.nterm constr)))
                                                              ((Pcoq.Symbol.token (CLexer.terminal "|"))))
                                                              ((Pcoq.Symbol.nterm natural)))
                                                              (fun n _ c
                                                              loc -> 
                                                              
# 224 "plugins/ssr/ssrvernac.mlg"
                                       mkhintref ~loc c n  
                                                              ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.nterm constr)))
                                                             (fun c loc -> 
# 223 "plugins/ssr/ssrvernac.mlg"
                        c  
                                                                    ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.val_tag (Genarg.topwit wit_constr));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (wit_constr);
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_constr);
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_constr);
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 221 "plugins/ssr/ssrvernac.mlg"
                   pr_raw_ssrhintref env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 222 "plugins/ssr/ssrvernac.mlg"
                    pr_glob_ssrhintref env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 220 "plugins/ssr/ssrvernac.mlg"
               pr_ssrhintref env sigma 
                                                            ));
                                   }
let _ = (wit_ssrhintref, ssrhintref)


# 227 "plugins/ssr/ssrvernac.mlg"
 

(* View purpose *)

let pr_viewpos = function
  | Some Ssrview.AdaptorDb.Forward -> str " for move/"
  | Some Ssrview.AdaptorDb.Backward -> str " for apply/"
  | Some Ssrview.AdaptorDb.Equivalence -> str " for apply//"
  | None -> mt ()

let pr_ssrviewpos _ _ _ = pr_viewpos



let (wit_ssrviewpos, ssrviewpos) = Tacentries.argument_extend ~name:"ssrviewpos" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.stop)
                                                              (fun loc -> 
# 246 "plugins/ssr/ssrvernac.mlg"
              None  
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "for"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "apply"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "//"))))
                                                             (fun _ _ _
                                                             loc -> 
# 245 "plugins/ssr/ssrvernac.mlg"
                                 Some Ssrview.AdaptorDb.Equivalence  
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "for"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "apply"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "/"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "/"))))
                                                             (fun _ _ _ _
                                                             loc -> 
# 244 "plugins/ssr/ssrvernac.mlg"
                                    Some Ssrview.AdaptorDb.Equivalence  
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "for"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "apply"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "/"))))
                                                             (fun _ _ _
                                                             loc -> 
# 243 "plugins/ssr/ssrvernac.mlg"
                                Some Ssrview.AdaptorDb.Backward  
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "for"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "move"))))
                                                             ((Pcoq.Symbol.token (CLexer.terminal "/"))))
                                                             (fun _ _ _
                                                             loc -> 
# 242 "plugins/ssr/ssrvernac.mlg"
                               Some Ssrview.AdaptorDb.Forward  
                                                                    ))]);
                                   Tacentries.arg_tag = None;
                                   Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                   Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                   Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 241 "plugins/ssr/ssrvernac.mlg"
                                        pr_ssrviewpos 
                                                            ), (fun env sigma -> 
                                                            
# 241 "plugins/ssr/ssrvernac.mlg"
                                        pr_ssrviewpos 
                                                            ), (fun env sigma -> 
                                                            
# 241 "plugins/ssr/ssrvernac.mlg"
                                        pr_ssrviewpos 
                                                            ));
                                   }
let _ = (wit_ssrviewpos, ssrviewpos)


# 249 "plugins/ssr/ssrvernac.mlg"
 

let pr_ssrviewposspc _ _ _ i = pr_viewpos i ++ spc ()



let (wit_ssrviewposspc, ssrviewposspc) = Tacentries.argument_extend ~name:"ssrviewposspc" 
                                         {
                                         Tacentries.arg_parsing = Vernacextend.Arg_alias (ssrviewpos);
                                         Tacentries.arg_tag = Some
                                                              (Geninterp.val_tag (Genarg.topwit wit_ssrviewpos));
                                         Tacentries.arg_intern = Tacentries.ArgInternWit (wit_ssrviewpos);
                                         Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_ssrviewpos);
                                         Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_ssrviewpos);
                                         Tacentries.arg_printer = ((fun env sigma -> 
                                                                  
# 255 "plugins/ssr/ssrvernac.mlg"
                                                               pr_ssrviewposspc 
                                                                  ), (fun env sigma -> 
                                                                  
# 255 "plugins/ssr/ssrvernac.mlg"
                                                               pr_ssrviewposspc 
                                                                  ), (fun env sigma -> 
                                                                  
# 255 "plugins/ssr/ssrvernac.mlg"
                                                               pr_ssrviewposspc 
                                                                  ));
                                         }
let _ = (wit_ssrviewposspc, ssrviewposspc)


# 259 "plugins/ssr/ssrvernac.mlg"
 

let print_view_hints env sigma kind l =
  let pp_viewname = str "Hint View" ++ pr_viewpos (Some kind) ++ str " " in
  let pp_hints = pr_list spc (pr_rawhintref env sigma) l in
  Feedback.msg_notice  (pp_viewname ++ hov 0 pp_hints ++ Pp.cut ())



let () = Vernacextend.vernac_extend ~command:"PrintView" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                     Vernacextend.TyTerminal ("Hint", 
                                     Vernacextend.TyTerminal ("View", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ssrviewpos), 
                                     Vernacextend.TyNil)))), (let coqpp_body i
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 270 "plugins/ssr/ssrvernac.mlg"
   
    let env = Global.env () in
    let sigma = Evd.from_env env in
    (match i with
    | Some k ->
      print_view_hints env sigma k (Ssrview.AdaptorDb.get k)
    | None ->
        List.iter (fun k -> print_view_hints env sigma k (Ssrview.AdaptorDb.get k))
          [ Ssrview.AdaptorDb.Forward;
            Ssrview.AdaptorDb.Backward;
            Ssrview.AdaptorDb.Equivalence ])
  
                                                                  ) in fun i
                                                             ?loc ~atts ()
                                                             -> coqpp_body i
                                                             (Attributes.unsupported_attributes atts)), None))]


# 284 "plugins/ssr/ssrvernac.mlg"
 

let glob_view_hints lvh =
  List.map (Constrintern.intern_constr (Global.env ()) (Evd.from_env (Global.env ()))) lvh



let () = Vernacextend.vernac_extend ~command:"HintView" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Hint", 
                                     Vernacextend.TyTerminal ("View", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ssrviewposspc), 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_ssrhintref)), 
                                     Vernacextend.TyNil)))), (let coqpp_body n
                                                             lvh
                                                             () = Vernacextend.vtdefault (fun () -> 
                                                                  
# 293 "plugins/ssr/ssrvernac.mlg"
       let hints = glob_view_hints lvh in
       match n with
       | None ->
          Ssrview.AdaptorDb.declare Ssrview.AdaptorDb.Forward hints;
          Ssrview.AdaptorDb.declare Ssrview.AdaptorDb.Backward hints
       | Some k ->
          Ssrview.AdaptorDb.declare k hints 
                                                                  ) in fun n
                                                             lvh
                                                             ?loc ~atts ()
                                                             -> coqpp_body n
                                                             lvh
                                                             (Attributes.unsupported_attributes atts)), None))]


# 304 "plugins/ssr/ssrvernac.mlg"
 

open G_vernac


let _ = let () =
        Pcoq.grammar_extend query_command
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Search"))))))
                                                            ((Pcoq.Symbol.nterm search_query)))
                                                            ((Pcoq.Symbol.nterm search_queries)))
                                            ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                            (fun _ l s _ loc -> 
# 314 "plugins/ssr/ssrvernac.mlg"
            let (sl,m) = l in
            fun g ->
              Vernacexpr.VernacSearch (Vernacexpr.Search (s::sl),g, m) 
                                                )]))
        in ()


# 335 "plugins/ssr/ssrvernac.mlg"
 

open Pltac



let _ = let () =
        Pcoq.grammar_extend hypident
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("value"))))))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("of")))))
                                                            ((Pcoq.Symbol.nterm Prim.identref)))
                                            ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                            (fun _ id _ _ _ loc -> 
# 345 "plugins/ssr/ssrvernac.mlg"
                                                           id, Locus.InHypValueOnly 
                                                   );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("type"))))))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("of")))))
                                                           ((Pcoq.Symbol.nterm Prim.identref)))
                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                           (fun _ id _ _ _ loc -> 
# 344 "plugins/ssr/ssrvernac.mlg"
                                                          id, Locus.InHypTypeOnly 
                                                  )]))
        in ()

let _ = let () =
        Pcoq.grammar_extend constr_eval
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("type"))))))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("of")))))
                                            ((Pcoq.Symbol.nterm Constr.constr)))
                            (fun c _ _ loc -> 
# 352 "plugins/ssr/ssrvernac.mlg"
                                                 Genredexpr.ConstrTypeOf c 
                                              )]))
        in ()


# 360 "plugins/ssr/ssrvernac.mlg"
 

let () = CLexer.set_keyword_state frozen_lexer ;;



