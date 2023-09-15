let __coq_plugin_name = "coq-core.plugins.ltac"
let _ = Mltop.add_known_module __coq_plugin_name

# 13 "plugins/ltac/g_ltac.mlg"
 

open Util
open Pp
open Constrexpr
open Tacexpr
open Namegen
open Genarg
open Genredexpr
open Names
open Attributes

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pvernac.Vernac_
open Pltac

let fail_default_value = Locus.ArgArg 0

let arg_of_expr = function
    { CAst.v=(TacArg v) } -> v
  | e -> Tacexp (e:raw_tactic_expr)

let genarg_of_unit () = in_gen (rawwit Stdarg.wit_unit) ()
let genarg_of_int n = in_gen (rawwit Stdarg.wit_int) n
let genarg_of_ipattern pat = in_gen (rawwit Tacarg.wit_simple_intropattern) pat
let genarg_of_uconstr c = in_gen (rawwit Stdarg.wit_uconstr) c
let in_tac tac = in_gen (rawwit Tacarg.wit_ltac) tac

let reference_to_id qid =
  if Libnames.qualid_is_ident qid then
    CAst.make ?loc:qid.CAst.loc @@ Libnames.qualid_basename qid
  else
    CErrors.user_err ?loc:qid.CAst.loc
      (str "This expression should be a simple identifier.")

let tactic_mode = Entry.create "tactic_command"

let new_entry name =
  let e = Entry.create name in
  e

let toplevel_selector = new_entry "toplevel_selector"
let tacdef_body = new_entry "tacdef_body"

(* Registers [tactic_mode] as a parser for proof editing *)
let classic_proof_mode = Pvernac.register_proof_mode "Classic" tactic_mode

(* Hack to parse "[ id" without dropping [ *)
let test_bracket_ident =
  let open Pcoq.Lookahead in
  to_entry "test_bracket_ident" begin
    lk_kw "[" >> lk_ident
  end

(* Tactics grammar rules *)

let hint = G_proofs.hint



let _ = let tactic_then_last = Pcoq.Entry.make "tactic_then_last"
        and for_each_goal = Pcoq.Entry.make "for_each_goal"
        and tactic_then_locality = Pcoq.Entry.make "tactic_then_locality"
        and failkw = Pcoq.Entry.make "failkw"
        and tactic_arg = Pcoq.Entry.make "tactic_arg"
        and fresh_id = Pcoq.Entry.make "fresh_id"
        and tactic_atom = Pcoq.Entry.make "tactic_atom"
        and match_key = Pcoq.Entry.make "match_key"
        and input_fun = Pcoq.Entry.make "input_fun"
        and let_clause = Pcoq.Entry.make "let_clause"
        and match_pattern = Pcoq.Entry.make "match_pattern"
        and match_hyp = Pcoq.Entry.make "match_hyp"
        and match_context_rule = Pcoq.Entry.make "match_context_rule"
        and match_context_list = Pcoq.Entry.make "match_context_list"
        and match_rule = Pcoq.Entry.make "match_rule"
        and match_list = Pcoq.Entry.make "match_list"
        and message_token = Pcoq.Entry.make "message_token"
        and ltac_def_kind = Pcoq.Entry.make "ltac_def_kind"
        and range_selector = Pcoq.Entry.make "range_selector"
        and range_selector_or_nth = Pcoq.Entry.make "range_selector_or_nth"
        and selector = Pcoq.Entry.make "selector"
        in
        let () = assert (Pcoq.Entry.is_empty tactic_then_last) in
        let () =
        Pcoq.grammar_extend tactic_then_last
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 83 "plugins/ltac/g_ltac.mlg"
             [||] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ltac_expr))) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun lta _ loc -> 
# 82 "plugins/ltac/g_ltac.mlg"
          Array.map (function None -> CAst.make ~loc (TacId []) | Some t -> t) (Array.of_list lta) 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty for_each_goal) in
        let () =
        Pcoq.grammar_extend for_each_goal
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 92 "plugins/ltac/g_ltac.mlg"
             ([CAst.make ~loc (TacId [])], None) 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.nterm for_each_goal)))
                                 (fun tg _ loc -> 
# 91 "plugins/ltac/g_ltac.mlg"
                                     let (first,last) = tg in (CAst.make ~loc (TacId []) :: first, last) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun ta loc -> 
# 90 "plugins/ltac/g_ltac.mlg"
                            ([ta], None) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("..")))))
                                                 ((Pcoq.Symbol.nterm tactic_then_last)))
                                 (fun l _ loc -> 
# 89 "plugins/ltac/g_ltac.mlg"
                                        ([], Some (CAst.make ~loc (TacId []), l)) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("..")))))
                                                 ((Pcoq.Symbol.nterm tactic_then_last)))
                                 (fun l _ ta loc -> 
# 88 "plugins/ltac/g_ltac.mlg"
                                                        ([], Some (ta, l)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.nterm for_each_goal)))
                                 (fun tg _ ta loc -> 
# 87 "plugins/ltac/g_ltac.mlg"
                                                     let (first,last) = tg in (ta::first, last) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty tactic_then_locality)
        in
        let () =
        Pcoq.grammar_extend tactic_then_locality
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.token (Tok.PKEYWORD (">"))))))
                                  (fun l _ loc -> 
# 97 "plugins/ltac/g_ltac.mlg"
                            if Option.is_empty l then true else false 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty ltac_expr) in
        let () =
        Pcoq.grammar_extend ltac_expr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(Some ("5"), Some (Gramlib.Gramext.RightA),
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm binder_tactic)))
                                  (fun te loc -> 
# 101 "plugins/ltac/g_ltac.mlg"
                                te 
                                                 )]);
                                (Some ("4"), Some (Gramlib.Gramext.LeftA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                                 ((Pcoq.Symbol.nterm tactic_then_locality)))
                                                                 ((Pcoq.Symbol.nterm for_each_goal)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ tg l _ ta0 loc -> 
# 105 "plugins/ltac/g_ltac.mlg"
                                                                                    
          let (first,tail) = tg in
          match l , tail with
          | false , Some (t,last) -> CAst.make ~loc (TacThen (ta0,
              CAst.make ~loc (TacExtendTac (Array.of_list first, t, last))))
          | true  , Some (t,last) -> CAst.make ~loc (TacThens3parts (ta0, Array.of_list first, t, last))
          | false , None -> CAst.make ~loc (TacThen (ta0, CAst.make ~loc (TacDispatch first)))
          | true  , None -> CAst.make ~loc (TacThens (ta0,first)) 
                                                          );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta1 _ ta0 loc -> 
# 104 "plugins/ltac/g_ltac.mlg"
                                                   CAst.make ~loc (TacThen (ta0,ta1)) 
                                                      );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                ((Pcoq.Symbol.nterm binder_tactic)))
                                (fun ta1 _ ta0 loc -> 
# 103 "plugins/ltac/g_ltac.mlg"
                                                       CAst.make ~loc (TacThen (ta0, ta1)) 
                                                      )]);
                                (Some ("3"), Some (Gramlib.Gramext.RightA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("only"))))))
                                                                 ((Pcoq.Symbol.nterm selector)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun ta _ sel _ loc -> 
# 126 "plugins/ltac/g_ltac.mlg"
                                                               CAst.make ~loc (TacSelect (sel, ta)) 
                                                        );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("abstract"))))))
                                                                (Pcoq.Symbol.next))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("using")))))
                                                ((Pcoq.Symbol.nterm ident)))
                                (fun s _ tc _ loc -> 
# 125 "plugins/ltac/g_ltac.mlg"
          CAst.make ~loc (TacAbstract (tc,Some s)) 
                                                     );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("abstract"))))))
                                                (Pcoq.Symbol.next))
                                (fun tc _ loc -> 
# 123 "plugins/ltac/g_ltac.mlg"
                                         CAst.make ~loc (TacAbstract (tc,None)) 
                                                 );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("exactly_once"))))))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta _ loc -> 
# 121 "plugins/ltac/g_ltac.mlg"
                                                  CAst.make ~loc (TacExactlyOnce ta) 
                                                 );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("once"))))))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta _ loc -> 
# 120 "plugins/ltac/g_ltac.mlg"
                                          CAst.make ~loc (TacOnce  ta) 
                                                 );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("progress"))))))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta _ loc -> 
# 119 "plugins/ltac/g_ltac.mlg"
                                              CAst.make ~loc (TacProgress ta) 
                                                 );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("repeat"))))))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta _ loc -> 
# 118 "plugins/ltac/g_ltac.mlg"
                                            CAst.make ~loc (TacRepeat ta) 
                                                 );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("time"))))))
                                                                ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm string))))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta s _ loc -> 
# 117 "plugins/ltac/g_ltac.mlg"
                                                          CAst.make ~loc (TacTime (s,ta)) 
                                                   );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("timeout"))))))
                                                                ((Pcoq.Symbol.nterm nat_or_var)))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta n _ loc -> 
# 116 "plugins/ltac/g_ltac.mlg"
                                                             CAst.make ~loc (TacTimeout (n,ta)) 
                                                   );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("do"))))))
                                                                ((Pcoq.Symbol.nterm nat_or_var)))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta n _ loc -> 
# 115 "plugins/ltac/g_ltac.mlg"
                                                        CAst.make ~loc (TacDo (n,ta)) 
                                                   );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("try"))))))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta _ loc -> 
# 114 "plugins/ltac/g_ltac.mlg"
                                         CAst.make ~loc (TacTry ta) 
                                                 )]);
                                (Some ("2"), Some (Gramlib.Gramext.RightA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("||")))))
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun ta1 _ ta0 loc -> 
# 135 "plugins/ltac/g_ltac.mlg"
                                                    CAst.make ~loc (TacOrelse (ta0,ta1)) 
                                                       );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("||")))))
                                                ((Pcoq.Symbol.nterm binder_tactic)))
                                (fun ta1 _ ta0 loc -> 
# 134 "plugins/ltac/g_ltac.mlg"
                                                        CAst.make ~loc (TacOrelse (ta0,ta1)) 
                                                      );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("tryif"))))))
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("then")))))
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("else")))))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun tae _ tat _ ta _ loc -> 
# 133 "plugins/ltac/g_ltac.mlg"
                                            CAst.make ~loc (TacIfThenCatch (ta,tat,tae)) 
                                                             );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                (fun ta1 _ ta0 loc -> 
# 130 "plugins/ltac/g_ltac.mlg"
                                                   CAst.make ~loc (TacOr (ta0,ta1)) 
                                                      );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                                ((Pcoq.Symbol.nterm binder_tactic)))
                                (fun ta1 _ ta0 loc -> 
# 129 "plugins/ltac/g_ltac.mlg"
                                                       CAst.make ~loc (TacOr (ta0,ta1)) 
                                                      )]);
                                (Some ("1"), Some (Gramlib.Gramext.RightA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm reference)))
                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm tactic_arg))))
                                 (fun la r loc -> 
# 154 "plugins/ltac/g_ltac.mlg"
          CAst.make ~loc @@ TacArg (TacCall (CAst.make ~loc (r,la))) 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm tactic_value)))
                                (fun a loc -> 
# 152 "plugins/ltac/g_ltac.mlg"
                              CAst.make ~loc (TacArg a) 
                                              );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm simple_tactic)))
                                (fun st loc -> 
# 151 "plugins/ltac/g_ltac.mlg"
                                st 
                                               );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm failkw)))
                                                                ((Pcoq.Symbol.rules 
                                                                [Pcoq.Rules.make 
                                                                (Pcoq.Rule.stop)
                                                                (fun loc -> 
                                                                
# 149 "plugins/ltac/g_ltac.mlg"
                                                       fail_default_value 
                                                                );
                                                                Pcoq.Rules.make 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm nat_or_var)))
                                                                (fun n loc ->
                                                                
# 149 "plugins/ltac/g_ltac.mlg"
                                            n 
                                                                )])))
                                                ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm message_token))))
                                (fun l n g loc -> 
# 150 "plugins/ltac/g_ltac.mlg"
                                       CAst.make ~loc (TacFail (g,n,l)) 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("idtac"))))))
                                                ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm message_token))))
                                (fun l _ loc -> 
# 148 "plugins/ltac/g_ltac.mlg"
                                                    CAst.make ~loc (TacId l) 
                                                );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("solve"))))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm ltac_expr)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                (fun _ l _ _ loc -> 
# 147 "plugins/ltac/g_ltac.mlg"
            CAst.make ~loc (TacSolve l) 
                                                    );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("first"))))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm ltac_expr)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                (fun _ l _ _ loc -> 
# 145 "plugins/ltac/g_ltac.mlg"
            CAst.make ~loc (TacFirst l) 
                                                    );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm match_key)))
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                                ((Pcoq.Symbol.nterm match_list)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("end")))))
                                (fun _ mrl _ c b loc -> 
# 143 "plugins/ltac/g_ltac.mlg"
            CAst.make ~loc (TacMatch (b,c,mrl)) 
                                                        );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm match_key)))
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("reverse"))))))
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("goal"))))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                                ((Pcoq.Symbol.nterm match_context_list)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("end")))))
                                (fun _ mrl _ _ _ b loc -> 
# 141 "plugins/ltac/g_ltac.mlg"
            CAst.make ~loc (TacMatchGoal (b,true,mrl)) 
                                                          );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm match_key)))
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("goal"))))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                                ((Pcoq.Symbol.nterm match_context_list)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("end")))))
                                (fun _ mrl _ _ b loc -> 
# 138 "plugins/ltac/g_ltac.mlg"
            CAst.make ~loc (TacMatchGoal (b,false,mrl)) 
                                                        )]);
                                (Some ("0"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm tactic_atom)))
                                 (fun a loc -> 
# 163 "plugins/ltac/g_ltac.mlg"
                             CAst.make ~loc (TacArg a) 
                                               );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (">")))))
                                                                ((Pcoq.Symbol.nterm for_each_goal)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                (fun _ tg _ _ loc -> 
# 157 "plugins/ltac/g_ltac.mlg"
                                              
          let (tf,tail) = tg in
          begin match tail with
          | Some (t,tl) -> CAst.make ~loc (TacExtendTac (Array.of_list tf,t,tl))
          | None -> CAst.make ~loc (TacDispatch tf)
          end 
                                                     );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                ((Pcoq.Symbol.nterm ltac_expr)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ a _ loc -> 
# 156 "plugins/ltac/g_ltac.mlg"
                                     a 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty failkw) in
        let () =
        Pcoq.grammar_extend failkw
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("gfail"))))))
                                  (fun _ loc -> 
# 166 "plugins/ltac/g_ltac.mlg"
                                                        TacGlobal 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("fail"))))))
                                 (fun _ loc -> 
# 166 "plugins/ltac/g_ltac.mlg"
                        TacLocal 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty binder_tactic) in
        let () =
        Pcoq.grammar_extend binder_tactic
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, Some (Gramlib.Gramext.RightA),
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("let")))))
                                                                  ((Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.stop)
                                                                  (fun loc ->
                                                                  
# 173 "plugins/ltac/g_ltac.mlg"
                                                       false 
                                                                  );
                                                                  Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("rec"))))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 173 "plugins/ltac/g_ltac.mlg"
                                         true 
                                                                  )])))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm let_clause)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                  ((Pcoq.Symbol.nterml ltac_expr ("5"))))
                                  (fun body _ llc isrec _ loc -> 
# 175 "plugins/ltac/g_ltac.mlg"
                                          CAst.make ~loc (TacLetIn (isrec,llc,body)) 
                                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("fun")))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm input_fun)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                 ((Pcoq.Symbol.nterml ltac_expr ("5"))))
                                 (fun body _ it _ loc -> 
# 172 "plugins/ltac/g_ltac.mlg"
            CAst.make ~loc (TacFun (it,body)) 
                                                         )])]))
        in let () = assert (Pcoq.Entry.is_empty tactic_arg) in
        let () =
        Pcoq.grammar_extend tactic_arg
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("()")))))
                                  (fun _ loc -> 
# 182 "plugins/ltac/g_ltac.mlg"
                  TacGeneric (None, genarg_of_unit ()) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Constr.constr)))
                                 (fun c loc -> 
# 180 "plugins/ltac/g_ltac.mlg"
                               (match c with { CAst.v = CRef (r,None) } -> Reference r | c -> ConstrMayEval (ConstrTerm c)) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm tactic_value)))
                                 (fun a loc -> 
# 179 "plugins/ltac/g_ltac.mlg"
                              a 
                                               )])]))
        in let () =
        Pcoq.grammar_extend tactic_value
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.stop)
                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                            ("numgoals"))))))
                            (fun _ loc -> 
# 189 "plugins/ltac/g_ltac.mlg"
                              TacNumgoals 
                                          );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("type_term"))))))
                                           ((Pcoq.Symbol.nterm uconstr)))
                           (fun c _ loc -> 
# 188 "plugins/ltac/g_ltac.mlg"
                                          TacPretype c 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("fresh"))))))
                                           ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm fresh_id))))
                           (fun l _ loc -> 
# 187 "plugins/ltac/g_ltac.mlg"
                                               TacFreshId l 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.nterm constr_eval)))
                           (fun c loc -> 
# 186 "plugins/ltac/g_ltac.mlg"
                             ConstrMayEval c 
                                         )]))
        in let () = assert (Pcoq.Entry.is_empty fresh_id) in
        let () =
        Pcoq.grammar_extend fresh_id
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm qualid)))
                                  (fun qid loc -> 
# 196 "plugins/ltac/g_ltac.mlg"
                            Locus.ArgVar (CAst.make ~loc @@ Libnames.qualid_basename qid) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                 (fun s loc -> 
# 195 "plugins/ltac/g_ltac.mlg"
                        Locus.ArgArg s (*| id = ident -> Locus.ArgVar (!@loc,id)*) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty constr_eval) in
        let () =
        Pcoq.grammar_extend constr_eval
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("type"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("of"))))))
                                                  ((Pcoq.Symbol.nterm Constr.constr)))
                                  (fun c _ _ loc -> 
# 204 "plugins/ltac/g_ltac.mlg"
            ConstrTypeOf c 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("context"))))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm Constr.lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ c _ id _ loc -> 
# 202 "plugins/ltac/g_ltac.mlg"
            ConstrContext (id,c) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eval"))))))
                                                                 ((Pcoq.Symbol.nterm red_expr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterm Constr.constr)))
                                 (fun c _ rtc _ loc -> 
# 200 "plugins/ltac/g_ltac.mlg"
            ConstrEval (rtc,c) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty constr_may_eval) in
        let () =
        Pcoq.grammar_extend constr_may_eval
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Constr.constr)))
                                  (fun c loc -> 
# 208 "plugins/ltac/g_ltac.mlg"
                               ConstrTerm c 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm constr_eval)))
                                 (fun c loc -> 
# 207 "plugins/ltac/g_ltac.mlg"
                             c 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty tactic_atom) in
        let () =
        Pcoq.grammar_extend tactic_atom
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("()")))))
                                  (fun _ loc -> 
# 213 "plugins/ltac/g_ltac.mlg"
                  TacGeneric (None, genarg_of_unit ()) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm reference)))
                                 (fun r loc -> 
# 212 "plugins/ltac/g_ltac.mlg"
                           TacCall (CAst.make ~loc (r,[])) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm integer)))
                                 (fun n loc -> 
# 211 "plugins/ltac/g_ltac.mlg"
                         TacGeneric (None, genarg_of_int n) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty match_key) in
        let () =
        Pcoq.grammar_extend match_key
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("multimatch"))))))
                                  (fun _ loc -> 
# 218 "plugins/ltac/g_ltac.mlg"
                                General 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("lazymatch"))))))
                                 (fun _ loc -> 
# 217 "plugins/ltac/g_ltac.mlg"
                               Select 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("match")))))
                                 (fun _ loc -> 
# 216 "plugins/ltac/g_ltac.mlg"
                     Once 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty input_fun) in
        let () =
        Pcoq.grammar_extend input_fun
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ident)))
                                  (fun l loc -> 
# 222 "plugins/ltac/g_ltac.mlg"
                       Name.Name l 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                 (fun _ loc -> 
# 221 "plugins/ltac/g_ltac.mlg"
                 Name.Anonymous 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty let_clause) in
        let () =
        Pcoq.grammar_extend let_clause
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm identref)))
                                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm input_fun)))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm ltac_expr)))
                                  (fun te _ args idr loc -> 
# 230 "plugins/ltac/g_ltac.mlg"
           (CAst.map (fun id -> Name id) idr, arg_of_expr (CAst.make ~loc (TacFun (args,te)))) 
                                                            );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 227 "plugins/ltac/g_ltac.mlg"
                       CAst.make ~loc Anonymous 
                                                                 )])))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun te _ na loc -> 
# 228 "plugins/ltac/g_ltac.mlg"
           (na, arg_of_expr te) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun te _ idr loc -> 
# 226 "plugins/ltac/g_ltac.mlg"
           (CAst.map (fun id -> Name id) idr, arg_of_expr te) 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty match_pattern) in
        let () =
        Pcoq.grammar_extend match_pattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Constr.cpattern)))
                                  (fun pc loc -> 
# 236 "plugins/ltac/g_ltac.mlg"
                                  Term pc 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("context"))))))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm Constr.ident))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm Constr.cpattern)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ pc _ oid _ loc -> 
# 235 "plugins/ltac/g_ltac.mlg"
          Subterm (oid, pc) 
                                                          )])]))
        in let () = assert (Pcoq.Entry.is_empty match_hyp) in
        let () =
        Pcoq.grammar_extend match_hyp
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm name)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm match_pattern)))
                                  (fun mpv _ na loc -> 
# 242 "plugins/ltac/g_ltac.mlg"
          let t, ty =
            match mpv with
            | Term t -> (match t with
              | { CAst.v = CCast (t, _, ty) } -> Term t, Some (Term ty)
              | _ -> mpv, None)
            | _ -> mpv, None
          in Def (na, t, Option.default (Term (CAst.make @@ CHole (None, IntroAnonymous, None))) ty) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm match_pattern)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm match_pattern)))
                                 (fun mpt _ _ mpv _ _ na loc -> 
# 240 "plugins/ltac/g_ltac.mlg"
                                                                                      Def (na, mpv, mpt) 
                                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm match_pattern)))
                                 (fun mp _ na loc -> 
# 239 "plugins/ltac/g_ltac.mlg"
                                                 Hyp (na, mp) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty match_context_rule)
        in
        let () =
        Pcoq.grammar_extend match_context_rule
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                  ((Pcoq.Symbol.nterm ltac_expr)))
                                  (fun te _ _ loc -> 
# 256 "plugins/ltac/g_ltac.mlg"
                                       All te 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm match_hyp)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                                 ((Pcoq.Symbol.nterm match_pattern)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun te _ _ mp _ largs _ loc -> 
# 255 "plugins/ltac/g_ltac.mlg"
                                       Pat (largs, mp, te) 
                                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm match_hyp)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                                 ((Pcoq.Symbol.nterm match_pattern)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun te _ mp _ largs loc -> 
# 253 "plugins/ltac/g_ltac.mlg"
                                  Pat (largs, mp, te) 
                                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty match_context_list)
        in
        let () =
        Pcoq.grammar_extend match_context_list
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm match_context_rule)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                  (fun mrl _ loc -> 
# 260 "plugins/ltac/g_ltac.mlg"
                                                         mrl 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm match_context_rule)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun mrl loc -> 
# 259 "plugins/ltac/g_ltac.mlg"
                                                    mrl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty match_rule) in
        let () =
        Pcoq.grammar_extend match_rule
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                  ((Pcoq.Symbol.nterm ltac_expr)))
                                  (fun te _ _ loc -> 
# 264 "plugins/ltac/g_ltac.mlg"
                                       All te 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm match_pattern)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun te _ mp loc -> 
# 263 "plugins/ltac/g_ltac.mlg"
                                                      Pat ([],mp,te) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty match_list) in
        let () =
        Pcoq.grammar_extend match_list
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm match_rule)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                  (fun mrl _ loc -> 
# 268 "plugins/ltac/g_ltac.mlg"
                                                 mrl 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm match_rule)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun mrl loc -> 
# 267 "plugins/ltac/g_ltac.mlg"
                                            mrl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty message_token) in
        let () =
        Pcoq.grammar_extend message_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm natural)))
                                  (fun n loc -> 
# 273 "plugins/ltac/g_ltac.mlg"
                         MsgInt n 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                 (fun s loc -> 
# 272 "plugins/ltac/g_ltac.mlg"
                        MsgString s 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm identref)))
                                 (fun id loc -> 
# 271 "plugins/ltac/g_ltac.mlg"
                           MsgIdent id 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty ltac_def_kind) in
        let () =
        Pcoq.grammar_extend ltac_def_kind
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("::=")))))
                                  (fun _ loc -> 
# 278 "plugins/ltac/g_ltac.mlg"
                   true 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                 (fun _ loc -> 
# 277 "plugins/ltac/g_ltac.mlg"
                  false 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty tacdef_body) in
        let () =
        Pcoq.grammar_extend tacdef_body
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm Constr.global)))
                                                                  ((Pcoq.Symbol.nterm ltac_def_kind)))
                                                  ((Pcoq.Symbol.nterm ltac_expr)))
                                  (fun body redef name loc -> 
# 291 "plugins/ltac/g_ltac.mlg"
          if redef then Tacexpr.TacticRedefinition (name, body)
          else
            let id = reference_to_id name in
            Tacexpr.TacticDefinition (id, body) 
                                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm Constr.global)))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm input_fun)))))
                                                                 ((Pcoq.Symbol.nterm ltac_def_kind)))
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun body redef it name loc -> 
# 285 "plugins/ltac/g_ltac.mlg"
          if redef then Tacexpr.TacticRedefinition (name, CAst.make ~loc (TacFun (it, body)))
          else
            let id = reference_to_id name in
            Tacexpr.TacticDefinition (id, CAst.make ~loc (TacFun (it, body))) 
                                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty tactic) in
        let () =
        Pcoq.grammar_extend tactic
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ltac_expr)))
                                  (fun tac loc -> 
# 298 "plugins/ltac/g_ltac.mlg"
                             tac 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty range_selector) in
        let () =
        Pcoq.grammar_extend range_selector
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm natural)))
                                  (fun n loc -> 
# 303 "plugins/ltac/g_ltac.mlg"
                         (n, n) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun m _ n loc -> 
# 302 "plugins/ltac/g_ltac.mlg"
                                             (n, m) 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty range_selector_or_nth)
        in
        let () =
        Pcoq.grammar_extend range_selector_or_nth
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm natural)))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                                                                   ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm range_selector)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                   (fun l _
                                                                   loc -> 
                                                                   
# 312 "plugins/ltac/g_ltac.mlg"
                                                            l 
                                                                   )]))))
                                  (fun l n loc -> 
# 313 "plugins/ltac/g_ltac.mlg"
          let open Goal_select in
          Option.cata (fun l -> SelectList ((n, n) :: l)) (SelectNth n) l 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm range_selector)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                  (fun l _
                                                                  loc -> 
                                                                  
# 309 "plugins/ltac/g_ltac.mlg"
                                                            l 
                                                                  )]))))
                                 (fun l m _ n loc -> 
# 310 "plugins/ltac/g_ltac.mlg"
          Goal_select.SelectList ((n, m) :: Option.default [] l) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty selector) in
        let () =
        Pcoq.grammar_extend selector
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm test_bracket_ident)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                  ((Pcoq.Symbol.nterm ident)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                  (fun _ id _ _ loc -> 
# 318 "plugins/ltac/g_ltac.mlg"
                                                    Goal_select.SelectId id 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm range_selector_or_nth)))
                                 (fun l loc -> 
# 317 "plugins/ltac/g_ltac.mlg"
                                     l 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty toplevel_selector) in
        let () =
        Pcoq.grammar_extend toplevel_selector
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("all"))))))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                  (fun _ _ loc -> 
# 323 "plugins/ltac/g_ltac.mlg"
                              Goal_select.SelectAll 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                 (fun _ _ loc -> 
# 322 "plugins/ltac/g_ltac.mlg"
                      Goal_select.SelectAlreadyFocused 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm selector)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                 (fun _ sel loc -> 
# 321 "plugins/ltac/g_ltac.mlg"
                                 sel 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty tactic_mode) in
        let () =
        Pcoq.grammar_extend tactic_mode
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm toplevel_selector))))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                  (fun _ g loc -> 
# 327 "plugins/ltac/g_ltac.mlg"
                                            Vernacexpr.VernacSubproof g 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm toplevel_selector))))
                                                 ((Pcoq.Symbol.nterm G_vernac.query_command)))
                                 (fun tac g loc -> 
# 326 "plugins/ltac/g_ltac.mlg"
                                                                     tac g 
                                                   )])]))
        in let () =
        Pcoq.grammar_extend command
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Proof"))))))
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("using"))))))
                                                            ((Pcoq.Symbol.nterm G_vernac.section_subset_expr)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                            ((Pcoq.Symbol.nterm Pltac.tactic)))
                            (fun ta _ l _ _ loc -> 
# 335 "plugins/ltac/g_ltac.mlg"
            Vernacexpr.VernacProof (Some (in_tac ta),Some l) 
                                                   );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Proof"))))))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                           ((Pcoq.Symbol.nterm Pltac.tactic)))
                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                           [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("using"))))))
                                                            ((Pcoq.Symbol.nterm G_vernac.section_subset_expr)))
                                                            (fun l _ loc -> 
                                                            
# 331 "plugins/ltac/g_ltac.mlg"
                                                                       l 
                                                            )]))))
                           (fun l ta _ _ loc -> 
# 332 "plugins/ltac/g_ltac.mlg"
            Vernacexpr.VernacProof (Some (in_tac ta), l) 
                                                )]))
        in let () =
        Pcoq.grammar_extend hint
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Extern"))))))
                                                            ((Pcoq.Symbol.nterm natural)))
                                                            ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm Constr.constr_pattern))))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                            ((Pcoq.Symbol.nterm Pltac.tactic)))
                            (fun tac _ c n _ loc -> 
# 340 "plugins/ltac/g_ltac.mlg"
          Vernacexpr.HintsExtern (n,c, in_tac tac) 
                                                    )]))
        in let () =
        Pcoq.grammar_extend term
        (Pcoq.Reuse (Some
        ("0"), [Pcoq.Production.make
                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("ltac"))))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                ((Pcoq.Symbol.nterm Pltac.ltac_expr)))
                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                (fun _ tac _ _ _ loc -> 
# 344 "plugins/ltac/g_ltac.mlg"
          let arg = Genarg.in_gen (Genarg.rawwit Tacarg.wit_tactic) tac in
          CAst.make ~loc @@ CHole (None, IntroAnonymous, Some arg) 
                                        )]))
        in ()


# 349 "plugins/ltac/g_ltac.mlg"
 

open Stdarg
open Tacarg
open Vernacextend
open Libnames

let pr_ltac_selector s = Pptactic.pr_goal_selector ~toplevel:true s



let (wit_ltac_selector, ltac_selector) = Vernacextend.vernac_argument_extend ~name:"ltac_selector" 
                                         {
                                         Vernacextend.arg_parsing = Vernacextend.Arg_alias (toplevel_selector);
                                         Vernacextend.arg_printer = fun env sigma -> 
                                         
# 360 "plugins/ltac/g_ltac.mlg"
                                                  pr_ltac_selector 
                                         ;
                                         }
let _ = (wit_ltac_selector, ltac_selector)


# 364 "plugins/ltac/g_ltac.mlg"
 

let pr_ltac_info n = str "Info" ++ spc () ++ int n



let (wit_ltac_info, ltac_info) = Vernacextend.vernac_argument_extend ~name:"ltac_info" 
                                 {
                                 Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.next 
                                                              (Pcoq.Rule.stop)
                                                              ((Pcoq.Symbol.token (CLexer.terminal "Info"))))
                                                              ((Pcoq.Symbol.nterm natural)))
                                                              (fun n _ loc ->
                                                              
# 371 "plugins/ltac/g_ltac.mlg"
                             n 
                                                              ))]);
                                 Vernacextend.arg_printer = fun env sigma -> 
                                 
# 370 "plugins/ltac/g_ltac.mlg"
                                              pr_ltac_info 
                                 ;
                                 }
let _ = (wit_ltac_info, ltac_info)


# 374 "plugins/ltac/g_ltac.mlg"
 

let pr_ltac_use_default b =
  if b then (* Bug: a space is inserted before "..." *) str ".." else mt ()



let (wit_ltac_use_default, ltac_use_default) = Vernacextend.vernac_argument_extend ~name:"ltac_use_default" 
                                               {
                                               Vernacextend.arg_parsing = 
                                               Vernacextend.Arg_rules (
                                               [(Pcoq.Production.make
                                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (CLexer.terminal "..."))))
                                                 (fun _ loc -> 
# 383 "plugins/ltac/g_ltac.mlg"
                 true 
                                                               ));
                                               (Pcoq.Production.make
                                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "."))))
                                                (fun _ loc -> 
# 382 "plugins/ltac/g_ltac.mlg"
               false 
                                                              ))]);
                                               Vernacextend.arg_printer = fun env sigma -> 
                                               
# 381 "plugins/ltac/g_ltac.mlg"
                                                     pr_ltac_use_default 
                                               ;
                                               }
let _ = (wit_ltac_use_default, ltac_use_default)


# 386 "plugins/ltac/g_ltac.mlg"
 

let rm_abstract tac =
  let (loc, tac2) = CAst.(tac.loc, tac.v) in
  match tac2 with
  | TacAbstract (t,_) -> t, true
  | TacSolve [ {CAst.loc; v=TacAbstract(t,_)} ] -> CAst.make ?loc (TacSolve [t]), true
  | _ -> tac, false

let is_explicit_terminator = function
  | {CAst.v=(TacSolve _)} -> true
  | _ -> false



let () = Vernacextend.vernac_extend ~command:"VernacSolve"  ?entry:(Some ( tactic_mode )) 
         [(Vernacextend.TyML (false, Vernacextend.TyNonTerminal (Extend.TUopt (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_ltac_selector)), 
                                     Vernacextend.TyNonTerminal (Extend.TUopt (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_ltac_info)), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ltac_use_default), 
                                     Vernacextend.TyNil)))), (let coqpp_body g
                                                             info t
                                                             with_end_tac
                                                             () = Vernacextend.vtmodifyproof (
                                                                  
# 403 "plugins/ltac/g_ltac.mlg"
                                  
    let g = Option.default (Goal_select.get_default_goal_selector ()) g in
    let global = match g with Goal_select.SelectAll | Goal_select.SelectList _ -> true | _ -> false in
    let t = Tacinterp.hide_interp { Tacinterp.global; ast = t; } in
    ComTactic.solve g ~info t ~with_end_tac
  
                                                                  ) in fun g
                                                             info t
                                                             with_end_tac
                                                             ?loc ~atts ()
                                                             -> coqpp_body g
                                                             info t
                                                             with_end_tac
                                                             (Attributes.unsupported_attributes atts)), Some 
         (fun g info t with_end_tac -> 
# 403 "plugins/ltac/g_ltac.mlg"
      classify_as_proofstep 
         )))]

let () = Vernacextend.vernac_extend ~command:"VernacSolveParallel"  ?entry:(Some ( tactic_mode )) 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("par", 
                                     Vernacextend.TyTerminal (":", Vernacextend.TyNonTerminal (
                                                                   Extend.TUopt (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ltac_info)), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                   Vernacextend.TyNonTerminal (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_ltac_use_default), 
                                                                   Vernacextend.TyNil))))), 
         (let coqpp_body info t with_end_tac
         () = Vernacextend.vtmodifyproof (
# 417 "plugins/ltac/g_ltac.mlg"
          
      let t, abstract = rm_abstract t in
      let t = Tacinterp.hide_interp { Tacinterp.global = true; ast = t; } in
      ComTactic.solve_parallel ~info t ~abstract ~with_end_tac
    
              ) in fun info
         t with_end_tac ?loc ~atts () -> coqpp_body info t with_end_tac
         (Attributes.unsupported_attributes atts)), Some (fun info t
                                                         with_end_tac -> 
                                                         
# 413 "plugins/ltac/g_ltac.mlg"
     
      let solving_tac = is_explicit_terminator t in
      let pbr = if solving_tac then Some "par" else None in
      VtProofStep{ proof_block_detection = pbr }
    
                                                         )))]


# 424 "plugins/ltac/g_ltac.mlg"
 

let pr_ltac_tactic_level n = str "(at level " ++ int n ++ str ")"



let (wit_ltac_tactic_level, ltac_tactic_level) = Vernacextend.vernac_argument_extend ~name:"ltac_tactic_level" 
                                                 {
                                                 Vernacextend.arg_parsing = 
                                                 Vernacextend.Arg_rules (
                                                 [(Pcoq.Production.make
                                                   (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.next 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "at"))))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal "level"))))
                                                                   ((Pcoq.Symbol.nterm natural)))
                                                                   ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                   (fun _ n _ _ _ loc -> 
# 431 "plugins/ltac/g_ltac.mlg"
                                           n 
                                                                    ))]);
                                                 Vernacextend.arg_printer = fun env sigma -> 
                                                 
# 430 "plugins/ltac/g_ltac.mlg"
                                                      pr_ltac_tactic_level 
                                                 ;
                                                 }
let _ = (wit_ltac_tactic_level, ltac_tactic_level)

let (wit_ltac_production_sep, ltac_production_sep) = Vernacextend.vernac_argument_extend ~name:"ltac_production_sep" 
                                                     {
                                                     Vernacextend.arg_parsing = 
                                                     Vernacextend.Arg_rules (
                                                     [(Pcoq.Production.make
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.next 
                                                       (Pcoq.Rule.stop)
                                                       ((Pcoq.Symbol.token (CLexer.terminal ","))))
                                                       ((Pcoq.Symbol.nterm string)))
                                                       (fun sep _ loc -> 
# 435 "plugins/ltac/g_ltac.mlg"
                           sep 
                                                                    ))]);
                                                     Vernacextend.arg_printer = fun env sigma -> 
                                                     fun _ -> Pp.str "missing printer";
                                                     }
let _ = (wit_ltac_production_sep, ltac_production_sep)


# 438 "plugins/ltac/g_ltac.mlg"
 

let pr_ltac_production_item = function
| Tacentries.TacTerm s -> quote (str s)
| Tacentries.TacNonTerm (_, ((arg, None), None)) -> str arg
| Tacentries.TacNonTerm (_, ((arg, Some _), None)) -> assert false
| Tacentries.TacNonTerm (_, ((arg, sep), Some id)) ->
  let sep = match sep with
  | None -> mt ()
  | Some sep -> str "," ++ spc () ++ quote (str sep)
  in
  str arg ++ str "(" ++ Id.print id ++ sep ++ str ")"

let check_non_empty_string ?loc s =
  if String.is_empty s then CErrors.user_err ?loc (str "Invalid empty string.")



let (wit_ltac_production_item, ltac_production_item) = Vernacextend.vernac_argument_extend ~name:"ltac_production_item" 
                                                       {
                                                       Vernacextend.arg_parsing = 
                                                       Vernacextend.Arg_rules (
                                                       [(Pcoq.Production.make
                                                         (Pcoq.Rule.next 
                                                         (Pcoq.Rule.stop)
                                                         ((Pcoq.Symbol.nterm ident)))
                                                         (fun nt loc -> 
# 461 "plugins/ltac/g_ltac.mlg"
    Tacentries.TacNonTerm (Loc.tag ~loc ((Id.to_string nt, None), None)) 
                                                                    ));
                                                       (Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.nterm ident)))
                                                        ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                        ((Pcoq.Symbol.nterm ident)))
                                                        ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ltac_production_sep))))
                                                        ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                        (fun _ sep p _ nt
                                                        loc -> 
# 459 "plugins/ltac/g_ltac.mlg"
    Tacentries.TacNonTerm (Loc.tag ~loc ((Id.to_string nt, sep), Some p)) 
                                                               ));
                                                       (Pcoq.Production.make
                                                        (Pcoq.Rule.next 
                                                        (Pcoq.Rule.stop)
                                                        ((Pcoq.Symbol.nterm string)))
                                                        (fun s loc -> 
# 457 "plugins/ltac/g_ltac.mlg"
                     check_non_empty_string ~loc s; Tacentries.TacTerm s 
                                                                    ))]);
                                                       Vernacextend.arg_printer = fun env sigma -> 
                                                       
# 456 "plugins/ltac/g_ltac.mlg"
                                                         pr_ltac_production_item 
                                                       ;
                                                       }
let _ = (wit_ltac_production_item, ltac_production_item)

let () = Vernacextend.vernac_extend ~command:"VernacTacticNotation"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Tactic", 
                                     Vernacextend.TyTerminal ("Notation", 
                                     Vernacextend.TyNonTerminal (Extend.TUopt (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_ltac_tactic_level)), 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1 (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_ltac_production_item)), 
                                     Vernacextend.TyTerminal (":=", Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                                    Vernacextend.TyNil)))))), 
         (let coqpp_body n r e
         (deprecation, locality) = Vernacextend.vtdefault (fun () -> 
# 468 "plugins/ltac/g_ltac.mlg"
   
    let n = Option.default 0 n in
    Tacentries.add_tactic_notation (Locality.make_module_locality locality) n ?deprecation r e;
  
                                   ) in fun n
         r e ?loc ~atts () -> coqpp_body n r e
         (Attributes.parse Attributes.Notations.(deprecation ++ locality) atts)), Some 
         (fun n r e -> 
# 467 "plugins/ltac/g_ltac.mlg"
    VtSideff ([], VtNow) 
         )))]

let () = Vernacextend.vernac_extend ~command:"VernacPrintLtac" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                     Vernacextend.TyTerminal ("Ltac", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNil))), (let coqpp_body r
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 476 "plugins/ltac/g_ltac.mlg"
    Feedback.msg_notice (Tacentries.print_ltac r) 
                                                                 ) in fun r
                                                            ?loc ~atts ()
                                                            -> coqpp_body r
                                                            (Attributes.unsupported_attributes atts)), None))]

let () = Vernacextend.vernac_extend ~command:"VernacLocateLtac" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Locate", 
                                     Vernacextend.TyTerminal ("Ltac", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNil))), (let coqpp_body r
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 481 "plugins/ltac/g_ltac.mlg"
    Tacentries.print_located_tactic r 
                                                                 ) in fun r
                                                            ?loc ~atts ()
                                                            -> coqpp_body r
                                                            (Attributes.unsupported_attributes atts)), None))]


# 484 "plugins/ltac/g_ltac.mlg"
 

let pr_ltac_ref = Libnames.pr_qualid

let pr_tacdef_body env sigma tacdef_body =
  let id, redef, body =
    match tacdef_body with
    | TacticDefinition ({CAst.v=id}, body) -> Id.print id, false, body
    | TacticRedefinition (id, body) -> pr_ltac_ref id, true, body
  in
  let idl, body =
    match body with
      | {CAst.v=(Tacexpr.TacFun (idl,b))} -> idl,b
      | _ -> [], body in
  id ++
    prlist (function Name.Anonymous -> str " _"
      | Name.Name id -> spc () ++ Id.print id) idl
  ++ (if redef then str" ::=" else str" :=") ++ brk(1,1)
  ++ Pptactic.pr_raw_tactic env sigma body



let (wit_ltac_tacdef_body, ltac_tacdef_body) = Vernacextend.vernac_argument_extend ~name:"ltac_tacdef_body" 
                                               {
                                               Vernacextend.arg_parsing = 
                                               Vernacextend.Arg_alias (tacdef_body);
                                               Vernacextend.arg_printer = fun env sigma -> 
                                               
# 507 "plugins/ltac/g_ltac.mlg"
             pr_tacdef_body env sigma 
                                               ;
                                               }
let _ = (wit_ltac_tacdef_body, ltac_tacdef_body)

let () = Vernacextend.vernac_extend ~command:"VernacDeclareTacticDefinition"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Ltac", 
                                     Vernacextend.TyNonTerminal (Extend.TUlist1sep (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_ltac_tacdef_body), "with"), 
                                     Vernacextend.TyNil)), (let coqpp_body l
                                                           (deprecation, locality) = 
                                                           Vernacextend.vtdefault (fun () -> 
                                                           
# 516 "plugins/ltac/g_ltac.mlg"
        
         Tacentries.register_ltac (Locality.make_module_locality locality) ?deprecation l;
  
                                                           ) in fun l
                                                           ?loc ~atts ()
                                                           -> coqpp_body l
                                                           (Attributes.parse Attributes.Notations.(deprecation ++ locality) atts)), Some 
         (fun l -> 
# 512 "plugins/ltac/g_ltac.mlg"
                                                                                     
    VtSideff (List.map (function
      | TacticDefinition ({CAst.v=r},_) -> r
      | TacticRedefinition (qid,_) -> qualid_basename qid) l, VtLater)
  
         )))]

let () = Vernacextend.vernac_extend ~command:"VernacPrintLtacs" ~classifier:(fun _ -> Vernacextend.classify_as_query) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                     Vernacextend.TyTerminal ("Ltac", 
                                     Vernacextend.TyTerminal ("Signatures", 
                                     Vernacextend.TyNil))), (let coqpp_body () = 
                                                            Vernacextend.vtdefault (fun () -> 
                                                            
# 522 "plugins/ltac/g_ltac.mlg"
                                       Tacentries.print_ltacs () 
                                                            ) in fun ?loc ~atts ()
                                                            -> coqpp_body (Attributes.unsupported_attributes atts)), None))]

