let __coq_plugin_name = "coq-core.plugins.ltac2"
let _ = Mltop.add_known_module __coq_plugin_name

# 13 "plugins/ltac2/g_ltac2.mlg"
 

open Pp
open Util
open Names
open Pcoq
open Attributes
open Constrexpr
open Tac2expr
open Tac2qexpr
open Ltac_plugin

let lk_ident_or_anti =
  Pcoq.Lookahead.(lk_ident <+> (lk_kw "$" >> lk_ident >> check_no_space))

(* lookahead for (x:=t), (?x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  let open Pcoq.Lookahead in
  to_entry "test_lpar_idnum_coloneq" begin
    lk_kw "(" >> (lk_ident_or_anti <+> lk_nat) >> lk_kw ":="
  end

(* lookahead for (x:t), (?x:t) *)
let test_lpar_id_colon =
  let open Pcoq.Lookahead in
  to_entry "test_lpar_id_colon" begin
    lk_kw "(" >> lk_ident_or_anti >> lk_kw ":"
  end

(* Hack to recognize "(x := t)" and "($x := t)" *)
let test_lpar_id_coloneq =
  let open Pcoq.Lookahead in
  to_entry "test_lpar_id_coloneq" begin
    lk_kw "(" >> lk_ident_or_anti >> lk_kw ":="
  end

(* Hack to recognize "(x)" *)
let test_lpar_id_rpar =
  let open Pcoq.Lookahead in
  to_entry "test_lpar_id_rpar" begin
    lk_kw "(" >> lk_ident >> lk_kw ")"
  end

let test_ampersand_ident =
  let open Pcoq.Lookahead in
  to_entry "test_ampersand_ident" begin
    lk_kw "&" >> lk_ident >> check_no_space
  end

let test_dollar_ident =
  let open Pcoq.Lookahead in
  to_entry "test_dollar_ident" begin
    lk_kw "$" >> lk_ident >> check_no_space
  end

let test_ltac1_env =
  let open Pcoq.Lookahead in
  to_entry "test_ltac1_env" begin
    lk_ident_list >> lk_kw "|-"
  end

let ltac2_expr = Tac2entries.Pltac.ltac2_expr
let _ltac2_expr = ltac2_expr
let ltac2_type = Entry.create "ltac2_type"
let tac2def_val = Entry.create "tac2def_val"
let tac2def_typ = Entry.create "tac2def_typ"
let tac2def_ext = Entry.create "tac2def_ext"
let tac2def_syn = Entry.create "tac2def_syn"
let tac2def_mut = Entry.create "tac2def_mut"
let tac2mode = Entry.create "ltac2_command"

let ltac_expr = Pltac.ltac_expr
let tac2expr_in_env = Tac2entries.Pltac.tac2expr_in_env

let inj_wit wit loc x = CAst.make ~loc @@ CTacExt (wit, x)
let inj_open_constr loc c = inj_wit Tac2quote.wit_open_constr loc c
let inj_pattern loc c = inj_wit Tac2quote.wit_pattern loc c
let inj_reference loc c = inj_wit Tac2quote.wit_reference loc c
let inj_ltac1 loc e = inj_wit Tac2quote.wit_ltac1 loc e
let inj_ltac1val loc e = inj_wit Tac2quote.wit_ltac1val loc e

let pattern_of_qualid qid =
  if Tac2env.is_constructor qid then CAst.make ?loc:qid.CAst.loc @@ CPatRef (RelId qid, [])
  else
    let open Libnames in
    if qualid_is_ident qid then CAst.make ?loc:qid.CAst.loc @@ CPatVar (Name (qualid_basename qid))
    else
      CErrors.user_err ?loc:qid.CAst.loc (Pp.str "Syntax error")

let opt_fun ?loc args ty e =
  let e = match ty with
  | None -> e
  | Some ty -> CAst.make ?loc:e.CAst.loc (CTacCnv (e, ty))
  in
  match args with
  | [] -> e
  | _ :: _ -> CAst.make ?loc (CTacFun (args, e))



let _ = let tac2pat = Pcoq.Entry.make "tac2pat"
        and atomic_tac2pat = Pcoq.Entry.make "atomic_tac2pat"
        and branches = Pcoq.Entry.make "branches"
        and branch = Pcoq.Entry.make "branch"
        and rec_flag = Pcoq.Entry.make "rec_flag"
        and mut_flag = Pcoq.Entry.make "mut_flag"
        and ltac2_typevar = Pcoq.Entry.make "ltac2_typevar"
        and tactic_atom = Pcoq.Entry.make "tactic_atom"
        and ltac1_expr_in_env = Pcoq.Entry.make "ltac1_expr_in_env"
        and type_cast = Pcoq.Entry.make "type_cast"
        and let_clause = Pcoq.Entry.make "let_clause"
        and let_binder = Pcoq.Entry.make "let_binder"
        and locident = Pcoq.Entry.make "locident"
        and binder = Pcoq.Entry.make "binder"
        and input_fun = Pcoq.Entry.make "input_fun"
        and tac2def_body = Pcoq.Entry.make "tac2def_body"
        and tac2typ_knd = Pcoq.Entry.make "tac2typ_knd"
        and tac2alg_constructors = Pcoq.Entry.make "tac2alg_constructors"
        and tac2alg_constructor = Pcoq.Entry.make "tac2alg_constructor"
        and tac2rec_fields = Pcoq.Entry.make "tac2rec_fields"
        and tac2rec_field = Pcoq.Entry.make "tac2rec_field"
        and tac2rec_fieldexprs = Pcoq.Entry.make "tac2rec_fieldexprs"
        and tac2rec_fieldexpr = Pcoq.Entry.make "tac2rec_fieldexpr"
        and tac2typ_prm = Pcoq.Entry.make "tac2typ_prm"
        and tac2typ_def = Pcoq.Entry.make "tac2typ_def"
        and tac2type_body = Pcoq.Entry.make "tac2type_body"
        and syn_node = Pcoq.Entry.make "syn_node"
        and ltac2_scope = Pcoq.Entry.make "ltac2_scope"
        and syn_level = Pcoq.Entry.make "syn_level"
        and lident = Pcoq.Entry.make "lident"
        and globref = Pcoq.Entry.make "globref"
        in
        let () = assert (Pcoq.Entry.is_empty tac2pat) in
        let () =
        Pcoq.grammar_extend tac2pat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(Some ("1"), Some (Gramlib.Gramext.LeftA),
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm tac2pat)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("::")))))
                                                  ((Pcoq.Symbol.nterm tac2pat)))
                                  (fun p2 _ p1 loc -> 
# 126 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CPatRef (AbsKn (Other Tac2core.Core.c_cons), [p1; p2])
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ _ loc -> 
# 124 "plugins/ltac2/g_ltac2.mlg"
                      CAst.make ~loc @@ CPatRef (AbsKn (Other Tac2core.Core.c_nil), []) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.qualid)))
                                 (fun qid loc -> 
# 123 "plugins/ltac2/g_ltac2.mlg"
                               pattern_of_qualid qid 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm Prim.qualid)))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterml tac2pat ("0"))))))
                                 (fun pl qid loc -> 
# 118 "plugins/ltac2/g_ltac2.mlg"
                                                            
        if Tac2env.is_constructor qid then
          CAst.make ~loc @@ CPatRef (RelId qid, pl)
        else
          CErrors.user_err ~loc (Pp.str "Syntax error") 
                                                    )]);
                                (Some ("0"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm atomic_tac2pat)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ p _ loc -> 
# 132 "plugins/ltac2/g_ltac2.mlg"
                                          p 
                                                   );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm Prim.qualid)))
                                (fun qid loc -> 
# 131 "plugins/ltac2/g_ltac2.mlg"
                               pattern_of_qualid qid 
                                                );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("()")))))
                                (fun _ loc -> 
# 130 "plugins/ltac2/g_ltac2.mlg"
                  CAst.make ~loc @@ CPatRef (AbsKn (Tuple 0), []) 
                                              );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                (fun _ loc -> 
# 129 "plugins/ltac2/g_ltac2.mlg"
                 CAst.make ~loc @@ CPatVar Anonymous 
                                              )])]))
        in let () = assert (Pcoq.Entry.is_empty atomic_tac2pat) in
        let () =
        Pcoq.grammar_extend atomic_tac2pat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm tac2pat)))
                                  (fun p loc -> 
# 143 "plugins/ltac2/g_ltac2.mlg"
                         p 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2pat)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                                                 ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm tac2pat)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                 (fun pl _ p loc -> 
# 141 "plugins/ltac2/g_ltac2.mlg"
          let pl = p :: pl in
          CAst.make ~loc @@ CPatRef (AbsKn (Tuple (List.length pl)), pl) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2pat)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm ltac2_type)))
                                 (fun t _ p loc -> 
# 139 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CPatCnv (p, t) 
                                                   );
                                 Pcoq.Production.make (Pcoq.Rule.stop)
                                 (fun loc -> 
# 137 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CPatRef (AbsKn (Tuple 0), []) 
                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty ltac2_expr) in
        let () =
        Pcoq.grammar_extend ltac2_expr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(Some ("6"), Some (Gramlib.Gramext.RightA),
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  (Pcoq.Symbol.self))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                  (Pcoq.Symbol.self))
                                  (fun e2 _ e1 loc -> 
# 148 "plugins/ltac2/g_ltac2.mlg"
                                         CAst.make ~loc @@ CTacSeq (e1, e2) 
                                                      )]);
                                (Some ("5"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("if")))))
                                                                 ((Pcoq.Symbol.nterml ltac2_expr ("5"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("then")))))
                                                                 ((Pcoq.Symbol.nterml ltac2_expr ("5"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("else")))))
                                                 ((Pcoq.Symbol.nterml ltac2_expr ("5"))))
                                 (fun e2 _ e1 _ e _ loc -> 
# 159 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacIft (e, e1, e2) 
                                                           );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("match")))))
                                                                ((Pcoq.Symbol.nterml ltac2_expr ("5"))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                                ((Pcoq.Symbol.nterm branches)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("end")))))
                                (fun _ bl _ e _ loc -> 
# 157 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacCse (e, bl) 
                                                       );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("let")))))
                                                                ((Pcoq.Symbol.nterm rec_flag)))
                                                                ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm let_clause)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                ((Pcoq.Symbol.nterml ltac2_expr ("6"))))
                                (fun e _ lc isrec _ loc -> 
# 155 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacLet (isrec, lc, e) 
                                                           );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("fun")))))
                                                                ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm input_fun)))))
                                                                ((Pcoq.Symbol.nterm type_cast)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                ((Pcoq.Symbol.nterml ltac2_expr ("6"))))
                                (fun body _ ty it _ loc -> 
# 151 "plugins/ltac2/g_ltac2.mlg"
          opt_fun ~loc it ty body 
                                                           )]);
                                (Some ("4"), Some (Gramlib.Gramext.LeftA),
                                []);
                                (Some ("3"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 (Pcoq.Symbol.self))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                                                 ((Pcoq.Symbol.list1sep (Pcoq.Symbol.next) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                 (fun el _ e0 loc -> 
# 163 "plugins/ltac2/g_ltac2.mlg"
          let el = e0 :: el in
          CAst.make ~loc @@ CTacApp (CAst.make ~loc @@ CTacCst (AbsKn (Tuple (List.length el))), el) 
                                                     )]);
                                (Some ("2"), Some (Gramlib.Gramext.RightA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ltac2_expr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("::")))))
                                                 ((Pcoq.Symbol.nterm ltac2_expr)))
                                 (fun e2 _ e1 loc -> 
# 167 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacApp (CAst.make ~loc @@ CTacCst (AbsKn (Other Tac2core.Core.c_cons)), [e1; e2]) 
                                                     )]);
                                (Some ("1"), Some (Gramlib.Gramext.LeftA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 (Pcoq.Symbol.self))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".(")))))
                                                                 ((Pcoq.Symbol.nterm Prim.qualid)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterml ltac2_expr ("5"))))
                                 (fun r _ _ qid _ e loc -> 
# 175 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacSet (e, RelId qid, r) 
                                                           );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                (Pcoq.Symbol.self))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (".(")))))
                                                                ((Pcoq.Symbol.nterm Prim.qualid)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ qid _ e loc -> 
# 173 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacPrj (e, RelId qid) 
                                                      );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ltac2_expr)))
                                                ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterml ltac2_expr ("0"))))))
                                (fun el e loc -> 
# 171 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacApp (e, el) 
                                                 )]);
                                (Some ("0"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm tactic_atom)))
                                 (fun a loc -> 
# 188 "plugins/ltac2/g_ltac2.mlg"
                             a 
                                               );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                ((Pcoq.Symbol.nterm tac2rec_fieldexprs)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                (fun _ a _ loc -> 
# 187 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacRec a 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterml ltac2_expr ("5"))) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (";"))])) false)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                (fun _ a _ loc -> 
# 185 "plugins/ltac2/g_ltac2.mlg"
          Tac2quote.of_list ~loc (fun x -> x) a 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ _ loc -> 
# 183 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacCst (AbsKn (Tuple 0)) 
                                                );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("()")))))
                                (fun _ loc -> 
# 181 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacCst (AbsKn (Tuple 0)) 
                                              );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                (Pcoq.Symbol.self))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                ((Pcoq.Symbol.nterm ltac2_type)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ t _ a _ loc -> 
# 179 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ CTacCnv (a, t) 
                                                      );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                (Pcoq.Symbol.self))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ a _ loc -> 
# 177 "plugins/ltac2/g_ltac2.mlg"
                                a 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty branches) in
        let () =
        Pcoq.grammar_extend branches
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm branch)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                  (fun bl loc -> 
# 194 "plugins/ltac2/g_ltac2.mlg"
                                     bl 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm branch)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun bl _ loc -> 
# 193 "plugins/ltac2/g_ltac2.mlg"
                                          bl 
                                                  );
                                 Pcoq.Production.make (Pcoq.Rule.stop)
                                 (fun loc -> 
# 192 "plugins/ltac2/g_ltac2.mlg"
           [] 
                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty branch) in
        let () =
        Pcoq.grammar_extend branch
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterml tac2pat ("1"))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                  ((Pcoq.Symbol.nterml ltac2_expr ("6"))))
                                  (fun e _ pat loc -> 
# 198 "plugins/ltac2/g_ltac2.mlg"
                                                                   (pat, e) 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty rec_flag) in
        let () =
        Pcoq.grammar_extend rec_flag
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 202 "plugins/ltac2/g_ltac2.mlg"
             false 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("rec"))))))
                                 (fun _ loc -> 
# 201 "plugins/ltac2/g_ltac2.mlg"
                         true 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty mut_flag) in
        let () =
        Pcoq.grammar_extend mut_flag
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 206 "plugins/ltac2/g_ltac2.mlg"
             false 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("mutable"))))))
                                 (fun _ loc -> 
# 205 "plugins/ltac2/g_ltac2.mlg"
                             true 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty ltac2_typevar) in
        let () =
        Pcoq.grammar_extend ltac2_typevar
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("'")))))
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id _ loc -> 
# 209 "plugins/ltac2/g_ltac2.mlg"
                                  id 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty tactic_atom) in
        let () =
        Pcoq.grammar_extend tactic_atom
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("ltac1val"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm ltac1_expr_in_env)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ qid _ _ _ loc -> 
# 228 "plugins/ltac2/g_ltac2.mlg"
                                                                      inj_ltac1val loc qid 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("ltac1"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm ltac1_expr_in_env)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ qid _ _ _ loc -> 
# 227 "plugins/ltac2/g_ltac2.mlg"
                                                                   inj_ltac1 loc qid 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("reference"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm globref)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ _ _ loc -> 
# 226 "plugins/ltac2/g_ltac2.mlg"
                                                           inj_reference loc c 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("pat"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm Constr.cpattern)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ _ _ loc -> 
# 225 "plugins/ltac2/g_ltac2.mlg"
                                                             inj_pattern loc c 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("ident"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm lident)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ _ _ loc -> 
# 224 "plugins/ltac2/g_ltac2.mlg"
                                                      Tac2quote.of_ident c 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("open_constr"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm Constr.lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ _ _ loc -> 
# 223 "plugins/ltac2/g_ltac2.mlg"
                                                                    Tac2quote.of_open_constr c 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("constr"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm Constr.lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ _ _ loc -> 
# 222 "plugins/ltac2/g_ltac2.mlg"
                                                               Tac2quote.of_constr c 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("'")))))
                                                 ((Pcoq.Symbol.nterm Constr.constr)))
                                 (fun c _ loc -> 
# 221 "plugins/ltac2/g_ltac2.mlg"
                                    inj_open_constr loc c 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("&")))))
                                                 ((Pcoq.Symbol.nterm lident)))
                                 (fun id _ loc -> 
# 220 "plugins/ltac2/g_ltac2.mlg"
                              Tac2quote.of_hyp ~loc id 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("@")))))
                                                 ((Pcoq.Symbol.nterm Prim.ident)))
                                 (fun id _ loc -> 
# 219 "plugins/ltac2/g_ltac2.mlg"
                                  Tac2quote.of_ident (CAst.make ~loc id) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.qualid)))
                                 (fun qid loc -> 
# 215 "plugins/ltac2/g_ltac2.mlg"
        if Tac2env.is_constructor qid then
          CAst.make ~loc @@ CTacCst (RelId qid)
        else
          CAst.make ~loc @@ CTacRef (RelId qid) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.string)))
                                 (fun s loc -> 
# 213 "plugins/ltac2/g_ltac2.mlg"
                             CAst.make ~loc @@ CTacAtm (AtmStr s) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.integer)))
                                 (fun n loc -> 
# 212 "plugins/ltac2/g_ltac2.mlg"
                              CAst.make ~loc @@ CTacAtm (AtmInt n) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty ltac1_expr_in_env) in
        let () =
        Pcoq.grammar_extend ltac1_expr_in_env
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ltac_expr)))
                                  (fun e loc -> 
# 233 "plugins/ltac2/g_ltac2.mlg"
                           [], e 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_ltac1_env)))
                                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm locident))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                 ((Pcoq.Symbol.nterm ltac_expr)))
                                 (fun e _ ids _ loc -> 
# 232 "plugins/ltac2/g_ltac2.mlg"
                                                                       ids, e 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2expr_in_env) in
        let () =
        Pcoq.grammar_extend tac2expr_in_env
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ltac2_expr)))
                                  (fun tac loc -> 
# 245 "plugins/ltac2/g_ltac2.mlg"
                              [], tac 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_ltac1_env)))
                                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm locident))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                 ((Pcoq.Symbol.nterm ltac2_expr)))
                                 (fun e _ ids _ loc -> 
# 238 "plugins/ltac2/g_ltac2.mlg"
        let check { CAst.v = id; CAst.loc = loc } =
          if Tac2env.is_constructor (Libnames.qualid_of_ident ?loc id) then
            CErrors.user_err ?loc Pp.(str "Invalid bound Ltac2 identifier " ++ Id.print id)
        in
        let () = List.iter check ids in
        (ids, e)
      
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty type_cast) in
        let () =
        Pcoq.grammar_extend type_cast
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                  ((Pcoq.Symbol.nterm ltac2_type)))
                                  (fun ty _ loc -> 
# 250 "plugins/ltac2/g_ltac2.mlg"
                                  Some ty 
                                                   );
                                 Pcoq.Production.make (Pcoq.Rule.stop)
                                 (fun loc -> 
# 249 "plugins/ltac2/g_ltac2.mlg"
             None 
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
                                                                  ((Pcoq.Symbol.nterm let_binder)))
                                                                  ((Pcoq.Symbol.nterm type_cast)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm ltac2_expr)))
                                  (fun te _ ty binder loc -> 
# 255 "plugins/ltac2/g_ltac2.mlg"
        let (pat, fn) = binder in
        let te = opt_fun ~loc fn ty te in
        (pat, te) 
                                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty let_binder) in
        let () =
        Pcoq.grammar_extend let_binder
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm input_fun)))))
                                  (fun pats loc -> 
# 262 "plugins/ltac2/g_ltac2.mlg"
        match pats with
        | [{CAst.v=CPatVar _} as pat] -> (pat, [])
        | ({CAst.v=CPatVar (Name id)} as pat) :: args -> (pat, args)
        | [pat] -> (pat, [])
        | _ -> CErrors.user_err ~loc (str "Invalid pattern") 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty ltac2_type) in
        let () =
        Pcoq.grammar_extend ltac2_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(Some ("5"), Some (Gramlib.Gramext.RightA),
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ltac2_type)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("->")))))
                                                  ((Pcoq.Symbol.nterm ltac2_type)))
                                  (fun t2 _ t1 loc -> 
# 271 "plugins/ltac2/g_ltac2.mlg"
                                                    CAst.make ~loc @@ CTypArrow (t1, t2) 
                                                      )]);
                                (Some ("2"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ltac2_type)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterml ltac2_type ("1"))) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("*"))])) false)))
                                 (fun tl _ t loc -> 
# 274 "plugins/ltac2/g_ltac2.mlg"
        let tl = t :: tl in
        CAst.make ~loc @@ CTypRef (AbsKn (Tuple (List.length tl)), tl) 
                                                    )]);
                                (Some ("1"), Some (Gramlib.Gramext.LeftA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 (Pcoq.Symbol.self))
                                                 ((Pcoq.Symbol.nterm Prim.qualid)))
                                 (fun qid t loc -> 
# 277 "plugins/ltac2/g_ltac2.mlg"
                                         CAst.make ~loc @@ CTypRef (RelId qid, [t]) 
                                                   )]);
                                (Some ("0"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.qualid)))
                                 (fun qid loc -> 
# 287 "plugins/ltac2/g_ltac2.mlg"
                               CAst.make ~loc @@ CTypRef (RelId qid, []) 
                                                 );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                (fun _ loc -> 
# 286 "plugins/ltac2/g_ltac2.mlg"
                 CAst.make ~loc @@ CTypVar Anonymous 
                                              );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm ltac2_typevar)))
                                (fun id loc -> 
# 285 "plugins/ltac2/g_ltac2.mlg"
                                CAst.make ~loc @@ CTypVar (Name id) 
                                               );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterml ltac2_type ("5"))) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm Prim.qualid))))
                                (fun qid _ p _ loc -> 
# 280 "plugins/ltac2/g_ltac2.mlg"
          match p, qid with
          | [t], None -> t
          | _, None -> CErrors.user_err ~loc (Pp.str "Syntax error")
          | ts, Some qid -> CAst.make ~loc @@ CTypRef (RelId qid, p)
        
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty locident) in
        let () =
        Pcoq.grammar_extend locident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id loc -> 
# 291 "plugins/ltac2/g_ltac2.mlg"
                             CAst.make ~loc id 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty binder) in
        let () =
        Pcoq.grammar_extend binder
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun l loc -> 
# 295 "plugins/ltac2/g_ltac2.mlg"
                            CAst.make ~loc (Name l) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                 (fun _ loc -> 
# 294 "plugins/ltac2/g_ltac2.mlg"
                 CAst.make ~loc Anonymous 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty input_fun) in
        let () =
        Pcoq.grammar_extend input_fun
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterml tac2pat ("0"))))
                                  (fun b loc -> 
# 298 "plugins/ltac2/g_ltac2.mlg"
                                   b 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2def_body) in
        let () =
        Pcoq.grammar_extend tac2def_body
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm binder)))
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm input_fun))))
                                                                  ((Pcoq.Symbol.nterm type_cast)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm ltac2_expr)))
                                  (fun e _ ty it name loc -> 
# 302 "plugins/ltac2/g_ltac2.mlg"
        (name, opt_fun ~loc it ty e) 
                                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2def_val) in
        let () =
        Pcoq.grammar_extend tac2def_val
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm mut_flag)))
                                                                  ((Pcoq.Symbol.nterm rec_flag)))
                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm tac2def_body)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                  (fun l isrec mut loc -> 
# 307 "plugins/ltac2/g_ltac2.mlg"
          StrVal (mut, isrec, l) 
                                                          )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2def_mut) in
        let () =
        Pcoq.grammar_extend tac2def_mut
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("Set")))))
                                                                  ((Pcoq.Symbol.nterm Prim.qualid)))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                                  ((Pcoq.Symbol.nterm locident)))
                                                                  (fun id _
                                                                  loc -> 
                                                                  
# 311 "plugins/ltac2/g_ltac2.mlg"
                                                                       id 
                                                                  )]))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm ltac2_expr)))
                                  (fun e _ old qid _ loc -> 
# 311 "plugins/ltac2/g_ltac2.mlg"
                                                                                                         StrMut (qid, old, e) 
                                                            )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2typ_knd) in
        let () =
        Pcoq.grammar_extend tac2typ_knd
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                  ((Pcoq.Symbol.nterm tac2rec_fields)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                  (fun _ t _ loc -> 
# 317 "plugins/ltac2/g_ltac2.mlg"
                                         CTydRec t 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm tac2alg_constructors)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ t _ loc -> 
# 316 "plugins/ltac2/g_ltac2.mlg"
                                                CTydAlg t 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("..")))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ _ _ loc -> 
# 315 "plugins/ltac2/g_ltac2.mlg"
                            CTydOpn 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm ltac2_type)))
                                 (fun t loc -> 
# 314 "plugins/ltac2/g_ltac2.mlg"
                            CTydDef (Some t) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2alg_constructors)
        in
        let () =
        Pcoq.grammar_extend tac2alg_constructors
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm tac2alg_constructor)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                  (fun cs loc -> 
# 321 "plugins/ltac2/g_ltac2.mlg"
                                                    cs 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm tac2alg_constructor)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun cs _ loc -> 
# 320 "plugins/ltac2/g_ltac2.mlg"
                                                         cs 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2alg_constructor)
        in
        let () =
        Pcoq.grammar_extend tac2alg_constructor
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm ltac2_type)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ args _ c loc -> 
# 325 "plugins/ltac2/g_ltac2.mlg"
                                                                      (c, args) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.ident)))
                                 (fun c loc -> 
# 324 "plugins/ltac2/g_ltac2.mlg"
                            (c, []) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2rec_fields) in
        let () =
        Pcoq.grammar_extend tac2rec_fields
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 331 "plugins/ltac2/g_ltac2.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm tac2rec_field)))
                                 (fun f loc -> 
# 330 "plugins/ltac2/g_ltac2.mlg"
                               [f] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2rec_field)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                 (fun _ f loc -> 
# 329 "plugins/ltac2/g_ltac2.mlg"
                                    [f] 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2rec_field)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                 ((Pcoq.Symbol.nterm tac2rec_fields)))
                                 (fun l _ f loc -> 
# 328 "plugins/ltac2/g_ltac2.mlg"
                                                        f :: l 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2rec_field) in
        let () =
        Pcoq.grammar_extend tac2rec_field
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm mut_flag)))
                                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                  ((Pcoq.Symbol.nterm ltac2_type)))
                                  (fun t _ id mut loc -> 
# 334 "plugins/ltac2/g_ltac2.mlg"
                                                                  (id, mut, t) 
                                                         )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2rec_fieldexprs)
        in
        let () =
        Pcoq.grammar_extend tac2rec_fieldexprs
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 340 "plugins/ltac2/g_ltac2.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm tac2rec_fieldexpr)))
                                 (fun f loc -> 
# 339 "plugins/ltac2/g_ltac2.mlg"
                                  [f] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2rec_fieldexpr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                 (fun _ f loc -> 
# 338 "plugins/ltac2/g_ltac2.mlg"
                                        [f] 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2rec_fieldexpr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                 ((Pcoq.Symbol.nterm tac2rec_fieldexprs)))
                                 (fun l _ f loc -> 
# 337 "plugins/ltac2/g_ltac2.mlg"
                                                                f :: l 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2rec_fieldexpr) in
        let () =
        Pcoq.grammar_extend tac2rec_fieldexpr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm Prim.qualid)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterml ltac2_expr ("1"))))
                                  (fun e _ qid loc -> 
# 343 "plugins/ltac2/g_ltac2.mlg"
                                                               RelId qid, e 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2typ_prm) in
        let () =
        Pcoq.grammar_extend tac2typ_prm
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ltac2_typevar)))
                                                                  (fun id
                                                                  loc -> 
                                                                  
# 348 "plugins/ltac2/g_ltac2.mlg"
                                                   CAst.make ~loc id 
                                                                  )])) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ ids _ loc -> 
# 348 "plugins/ltac2/g_ltac2.mlg"
                                                                                           ids 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm ltac2_typevar)))
                                 (fun id loc -> 
# 347 "plugins/ltac2/g_ltac2.mlg"
                                [CAst.make ~loc id] 
                                                );
                                 Pcoq.Production.make (Pcoq.Rule.stop)
                                 (fun loc -> 
# 346 "plugins/ltac2/g_ltac2.mlg"
             [] 
                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2typ_def) in
        let () =
        Pcoq.grammar_extend tac2typ_def
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm tac2typ_prm)))
                                                                  ((Pcoq.Symbol.nterm Prim.qualid)))
                                                  ((Pcoq.Symbol.nterm tac2type_body)))
                                  (fun b id prm loc -> 
# 352 "plugins/ltac2/g_ltac2.mlg"
                                                                    let (r, e) = b in (id, r, (prm, e)) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2type_body) in
        let () =
        Pcoq.grammar_extend tac2type_body
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("::=")))))
                                                  ((Pcoq.Symbol.nterm tac2typ_knd)))
                                  (fun e _ loc -> 
# 357 "plugins/ltac2/g_ltac2.mlg"
                                    true, e 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterm tac2typ_knd)))
                                 (fun e _ loc -> 
# 356 "plugins/ltac2/g_ltac2.mlg"
                                   false, e 
                                                 );
                                 Pcoq.Production.make (Pcoq.Rule.stop)
                                 (fun loc -> 
# 355 "plugins/ltac2/g_ltac2.mlg"
             false, CTydDef None 
                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2def_typ) in
        let () =
        Pcoq.grammar_extend tac2def_typ
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                                                  ((Pcoq.Symbol.nterm rec_flag)))
                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm tac2typ_def)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                  (fun l isrec _ loc -> 
# 362 "plugins/ltac2/g_ltac2.mlg"
          StrTyp (isrec, l) 
                                                        )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2def_ext) in
        let () =
        Pcoq.grammar_extend tac2def_ext
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("@")))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("external"))))))
                                                                  ((Pcoq.Symbol.nterm locident)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.nterml ltac2_type ("5"))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                  ((Pcoq.Symbol.nterm Prim.string)))
                                                  ((Pcoq.Symbol.nterm Prim.string)))
                                  (fun name plugin _ t _ id _ _ loc -> 
# 368 "plugins/ltac2/g_ltac2.mlg"
        let ml = { mltac_plugin = "coq-core.plugins." ^ plugin; mltac_tactic = name } in
        StrPrm (id, t, ml) 
                                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty syn_node) in
        let () =
        Pcoq.grammar_extend syn_node
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id loc -> 
# 374 "plugins/ltac2/g_ltac2.mlg"
                             CAst.make ~loc (Some id) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                 (fun _ loc -> 
# 373 "plugins/ltac2/g_ltac2.mlg"
                 CAst.make ~loc None 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty ltac2_scope) in
        let () =
        Pcoq.grammar_extend ltac2_scope
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm syn_node)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm ltac2_scope)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ tok _ id loc -> 
# 382 "plugins/ltac2/g_ltac2.mlg"
          SexprRec (loc, id, tok) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm syn_node)))
                                 (fun id loc -> 
# 380 "plugins/ltac2/g_ltac2.mlg"
                           SexprRec (loc, id, []) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.integer)))
                                 (fun n loc -> 
# 379 "plugins/ltac2/g_ltac2.mlg"
                              SexprInt (CAst.make ~loc n) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.string)))
                                 (fun s loc -> 
# 378 "plugins/ltac2/g_ltac2.mlg"
                             SexprStr (CAst.make ~loc s) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty syn_level) in
        let () =
        Pcoq.grammar_extend syn_level
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                  ((Pcoq.Symbol.nterm Prim.natural)))
                                  (fun n _ loc -> 
# 387 "plugins/ltac2/g_ltac2.mlg"
                                   Some n 
                                                  );
                                 Pcoq.Production.make (Pcoq.Rule.stop)
                                 (fun loc -> 
# 386 "plugins/ltac2/g_ltac2.mlg"
             None 
                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty tac2def_syn) in
        let () =
        Pcoq.grammar_extend tac2def_syn
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("Notation")))))
                                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ltac2_scope)))))
                                                                  ((Pcoq.Symbol.nterm syn_level)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm ltac2_expr)))
                                  (fun e _ n toks _ loc -> 
# 393 "plugins/ltac2/g_ltac2.mlg"
          StrSyn (toks, n, e) 
                                                           )])]))
        in let () = assert (Pcoq.Entry.is_empty lident) in
        let () =
        Pcoq.grammar_extend lident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id loc -> 
# 397 "plugins/ltac2/g_ltac2.mlg"
                             CAst.make ~loc id 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty globref) in
        let () =
        Pcoq.grammar_extend globref
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.qualid)))
                                  (fun qid loc -> 
# 401 "plugins/ltac2/g_ltac2.mlg"
                               CAst.make ~loc @@ QReference qid 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("&")))))
                                                 ((Pcoq.Symbol.nterm Prim.ident)))
                                 (fun id _ loc -> 
# 400 "plugins/ltac2/g_ltac2.mlg"
                                  CAst.make ~loc (QHypothesis id) 
                                                  )])]))
        in ()


# 408 "plugins/ltac2/g_ltac2.mlg"
 

open Tac2entries.Pltac

let loc_of_ne_list l = Loc.merge_opt (fst (List.hd l)) (fst (List.last l))



let _ = let anti = Pcoq.Entry.make "anti"
        and ident_or_anti = Pcoq.Entry.make "ident_or_anti"
        and lident = Pcoq.Entry.make "lident"
        and lnatural = Pcoq.Entry.make "lnatural"
        and qhyp = Pcoq.Entry.make "qhyp"
        and simple_binding = Pcoq.Entry.make "simple_binding"
        and bindings = Pcoq.Entry.make "bindings"
        and intropatterns = Pcoq.Entry.make "intropatterns"
        and or_and_intropattern = Pcoq.Entry.make "or_and_intropattern"
        and equality_intropattern = Pcoq.Entry.make "equality_intropattern"
        and naming_intropattern = Pcoq.Entry.make "naming_intropattern"
        and nonsimple_intropattern = Pcoq.Entry.make "nonsimple_intropattern"
        and simple_intropattern = Pcoq.Entry.make "simple_intropattern"
        and simple_intropattern_closed =
          Pcoq.Entry.make "simple_intropattern_closed"
        and nat_or_anti = Pcoq.Entry.make "nat_or_anti"
        and eqn_ipat = Pcoq.Entry.make "eqn_ipat"
        and with_bindings = Pcoq.Entry.make "with_bindings"
        and constr_with_bindings = Pcoq.Entry.make "constr_with_bindings"
        and destruction_arg = Pcoq.Entry.make "destruction_arg"
        and as_or_and_ipat = Pcoq.Entry.make "as_or_and_ipat"
        and occs_nums = Pcoq.Entry.make "occs_nums"
        and occs = Pcoq.Entry.make "occs"
        and hypident = Pcoq.Entry.make "hypident"
        and hypident_occ = Pcoq.Entry.make "hypident_occ"
        and in_clause = Pcoq.Entry.make "in_clause"
        and clause = Pcoq.Entry.make "clause"
        and concl_occ = Pcoq.Entry.make "concl_occ"
        and induction_clause = Pcoq.Entry.make "induction_clause"
        and conversion = Pcoq.Entry.make "conversion"
        and ltac2_orient = Pcoq.Entry.make "ltac2_orient"
        and rewriter = Pcoq.Entry.make "rewriter"
        and oriented_rewriter = Pcoq.Entry.make "oriented_rewriter"
        and tactic_then_last = Pcoq.Entry.make "tactic_then_last"
        and for_each_goal = Pcoq.Entry.make "for_each_goal"
        and ltac2_red_flag = Pcoq.Entry.make "ltac2_red_flag"
        and refglobal = Pcoq.Entry.make "refglobal"
        and refglobals = Pcoq.Entry.make "refglobals"
        and delta_flag = Pcoq.Entry.make "delta_flag"
        and strategy_flag = Pcoq.Entry.make "strategy_flag"
        and hintdb = Pcoq.Entry.make "hintdb"
        and match_pattern = Pcoq.Entry.make "match_pattern"
        and match_rule = Pcoq.Entry.make "match_rule"
        and match_list = Pcoq.Entry.make "match_list"
        and gmatch_hyp_pattern = Pcoq.Entry.make "gmatch_hyp_pattern"
        and gmatch_pattern = Pcoq.Entry.make "gmatch_pattern"
        and gmatch_rule = Pcoq.Entry.make "gmatch_rule"
        and goal_match_list = Pcoq.Entry.make "goal_match_list"
        and move_location = Pcoq.Entry.make "move_location"
        and as_name = Pcoq.Entry.make "as_name"
        and pose = Pcoq.Entry.make "pose"
        and as_ipat = Pcoq.Entry.make "as_ipat"
        and by_tactic = Pcoq.Entry.make "by_tactic"
        and assertion = Pcoq.Entry.make "assertion"
        in
        let () = assert (Pcoq.Entry.is_empty anti) in
        let () =
        Pcoq.grammar_extend anti
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("$")))))
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id _ loc -> 
# 422 "plugins/ltac2/g_ltac2.mlg"
                                  QAnti (CAst.make ~loc id) 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty ident_or_anti) in
        let () =
        Pcoq.grammar_extend ident_or_anti
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("$")))))
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id _ loc -> 
# 426 "plugins/ltac2/g_ltac2.mlg"
                                  QAnti (CAst.make ~loc id) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm lident)))
                                 (fun id loc -> 
# 425 "plugins/ltac2/g_ltac2.mlg"
                         QExpr id 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty lident) in
        let () =
        Pcoq.grammar_extend lident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id loc -> 
# 430 "plugins/ltac2/g_ltac2.mlg"
                             CAst.make ~loc id 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty lnatural) in
        let () =
        Pcoq.grammar_extend lnatural
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.natural)))
                                  (fun n loc -> 
# 433 "plugins/ltac2/g_ltac2.mlg"
                              CAst.make ~loc n 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty q_ident) in
        let () =
        Pcoq.grammar_extend q_ident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ident_or_anti)))
                                  (fun id loc -> 
# 436 "plugins/ltac2/g_ltac2.mlg"
                                id 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty qhyp) in
        let () =
        Pcoq.grammar_extend qhyp
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm lident)))
                                  (fun id loc -> 
# 441 "plugins/ltac2/g_ltac2.mlg"
                         QExpr (CAst.make ~loc @@ QNamedHyp id) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm lnatural)))
                                 (fun n loc -> 
# 440 "plugins/ltac2/g_ltac2.mlg"
                          QExpr (CAst.make ~loc @@ QAnonHyp n) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm anti)))
                                 (fun x loc -> 
# 439 "plugins/ltac2/g_ltac2.mlg"
                      x 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty simple_binding) in
        let () =
        Pcoq.grammar_extend simple_binding
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm qhyp)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                  ((Pcoq.Symbol.nterm Constr.lconstr)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ c _ h _ loc -> 
# 446 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc (h, c) 
                                                        )])]))
        in let () = assert (Pcoq.Entry.is_empty bindings) in
        let () =
        Pcoq.grammar_extend bindings
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm Constr.constr)))))
                                  (fun bl loc -> 
# 453 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QImplicitBindings bl 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_lpar_idnum_coloneq)))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm simple_binding)))))
                                 (fun bl _ loc -> 
# 451 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QExplicitBindings bl 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty q_bindings) in
        let () =
        Pcoq.grammar_extend q_bindings
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm bindings)))
                                  (fun bl loc -> 
# 457 "plugins/ltac2/g_ltac2.mlg"
                           bl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty q_with_bindings) in
        let () =
        Pcoq.grammar_extend q_with_bindings
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm with_bindings)))
                                  (fun bl loc -> 
# 460 "plugins/ltac2/g_ltac2.mlg"
                                bl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty intropatterns) in
        let () =
        Pcoq.grammar_extend intropatterns
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm nonsimple_intropattern))))
                                  (fun l loc -> 
# 463 "plugins/ltac2/g_ltac2.mlg"
                                              CAst.make ~loc l 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty or_and_intropattern)
        in
        let () =
        Pcoq.grammar_extend or_and_intropattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm simple_intropattern)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("&")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm simple_intropattern)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("&"))])) false)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ tc _ si _ loc -> 
# 478 "plugins/ltac2/g_ltac2.mlg"
          let rec pairify = function
            | ([]|[_]|[_;_]) as l -> CAst.make ~loc l
            | t::q ->
              let q =
                CAst.make ~loc @@
                  QIntroAction (CAst.make ~loc @@
                    QIntroOrAndPattern (CAst.make ~loc @@
                      QIntroAndPattern (pairify q)))
              in
              CAst.make ~loc [t; q]
          in CAst.make ~loc @@ QIntroAndPattern (pairify (si::tc)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm simple_intropattern)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm simple_intropattern)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ tc _ si _ loc -> 
# 474 "plugins/ltac2/g_ltac2.mlg"
               CAst.make ~loc @@ QIntroAndPattern (CAst.make ~loc (si::tc)) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm simple_intropattern)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ si _ loc -> 
# 471 "plugins/ltac2/g_ltac2.mlg"
                                                CAst.make ~loc @@ QIntroAndPattern (CAst.make ~loc [si]) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("()")))))
                                 (fun _ loc -> 
# 470 "plugins/ltac2/g_ltac2.mlg"
                  CAst.make ~loc @@ QIntroAndPattern (CAst.make ~loc []) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm intropatterns)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ tc _ loc -> 
# 469 "plugins/ltac2/g_ltac2.mlg"
                                                        CAst.make ~loc @@ QIntroOrPattern tc 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty equality_intropattern)
        in
        let () =
        Pcoq.grammar_extend equality_intropattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("[=")))))
                                                                  ((Pcoq.Symbol.nterm intropatterns)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                  (fun _ tc _ loc -> 
# 493 "plugins/ltac2/g_ltac2.mlg"
                                           CAst.make ~loc @@ QIntroInjection tc 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("<-")))))
                                 (fun _ loc -> 
# 492 "plugins/ltac2/g_ltac2.mlg"
                  CAst.make ~loc @@ QIntroRewrite false 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("->")))))
                                 (fun _ loc -> 
# 491 "plugins/ltac2/g_ltac2.mlg"
                  CAst.make ~loc @@ QIntroRewrite true 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty naming_intropattern)
        in
        let () =
        Pcoq.grammar_extend naming_intropattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ident_or_anti)))
                                  (fun id loc -> 
# 503 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QIntroIdentifier id 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                 (fun _ loc -> 
# 501 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QIntroAnonymous 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?$")))))
                                                 ((Pcoq.Symbol.nterm lident)))
                                 (fun id _ loc -> 
# 499 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QIntroFresh (QAnti id) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PLEFTQMARK))))
                                                 ((Pcoq.Symbol.nterm lident)))
                                 (fun id _ loc -> 
# 497 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QIntroFresh (QExpr id) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty nonsimple_intropattern)
        in
        let () =
        Pcoq.grammar_extend nonsimple_intropattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("**")))))
                                  (fun _ loc -> 
# 509 "plugins/ltac2/g_ltac2.mlg"
                  CAst.make ~loc @@ QIntroForthcoming false 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                 (fun _ loc -> 
# 508 "plugins/ltac2/g_ltac2.mlg"
                  CAst.make ~loc @@ QIntroForthcoming true 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm simple_intropattern)))
                                 (fun l loc -> 
# 507 "plugins/ltac2/g_ltac2.mlg"
                                     l 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty simple_intropattern)
        in
        let () =
        Pcoq.grammar_extend simple_intropattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm simple_intropattern_closed)))
                                  (fun pat loc -> 
# 515 "plugins/ltac2/g_ltac2.mlg"
          pat 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty simple_intropattern_closed)
        in
        let () =
        Pcoq.grammar_extend simple_intropattern_closed
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm naming_intropattern)))
                                  (fun pat loc -> 
# 526 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QIntroNaming pat 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                 (fun _ loc -> 
# 524 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QIntroAction (CAst.make ~loc @@ QIntroWildcard) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm equality_intropattern)))
                                 (fun pat loc -> 
# 522 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QIntroAction pat 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm or_and_intropattern)))
                                 (fun pat loc -> 
# 520 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QIntroAction (CAst.make ~loc @@ QIntroOrAndPattern pat) 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty q_intropatterns) in
        let () =
        Pcoq.grammar_extend q_intropatterns
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm intropatterns)))
                                  (fun ipat loc -> 
# 530 "plugins/ltac2/g_ltac2.mlg"
                                  ipat 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty q_intropattern) in
        let () =
        Pcoq.grammar_extend q_intropattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm simple_intropattern)))
                                  (fun ipat loc -> 
# 533 "plugins/ltac2/g_ltac2.mlg"
                                        ipat 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty nat_or_anti) in
        let () =
        Pcoq.grammar_extend nat_or_anti
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("$")))))
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id _ loc -> 
# 537 "plugins/ltac2/g_ltac2.mlg"
                                  QAnti (CAst.make ~loc id) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm lnatural)))
                                 (fun n loc -> 
# 536 "plugins/ltac2/g_ltac2.mlg"
                          QExpr n 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty eqn_ipat) in
        let () =
        Pcoq.grammar_extend eqn_ipat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 542 "plugins/ltac2/g_ltac2.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eqn"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm naming_intropattern)))
                                 (fun pat _ _ loc -> 
# 541 "plugins/ltac2/g_ltac2.mlg"
                                                         Some pat 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty with_bindings) in
        let () =
        Pcoq.grammar_extend with_bindings
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 546 "plugins/ltac2/g_ltac2.mlg"
                                               CAst.make ~loc @@ QNoBindings 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                 ((Pcoq.Symbol.nterm bindings)))
                                 (fun bl _ loc -> 
# 546 "plugins/ltac2/g_ltac2.mlg"
                                   bl 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty constr_with_bindings)
        in
        let () =
        Pcoq.grammar_extend constr_with_bindings
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm Constr.constr)))
                                                  ((Pcoq.Symbol.nterm with_bindings)))
                                  (fun l c loc -> 
# 549 "plugins/ltac2/g_ltac2.mlg"
                                                  CAst.make ~loc @@ (c, l) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty destruction_arg) in
        let () =
        Pcoq.grammar_extend destruction_arg
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr_with_bindings)))
                                  (fun c loc -> 
# 554 "plugins/ltac2/g_ltac2.mlg"
                                      CAst.make ~loc @@ QElimOnConstr c 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm lident)))
                                 (fun id loc -> 
# 553 "plugins/ltac2/g_ltac2.mlg"
                         CAst.make ~loc @@ QElimOnIdent id 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm lnatural)))
                                 (fun n loc -> 
# 552 "plugins/ltac2/g_ltac2.mlg"
                          CAst.make ~loc @@ QElimOnAnonHyp n 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty q_destruction_arg) in
        let () =
        Pcoq.grammar_extend q_destruction_arg
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm destruction_arg)))
                                  (fun arg loc -> 
# 558 "plugins/ltac2/g_ltac2.mlg"
                                   arg 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty as_or_and_ipat) in
        let () =
        Pcoq.grammar_extend as_or_and_ipat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 562 "plugins/ltac2/g_ltac2.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm or_and_intropattern)))
                                 (fun ipat _ loc -> 
# 561 "plugins/ltac2/g_ltac2.mlg"
                                              Some ipat 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty occs_nums) in
        let () =
        Pcoq.grammar_extend occs_nums
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                                  ((Pcoq.Symbol.nterm nat_or_anti)))
                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm nat_or_anti))))
                                  (fun nl n _ loc -> 
# 568 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QAllOccurrencesBut (n::nl) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm nat_or_anti)))))
                                 (fun nl loc -> 
# 566 "plugins/ltac2/g_ltac2.mlg"
                                    CAst.make ~loc @@ QOnlyOccurrences nl 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty occs) in
        let () =
        Pcoq.grammar_extend occs
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 572 "plugins/ltac2/g_ltac2.mlg"
                                                  CAst.make ~loc QAllOccurrences 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                 ((Pcoq.Symbol.nterm occs_nums)))
                                 (fun occs _ loc -> 
# 572 "plugins/ltac2/g_ltac2.mlg"
                                    occs 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty hypident) in
        let () =
        Pcoq.grammar_extend hypident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("value"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("of"))))))
                                                                  ((Pcoq.Symbol.nterm ident_or_anti)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ id _ _ _ loc -> 
# 580 "plugins/ltac2/g_ltac2.mlg"
          id,Locus.InHypValueOnly 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("type"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("of"))))))
                                                                 ((Pcoq.Symbol.nterm ident_or_anti)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ id _ _ _ loc -> 
# 578 "plugins/ltac2/g_ltac2.mlg"
          id,Locus.InHypTypeOnly 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm ident_or_anti)))
                                 (fun id loc -> 
# 576 "plugins/ltac2/g_ltac2.mlg"
          id,Locus.InHyp 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty hypident_occ) in
        let () =
        Pcoq.grammar_extend hypident_occ
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm hypident)))
                                                  ((Pcoq.Symbol.nterm occs)))
                                  (fun occs h loc -> 
# 584 "plugins/ltac2/g_ltac2.mlg"
                                   let (id,l) = h in ((occs,id),l) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty in_clause) in
        let () =
        Pcoq.grammar_extend in_clause
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm hypident_occ)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                  (fun hl loc -> 
# 594 "plugins/ltac2/g_ltac2.mlg"
          { q_onhyps = Some hl; q_concl_occs = CAst.make ~loc QNoOccurrences } 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm hypident_occ)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                 ((Pcoq.Symbol.nterm concl_occ)))
                                 (fun occs _ hl loc -> 
# 592 "plugins/ltac2/g_ltac2.mlg"
          { q_onhyps = Some hl; q_concl_occs = occs } 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                 ((Pcoq.Symbol.nterm concl_occ)))
                                 (fun occs _ _ loc -> 
# 590 "plugins/ltac2/g_ltac2.mlg"
          { q_onhyps = None; q_concl_occs = occs } 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                                 ((Pcoq.Symbol.nterm occs)))
                                 (fun occs _ loc -> 
# 588 "plugins/ltac2/g_ltac2.mlg"
          { q_onhyps = None; q_concl_occs = occs } 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty clause) in
        let () =
        Pcoq.grammar_extend clause
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                  ((Pcoq.Symbol.nterm occs_nums)))
                                  (fun occs _ loc -> 
# 600 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ { q_onhyps = Some []; q_concl_occs = occs } 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterm in_clause)))
                                 (fun cl _ loc -> 
# 598 "plugins/ltac2/g_ltac2.mlg"
                                  CAst.make ~loc @@ cl 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty q_clause) in
        let () =
        Pcoq.grammar_extend q_clause
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm clause)))
                                  (fun cl loc -> 
# 604 "plugins/ltac2/g_ltac2.mlg"
                         cl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty concl_occ) in
        let () =
        Pcoq.grammar_extend concl_occ
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 608 "plugins/ltac2/g_ltac2.mlg"
             CAst.make ~loc QNoOccurrences 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                                 ((Pcoq.Symbol.nterm occs)))
                                 (fun occs _ loc -> 
# 607 "plugins/ltac2/g_ltac2.mlg"
                              occs 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty induction_clause) in
        let () =
        Pcoq.grammar_extend induction_clause
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm destruction_arg)))
                                                                  ((Pcoq.Symbol.nterm as_or_and_ipat)))
                                                                  ((Pcoq.Symbol.nterm eqn_ipat)))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm clause))))
                                  (fun cl eq pat c loc -> 
# 614 "plugins/ltac2/g_ltac2.mlg"
        CAst.make ~loc @@ {
          indcl_arg = c;
          indcl_eqn = eq;
          indcl_as = pat;
          indcl_in = cl;
        } 
                                                          )])]))
        in let () = assert (Pcoq.Entry.is_empty q_induction_clause)
        in
        let () =
        Pcoq.grammar_extend q_induction_clause
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm induction_clause)))
                                  (fun cl loc -> 
# 623 "plugins/ltac2/g_ltac2.mlg"
                                   cl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty conversion) in
        let () =
        Pcoq.grammar_extend conversion
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm Constr.constr)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                  ((Pcoq.Symbol.nterm Constr.constr)))
                                  (fun c2 _ c1 loc -> 
# 629 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QConvertWith (c1, c2) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Constr.constr)))
                                 (fun c loc -> 
# 627 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ QConvert c 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty q_conversion) in
        let () =
        Pcoq.grammar_extend q_conversion
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm conversion)))
                                  (fun c loc -> 
# 633 "plugins/ltac2/g_ltac2.mlg"
                            c 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty ltac2_orient) in
        let () =
        Pcoq.grammar_extend ltac2_orient
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 638 "plugins/ltac2/g_ltac2.mlg"
             CAst.make ~loc None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("<-")))))
                                 (fun _ loc -> 
# 637 "plugins/ltac2/g_ltac2.mlg"
                  CAst.make ~loc (Some false) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("->")))))
                                 (fun _ loc -> 
# 636 "plugins/ltac2/g_ltac2.mlg"
                  CAst.make ~loc (Some true) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty rewriter) in
        let () =
        Pcoq.grammar_extend rewriter
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr_with_bindings)))
                                  (fun c loc -> 
# 653 "plugins/ltac2/g_ltac2.mlg"
          (CAst.make ~loc @@ QPrecisely (CAst.make 1), c) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm lnatural)))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings)))
                                 (fun c n loc -> 
# 651 "plugins/ltac2/g_ltac2.mlg"
          (CAst.make ~loc @@ QPrecisely n,c) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm lnatural)))
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PLEFTQMARK))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 648 "plugins/ltac2/g_ltac2.mlg"
                                                      () 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 648 "plugins/ltac2/g_ltac2.mlg"
                                () 
                                                                 )])))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings)))
                                 (fun c _ n loc -> 
# 649 "plugins/ltac2/g_ltac2.mlg"
          (CAst.make ~loc @@ QUpTo n,c) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm lnatural)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings)))
                                 (fun c _ n loc -> 
# 647 "plugins/ltac2/g_ltac2.mlg"
          (CAst.make ~loc @@ QPrecisely n,c) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PLEFTQMARK))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 644 "plugins/ltac2/g_ltac2.mlg"
                                         () 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 644 "plugins/ltac2/g_ltac2.mlg"
                   () 
                                                                 )])))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings)))
                                 (fun c _ loc -> 
# 645 "plugins/ltac2/g_ltac2.mlg"
          (CAst.make ~loc @@ QRepeatStar,c) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings)))
                                 (fun c _ loc -> 
# 643 "plugins/ltac2/g_ltac2.mlg"
          (CAst.make ~loc @@ QRepeatPlus,c) 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty oriented_rewriter) in
        let () =
        Pcoq.grammar_extend oriented_rewriter
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ltac2_orient)))
                                                  ((Pcoq.Symbol.nterm rewriter)))
                                  (fun r b loc -> 
# 658 "plugins/ltac2/g_ltac2.mlg"
        let (m, c) = r in
        CAst.make ~loc @@ {
        rew_orient = b;
        rew_repeat = m;
        rew_equatn = c;
      } 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty q_rewriting) in
        let () =
        Pcoq.grammar_extend q_rewriting
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm oriented_rewriter)))
                                  (fun r loc -> 
# 667 "plugins/ltac2/g_ltac2.mlg"
                                   r 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty tactic_then_last) in
        let () =
        Pcoq.grammar_extend tactic_then_last
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 671 "plugins/ltac2/g_ltac2.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.opt (Pcoq.Symbol.nterml ltac2_expr ("6")))) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun lta _ loc -> 
# 670 "plugins/ltac2/g_ltac2.mlg"
                                                                 lta 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty for_each_goal) in
        let () =
        Pcoq.grammar_extend for_each_goal
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 680 "plugins/ltac2/g_ltac2.mlg"
             ([None], None) 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.nterm for_each_goal)))
                                 (fun tg _ loc -> 
# 679 "plugins/ltac2/g_ltac2.mlg"
                                     let (first,last) = tg in (None :: first, last) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm ltac2_expr)))
                                 (fun ta loc -> 
# 678 "plugins/ltac2/g_ltac2.mlg"
                             ([Some ta], None) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("..")))))
                                                 ((Pcoq.Symbol.nterm tactic_then_last)))
                                 (fun l _ loc -> 
# 677 "plugins/ltac2/g_ltac2.mlg"
                                        ([], Some (None, l)) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ltac2_expr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("..")))))
                                                 ((Pcoq.Symbol.nterm tactic_then_last)))
                                 (fun l _ ta loc -> 
# 676 "plugins/ltac2/g_ltac2.mlg"
                                                         ([], Some (Some ta, l)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ltac2_expr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.nterm for_each_goal)))
                                 (fun tg _ ta loc -> 
# 675 "plugins/ltac2/g_ltac2.mlg"
                                                      let (first,last) = tg in (Some ta :: first, last) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty q_dispatch) in
        let () =
        Pcoq.grammar_extend q_dispatch
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm for_each_goal)))
                                  (fun d loc -> 
# 684 "plugins/ltac2/g_ltac2.mlg"
                               CAst.make ~loc d 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty q_occurrences) in
        let () =
        Pcoq.grammar_extend q_occurrences
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm occs)))
                                  (fun occs loc -> 
# 687 "plugins/ltac2/g_ltac2.mlg"
                         occs 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty ltac2_red_flag) in
        let () =
        Pcoq.grammar_extend ltac2_red_flag
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("delta"))))))
                                                  ((Pcoq.Symbol.nterm delta_flag)))
                                  (fun d _ loc -> 
# 696 "plugins/ltac2/g_ltac2.mlg"
                                           d 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("zeta"))))))
                                 (fun _ loc -> 
# 695 "plugins/ltac2/g_ltac2.mlg"
                          CAst.make ~loc @@ QZeta 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("cofix"))))))
                                 (fun _ loc -> 
# 694 "plugins/ltac2/g_ltac2.mlg"
                           CAst.make ~loc @@ QCofix 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("fix"))))))
                                 (fun _ loc -> 
# 693 "plugins/ltac2/g_ltac2.mlg"
                         CAst.make ~loc @@ QFix 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("match"))))))
                                 (fun _ loc -> 
# 692 "plugins/ltac2/g_ltac2.mlg"
                           CAst.make ~loc @@ QMatch 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("iota"))))))
                                 (fun _ loc -> 
# 691 "plugins/ltac2/g_ltac2.mlg"
                          CAst.make ~loc @@ QIota 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("beta"))))))
                                 (fun _ loc -> 
# 690 "plugins/ltac2/g_ltac2.mlg"
                          CAst.make ~loc @@ QBeta 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty refglobal) in
        let () =
        Pcoq.grammar_extend refglobal
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("$")))))
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id _ loc -> 
# 702 "plugins/ltac2/g_ltac2.mlg"
                                  QAnti (CAst.make ~loc id) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm Prim.qualid)))
                                 (fun qid loc -> 
# 701 "plugins/ltac2/g_ltac2.mlg"
                               QExpr (CAst.make ~loc @@ QReference qid) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("&")))))
                                                 ((Pcoq.Symbol.nterm Prim.ident)))
                                 (fun id _ loc -> 
# 700 "plugins/ltac2/g_ltac2.mlg"
                                  QExpr (CAst.make ~loc @@ QHypothesis id) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty q_reference) in
        let () =
        Pcoq.grammar_extend q_reference
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm refglobal)))
                                  (fun r loc -> 
# 706 "plugins/ltac2/g_ltac2.mlg"
                           r 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty refglobals) in
        let () =
        Pcoq.grammar_extend refglobals
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm refglobal)))))
                                  (fun gl loc -> 
# 709 "plugins/ltac2/g_ltac2.mlg"
                                  CAst.make ~loc gl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty delta_flag) in
        let () =
        Pcoq.grammar_extend delta_flag
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 714 "plugins/ltac2/g_ltac2.mlg"
             CAst.make ~loc @@ QDeltaBut (CAst.make ~loc []) 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm refglobals)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ idl _ loc -> 
# 713 "plugins/ltac2/g_ltac2.mlg"
                                        CAst.make ~loc @@ QConst idl 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm refglobals)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ idl _ _ loc -> 
# 712 "plugins/ltac2/g_ltac2.mlg"
                                             CAst.make ~loc @@ QDeltaBut idl 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty strategy_flag) in
        let () =
        Pcoq.grammar_extend strategy_flag
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm delta_flag)))
                                  (fun d loc -> 
# 720 "plugins/ltac2/g_ltac2.mlg"
        CAst.make ~loc
          [CAst.make ~loc QBeta; CAst.make ~loc QIota; CAst.make ~loc QZeta; d] 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ltac2_red_flag)))))
                                 (fun s loc -> 
# 718 "plugins/ltac2/g_ltac2.mlg"
                                      CAst.make ~loc s 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty q_strategy_flag) in
        let () =
        Pcoq.grammar_extend q_strategy_flag
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm strategy_flag)))
                                  (fun flag loc -> 
# 725 "plugins/ltac2/g_ltac2.mlg"
                                  flag 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty hintdb) in
        let () =
        Pcoq.grammar_extend hintdb
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ident_or_anti)))))
                                  (fun l loc -> 
# 729 "plugins/ltac2/g_ltac2.mlg"
                                     CAst.make ~loc @@ QHintDbs l 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                 (fun _ loc -> 
# 728 "plugins/ltac2/g_ltac2.mlg"
                 CAst.make ~loc @@ QHintAll 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty q_hintdb) in
        let () =
        Pcoq.grammar_extend q_hintdb
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm hintdb)))
                                  (fun db loc -> 
# 733 "plugins/ltac2/g_ltac2.mlg"
                         db 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty match_pattern) in
        let () =
        Pcoq.grammar_extend match_pattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Constr.cpattern)))
                                  (fun pat loc -> 
# 738 "plugins/ltac2/g_ltac2.mlg"
                                   CAst.make ~loc @@ QConstrMatchPattern pat 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("context"))))))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm Prim.ident))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm Constr.cpattern)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ pat _ id _ loc -> 
# 737 "plugins/ltac2/g_ltac2.mlg"
                                               CAst.make ~loc @@ QConstrMatchContext (id, pat) 
                                                          )])]))
        in let () = assert (Pcoq.Entry.is_empty match_rule) in
        let () =
        Pcoq.grammar_extend match_rule
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm match_pattern)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                  ((Pcoq.Symbol.nterm ltac2_expr)))
                                  (fun tac _ mp loc -> 
# 742 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ (mp, tac) 
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
# 747 "plugins/ltac2/g_ltac2.mlg"
                                                 CAst.make ~loc @@ mrl 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm match_rule)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun mrl loc -> 
# 746 "plugins/ltac2/g_ltac2.mlg"
                                            CAst.make ~loc @@ mrl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty q_constr_matching) in
        let () =
        Pcoq.grammar_extend q_constr_matching
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm match_list)))
                                  (fun m loc -> 
# 750 "plugins/ltac2/g_ltac2.mlg"
                            m 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty gmatch_hyp_pattern)
        in
        let () =
        Pcoq.grammar_extend gmatch_hyp_pattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm Prim.name)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                  ((Pcoq.Symbol.nterm match_pattern)))
                                  (fun pat _ na loc -> 
# 753 "plugins/ltac2/g_ltac2.mlg"
                                                      (na, pat) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty gmatch_pattern) in
        let () =
        Pcoq.grammar_extend gmatch_pattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm gmatch_hyp_pattern)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                                  ((Pcoq.Symbol.nterm match_pattern)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                  (fun _ p _ hl _ loc -> 
# 757 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ {
          q_goal_match_concl = p;
          q_goal_match_hyps = hl;
        } 
                                                         )])]))
        in let () = assert (Pcoq.Entry.is_empty gmatch_rule) in
        let () =
        Pcoq.grammar_extend gmatch_rule
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm gmatch_pattern)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                  ((Pcoq.Symbol.nterm ltac2_expr)))
                                  (fun tac _ mp loc -> 
# 765 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc @@ (mp, tac) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty goal_match_list) in
        let () =
        Pcoq.grammar_extend goal_match_list
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm gmatch_rule)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                  (fun mrl _ loc -> 
# 770 "plugins/ltac2/g_ltac2.mlg"
                                                  CAst.make ~loc @@ mrl 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm gmatch_rule)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun mrl loc -> 
# 769 "plugins/ltac2/g_ltac2.mlg"
                                             CAst.make ~loc @@ mrl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty q_goal_matching) in
        let () =
        Pcoq.grammar_extend q_goal_matching
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm goal_match_list)))
                                  (fun m loc -> 
# 773 "plugins/ltac2/g_ltac2.mlg"
                                 m 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty move_location) in
        let () =
        Pcoq.grammar_extend move_location
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("before"))))))
                                                  ((Pcoq.Symbol.nterm ident_or_anti)))
                                  (fun id _ loc -> 
# 779 "plugins/ltac2/g_ltac2.mlg"
                                                CAst.make ~loc @@ QMoveBefore id 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("after"))))))
                                                 ((Pcoq.Symbol.nterm ident_or_anti)))
                                 (fun id _ loc -> 
# 778 "plugins/ltac2/g_ltac2.mlg"
                                               CAst.make ~loc @@ QMoveAfter id 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("bottom"))))))
                                 (fun _ _ loc -> 
# 777 "plugins/ltac2/g_ltac2.mlg"
                                  CAst.make ~loc @@ QMoveLast 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("top"))))))
                                 (fun _ _ loc -> 
# 776 "plugins/ltac2/g_ltac2.mlg"
                               CAst.make ~loc @@ QMoveFirst 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty q_move_location) in
        let () =
        Pcoq.grammar_extend q_move_location
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm move_location)))
                                  (fun mv loc -> 
# 783 "plugins/ltac2/g_ltac2.mlg"
                                mv 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty as_name) in
        let () =
        Pcoq.grammar_extend as_name
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                  ((Pcoq.Symbol.nterm ident_or_anti)))
                                  (fun id _ loc -> 
# 787 "plugins/ltac2/g_ltac2.mlg"
                                      Some id 
                                                   );
                                 Pcoq.Production.make (Pcoq.Rule.stop)
                                 (fun loc -> 
# 786 "plugins/ltac2/g_ltac2.mlg"
             None 
                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty pose) in
        let () =
        Pcoq.grammar_extend pose
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm Constr.constr)))
                                                  ((Pcoq.Symbol.nterm as_name)))
                                  (fun na c loc -> 
# 793 "plugins/ltac2/g_ltac2.mlg"
                                             CAst.make ~loc (na, c) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_coloneq)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm ident_or_anti)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm Constr.lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ id _ _ loc -> 
# 792 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc (Some id, c) 
                                                          )])]))
        in let () = assert (Pcoq.Entry.is_empty q_pose) in
        let () =
        Pcoq.grammar_extend q_pose
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm pose)))
                                  (fun p loc -> 
# 797 "plugins/ltac2/g_ltac2.mlg"
                      p 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty as_ipat) in
        let () =
        Pcoq.grammar_extend as_ipat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 801 "plugins/ltac2/g_ltac2.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm simple_intropattern)))
                                 (fun ipat _ loc -> 
# 800 "plugins/ltac2/g_ltac2.mlg"
                                              Some ipat 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty by_tactic) in
        let () =
        Pcoq.grammar_extend by_tactic
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 806 "plugins/ltac2/g_ltac2.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("by")))))
                                                 ((Pcoq.Symbol.nterm ltac2_expr)))
                                 (fun tac _ loc -> 
# 805 "plugins/ltac2/g_ltac2.mlg"
                                    Some tac 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty assertion) in
        let () =
        Pcoq.grammar_extend assertion
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm Constr.constr)))
                                                                  ((Pcoq.Symbol.nterm as_ipat)))
                                                  ((Pcoq.Symbol.nterm by_tactic)))
                                  (fun tac ipat c loc -> 
# 816 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc (QAssertType (ipat, c, tac)) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_colon)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm ident_or_anti)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm Constr.lconstr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun tac _ c _ id _ _ loc -> 
# 813 "plugins/ltac2/g_ltac2.mlg"
        let ipat = CAst.make ~loc @@ QIntroNaming (CAst.make ~loc @@ QIntroIdentifier id) in
        CAst.make ~loc (QAssertType (Some ipat, c, tac)) 
                                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_coloneq)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm ident_or_anti)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm Constr.lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ id _ _ loc -> 
# 811 "plugins/ltac2/g_ltac2.mlg"
          CAst.make ~loc (QAssertValue (id, c)) 
                                                          )])]))
        in let () = assert (Pcoq.Entry.is_empty q_assert) in
        let () =
        Pcoq.grammar_extend q_assert
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm assertion)))
                                  (fun a loc -> 
# 820 "plugins/ltac2/g_ltac2.mlg"
                           a 
                                                )])]))
        in ()


# 844 "plugins/ltac2/g_ltac2.mlg"
 

let () =

let open Tok in
let (++) r s = Pcoq.Rule.next r s in
let rules = [
  Pcoq.(
    Production.make
      (Rule.stop ++ Symbol.nterm test_dollar_ident ++ Symbol.token (PKEYWORD "$") ++ Symbol.nterm Prim.ident)
    begin fun id _ _ loc ->
      let id = Loc.tag ~loc id in
      let arg = Genarg.in_gen (Genarg.rawwit Tac2env.wit_ltac2_quotation) id in
      CAst.make ~loc (CHole (None, Namegen.IntroAnonymous, Some arg))
    end
  );

  Pcoq.(
    Production.make
      (Rule.stop ++ Symbol.nterm test_ampersand_ident ++ Symbol.token (PKEYWORD "&") ++ Symbol.nterm Prim.ident)
    begin fun id _ _ loc ->
      let tac = Tac2quote.of_exact_hyp ~loc (CAst.make ~loc id) in
      let arg = Genarg.in_gen (Genarg.rawwit Tac2env.wit_ltac2_constr) tac in
      CAst.make ~loc (CHole (None, Namegen.IntroAnonymous, Some arg))
    end
  );

  Pcoq.(
    Production.make
      (Rule.stop ++ Symbol.token (PIDENT (Some "ltac2")) ++ Symbol.token (PKEYWORD ":") ++
       Symbol.token (PKEYWORD "(") ++ Symbol.nterm ltac2_expr ++ Symbol.token (PKEYWORD ")"))
    begin fun _ tac _ _ _ loc ->
      let arg = Genarg.in_gen (Genarg.rawwit Tac2env.wit_ltac2_constr) tac in
      CAst.make ~loc (CHole (None, Namegen.IntroAnonymous, Some arg))
    end
  )
] in

Hook.set Tac2entries.register_constr_quotations begin fun () ->
  Pcoq.grammar_extend Pcoq.Constr.term (Pcoq.Reuse (Some"0", rules))
end




# 888 "plugins/ltac2/g_ltac2.mlg"
 

let pr_ltac2entry _ = mt () (* FIXME *)
let pr_ltac2expr _ = mt () (* FIXME *)



let (wit_ltac2_entry, ltac2_entry) = Vernacextend.vernac_argument_extend ~name:"ltac2_entry" 
                                     {
                                     Vernacextend.arg_parsing = Vernacextend.Arg_rules (
                                                                [(Pcoq.Production.make
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm tac2def_mut)))
                                                                  (fun e
                                                                  loc -> 
                                                                  
# 901 "plugins/ltac2/g_ltac2.mlg"
                          e 
                                                                  ));
                                                                (Pcoq.Production.make
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2def_syn)))
                                                                 (fun e
                                                                 loc -> 
                                                                 
# 900 "plugins/ltac2/g_ltac2.mlg"
                          e 
                                                                 ));
                                                                (Pcoq.Production.make
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2def_ext)))
                                                                 (fun e
                                                                 loc -> 
                                                                 
# 899 "plugins/ltac2/g_ltac2.mlg"
                          e 
                                                                 ));
                                                                (Pcoq.Production.make
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2def_typ)))
                                                                 (fun t
                                                                 loc -> 
                                                                 
# 898 "plugins/ltac2/g_ltac2.mlg"
                          t 
                                                                 ));
                                                                (Pcoq.Production.make
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm tac2def_val)))
                                                                 (fun v
                                                                 loc -> 
                                                                 
# 897 "plugins/ltac2/g_ltac2.mlg"
                          v 
                                                                 ))]);
                                     Vernacextend.arg_printer = fun env sigma -> 
                                     
# 896 "plugins/ltac2/g_ltac2.mlg"
             pr_ltac2entry 
                                     ;
                                     }
let _ = (wit_ltac2_entry, ltac2_entry)

let (wit_ltac2_expr, ltac2_expr) = Vernacextend.vernac_argument_extend ~name:"ltac2_expr" 
                                   {
                                   Vernacextend.arg_parsing = Vernacextend.Arg_alias (_ltac2_expr);
                                   Vernacextend.arg_printer = fun env sigma -> 
                                   
# 905 "plugins/ltac2/g_ltac2.mlg"
             pr_ltac2expr 
                                   ;
                                   }
let _ = (wit_ltac2_expr, ltac2_expr)


# 909 "plugins/ltac2/g_ltac2.mlg"
 

let classify_ltac2 = function
| StrSyn _ -> Vernacextend.(VtSideff ([], VtNow))
| StrMut _ | StrVal _ | StrPrm _  | StrTyp _ -> Vernacextend.classify_as_sideeff



let () = Vernacextend.vernac_extend ~command:"VernacDeclareTactic2Definition"  ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Ltac2", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ltac2_entry), 
                                     Vernacextend.TyNil)), (let coqpp_body e
                                                           raw_attributes = 
                                                           Vernacextend.vtdefault (fun () -> 
                                                           
# 918 "plugins/ltac2/g_ltac2.mlg"
                                                                             
  Tac2entries.register_struct raw_attributes e
  
                                                           ) in fun e
                                                           ?loc ~atts ()
                                                           -> coqpp_body e
                                                           (Attributes.parse raw_attributes atts)), Some 
         (fun e -> 
# 918 "plugins/ltac2/g_ltac2.mlg"
                                                      classify_ltac2 e 
         )));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("Ltac2", 
                                    Vernacextend.TyTerminal ("Eval", 
                                    Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ltac2_expr), 
                                    Vernacextend.TyNil))), (let coqpp_body e
                                                           () = Vernacextend.vtreadproofopt (
                                                                
# 921 "plugins/ltac2/g_ltac2.mlg"
                                                                                                
  fun ~pstate -> Tac2entries.perform_eval ~pstate e
  
                                                                ) in fun e
                                                           ?loc ~atts ()
                                                           -> coqpp_body e
                                                           (Attributes.unsupported_attributes atts)), Some 
         (fun e -> 
# 921 "plugins/ltac2/g_ltac2.mlg"
                                                           Vernacextend.classify_as_query 
         )))]


# 926 "plugins/ltac2/g_ltac2.mlg"
 

let _ = Pvernac.register_proof_mode "Ltac2" tac2mode

open G_ltac
open Vernacextend



let () = Vernacextend.vernac_extend ~command:"VernacLtac2"  ?entry:(Some ( tac2mode )) 
         [(Vernacextend.TyML (false, Vernacextend.TyNonTerminal (Extend.TUopt (
                                                                 Extend.TUentry (Genarg.get_arg_tag wit_ltac_selector)), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ltac2_expr), 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_ltac_use_default), 
                                     Vernacextend.TyNil))), (let coqpp_body g
                                                            t with_end_tac
                                                            () = Vernacextend.vtmodifyproof (
                                                                 
# 937 "plugins/ltac2/g_ltac2.mlg"
                                 fun ~pstate ->
    Tac2entries.call ~pstate g ~with_end_tac t
  
                                                                 ) in fun g
                                                            t with_end_tac
                                                            ?loc ~atts ()
                                                            -> coqpp_body g t
                                                            with_end_tac
                                                            (Attributes.unsupported_attributes atts)), Some 
         (fun g t with_end_tac -> 
# 937 "plugins/ltac2/g_ltac2.mlg"
    classify_as_proofstep 
         )));
         (Vernacextend.TyML (false, Vernacextend.TyTerminal ("par", Vernacextend.TyTerminal (":", 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ltac2_expr), 
                                                                    Vernacextend.TyNonTerminal (
                                                                    Extend.TUentry (Genarg.get_arg_tag wit_ltac_use_default), 
                                                                    Vernacextend.TyNil)))), 
         (let coqpp_body t with_end_tac
         () = Vernacextend.vtmodifyproof (
# 941 "plugins/ltac2/g_ltac2.mlg"
                                 fun ~pstate ->
    Tac2entries.call_par ~pstate ~with_end_tac t
  
              ) in fun t
         with_end_tac ?loc ~atts () -> coqpp_body t with_end_tac
         (Attributes.unsupported_attributes atts)), Some (fun t with_end_tac
                                                         -> 
# 941 "plugins/ltac2/g_ltac2.mlg"
    classify_as_proofstep 
                                                         )))]

let _ = let () =
        Pcoq.grammar_extend tac2mode
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.stop)
                                            ((Pcoq.Symbol.nterm G_vernac.query_command)))
                            (fun tac loc -> 
# 949 "plugins/ltac2/g_ltac2.mlg"
                                          tac None 
                                            )]))
        in ()


# 952 "plugins/ltac2/g_ltac2.mlg"
 

open Stdarg



let () = Vernacextend.vernac_extend ~command:"Ltac2Print" ~classifier:(fun _ -> Vernacextend.classify_as_sideeff) ?entry:None 
         [(Vernacextend.TyML (false, Vernacextend.TyTerminal ("Print", 
                                     Vernacextend.TyTerminal ("Ltac2", 
                                     Vernacextend.TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag wit_reference), 
                                     Vernacextend.TyNil))), (let coqpp_body tac
                                                            () = Vernacextend.vtdefault (fun () -> 
                                                                 
# 959 "plugins/ltac2/g_ltac2.mlg"
                                          Tac2entries.print_ltac tac 
                                                                 ) in fun tac
                                                            ?loc ~atts ()
                                                            -> coqpp_body tac
                                                            (Attributes.unsupported_attributes atts)), None))]

