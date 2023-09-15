
# 11 "parsing/g_constr.mlg"
 

open Names
open Constr
open Libnames
open Glob_term
open Constrexpr
open Constrexpr_ops
open Util
open Namegen

open Pcoq
open Pcoq.Prim
open Pcoq.Constr

(* TODO: avoid this redefinition without an extra dep to Notation_ops *)
let ldots_var = Id.of_string ".."

let mk_cast = function
    (c,(_,None)) -> c
  | (c,(_,Some ty)) ->
    let loc = Loc.merge_opt (constr_loc c) (constr_loc ty)
    in CAst.make ?loc @@ CCast(c, DEFAULTcast, ty)

let binder_of_name expl { CAst.loc = loc; v = na } =
  CLocalAssum ([CAst.make ?loc na], Default expl,
    CAst.make ?loc @@ CHole (Some (Evar_kinds.BinderType na), IntroAnonymous, None))

let binders_of_names l =
  List.map (binder_of_name Explicit) l

let pat_of_name CAst.{loc;v} = match v with
| Anonymous -> CAst.make ?loc @@ CPatAtom None
| Name id -> CAst.make ?loc @@ CPatAtom (Some (qualid_of_ident id))

let err () = raise Stream.Failure

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let test_lpar_id_coloneq =
  let open Pcoq.Lookahead in
  to_entry "test_lpar_id_coloneq" begin
    lk_kw "(" >> lk_ident >> lk_kw ":="
  end

(* Hack to parse "(n:=t)" as an explicit argument without conflicts with the *)
(* syntax "(n t)" *)
let test_lpar_nat_coloneq =
  let open Pcoq.Lookahead in
  to_entry "test_lpar_id_coloneq" begin
    lk_kw "(" >> lk_nat >> lk_kw ":="
  end

let ensure_fixannot =
  let open Pcoq.Lookahead in
  to_entry "check_fixannot" begin
    lk_kw "{" >> lk_kws ["wf"; "struct"; "measure"]
  end

let lk_name = Pcoq.Lookahead.(lk_ident <+> lk_kw "_")

let test_name_colon =
  let open Pcoq.Lookahead in
  to_entry "test_name_colon" begin
    lk_name >> lk_kw ":"
  end

let aliasvar = function { CAst.v = CPatAlias (_, na) } -> Some na | _ -> None

let test_array_opening =
  let open Pcoq.Lookahead in
  to_entry "test_array_opening" begin
    lk_kw "[" >> lk_kw "|" >> check_no_space
  end

let test_array_closing =
  let open Pcoq.Lookahead in
  to_entry "test_array_closing" begin
    lk_kw "|" >> lk_kw "]" >> check_no_space
  end



let _ = let universe_increment = Pcoq.Entry.make "universe_increment"
        and universe_expr = Pcoq.Entry.make "universe_expr"
        and universe = Pcoq.Entry.make "universe"
        and array_elems = Pcoq.Entry.make "array_elems"
        and fields_def = Pcoq.Entry.make "fields_def"
        and field_def = Pcoq.Entry.make "field_def"
        and atomic_constr = Pcoq.Entry.make "atomic_constr"
        and inst = Pcoq.Entry.make "inst"
        and evar_instance = Pcoq.Entry.make "evar_instance"
        and univ_annot = Pcoq.Entry.make "univ_annot"
        and fix_decls = Pcoq.Entry.make "fix_decls"
        and cofix_decls = Pcoq.Entry.make "cofix_decls"
        and fix_decl = Pcoq.Entry.make "fix_decl"
        and cofix_body = Pcoq.Entry.make "cofix_body"
        and term_match = Pcoq.Entry.make "term_match"
        and case_item = Pcoq.Entry.make "case_item"
        and case_type = Pcoq.Entry.make "case_type"
        and as_return_type = Pcoq.Entry.make "as_return_type"
        and branches = Pcoq.Entry.make "branches"
        and mult_pattern = Pcoq.Entry.make "mult_pattern"
        and eqn = Pcoq.Entry.make "eqn"
        and record_pattern = Pcoq.Entry.make "record_pattern"
        and record_patterns = Pcoq.Entry.make "record_patterns"
        and fixannot = Pcoq.Entry.make "fixannot"
        and let_type_cstr = Pcoq.Entry.make "let_type_cstr"
        in
        let () = assert (Pcoq.Entry.is_empty Constr.ident) in
        let () =
        Pcoq.grammar_extend Constr.ident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.ident)))
                                  (fun id loc -> 
# 102 "parsing/g_constr.mlg"
                             id 
                                                 )])]))
        in let () =
        Pcoq.grammar_extend Prim.name
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.stop)
                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                            (fun _ loc -> 
# 105 "parsing/g_constr.mlg"
                 CAst.make ~loc Anonymous 
                                          )]))
        in let () = assert (Pcoq.Entry.is_empty global) in
        let () =
        Pcoq.grammar_extend global
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Prim.reference)))
                                  (fun r loc -> 
# 108 "parsing/g_constr.mlg"
                                r 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty constr_pattern) in
        let () =
        Pcoq.grammar_extend constr_pattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr)))
                                  (fun c loc -> 
# 111 "parsing/g_constr.mlg"
                        c 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty cpattern) in
        let () =
        Pcoq.grammar_extend cpattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun c loc -> 
# 114 "parsing/g_constr.mlg"
                         c 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty sort) in
        let () =
        Pcoq.grammar_extend sort
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("@{")))))
                                                                  ((Pcoq.Symbol.nterm universe)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                  (fun _ u _ _ loc -> 
# 122 "parsing/g_constr.mlg"
                                             UNamed u 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("@{")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ _ _ _ loc -> 
# 121 "parsing/g_constr.mlg"
                                    UAnonymous {rigid=false} 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                 (fun _ loc -> 
# 120 "parsing/g_constr.mlg"
                    UAnonymous {rigid=true} 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("SProp")))))
                                 (fun _ loc -> 
# 119 "parsing/g_constr.mlg"
                     UNamed [CSProp,0] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Prop")))))
                                 (fun _ loc -> 
# 118 "parsing/g_constr.mlg"
                    UNamed [CProp,0] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Set")))))
                                 (fun _ loc -> 
# 117 "parsing/g_constr.mlg"
                    UNamed [CSet,0] 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty sort_family) in
        let () =
        Pcoq.grammar_extend sort_family
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                  (fun _ loc -> 
# 128 "parsing/g_constr.mlg"
                    Sorts.InType 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("SProp")))))
                                 (fun _ loc -> 
# 127 "parsing/g_constr.mlg"
                     Sorts.InSProp 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Prop")))))
                                 (fun _ loc -> 
# 126 "parsing/g_constr.mlg"
                    Sorts.InProp 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Set")))))
                                 (fun _ loc -> 
# 125 "parsing/g_constr.mlg"
                    Sorts.InSet 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty universe_increment)
        in
        let () =
        Pcoq.grammar_extend universe_increment
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 132 "parsing/g_constr.mlg"
             0 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n _ loc -> 
# 131 "parsing/g_constr.mlg"
                              n 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty universe_name) in
        let () =
        Pcoq.grammar_extend universe_name
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("Prop")))))
                                  (fun _ loc -> 
# 137 "parsing/g_constr.mlg"
                    CProp 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Set")))))
                                 (fun _ loc -> 
# 136 "parsing/g_constr.mlg"
                    CSet 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm global)))
                                 (fun id loc -> 
# 135 "parsing/g_constr.mlg"
                         CType id 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty universe_expr) in
        let () =
        Pcoq.grammar_extend universe_expr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm universe_name)))
                                                  ((Pcoq.Symbol.nterm universe_increment)))
                                  (fun n id loc -> 
# 140 "parsing/g_constr.mlg"
                                                        (id,n) 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty universe) in
        let () =
        Pcoq.grammar_extend universe
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm universe_expr)))
                                  (fun u loc -> 
# 144 "parsing/g_constr.mlg"
                               [u] 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("max"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm universe_expr)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ ids _ _ loc -> 
# 143 "parsing/g_constr.mlg"
                                                                      ids 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty lconstr) in
        let () =
        Pcoq.grammar_extend lconstr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterml term ("200"))))
                                  (fun c loc -> 
# 147 "parsing/g_constr.mlg"
                                  c 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty constr) in
        let () =
        Pcoq.grammar_extend constr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("@")))))
                                                                  ((Pcoq.Symbol.nterm global)))
                                                  ((Pcoq.Symbol.nterm univ_annot)))
                                  (fun i f _ loc -> 
# 151 "parsing/g_constr.mlg"
                                           CAst.make ~loc @@ CAppExpl((f,i),[]) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterml term ("8"))))
                                 (fun c loc -> 
# 150 "parsing/g_constr.mlg"
                                c 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty term) in
        let () =
        Pcoq.grammar_extend term
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(Some ("200"), Some
                                 (Gramlib.Gramext.RightA),
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm binder_constr)))
                                  (fun c loc -> 
# 155 "parsing/g_constr.mlg"
                               c 
                                                )]);
                                (Some ("100"), Some (Gramlib.Gramext.RightA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm term)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c2 _ c1 loc -> 
# 162 "parsing/g_constr.mlg"
                   CAst.make ~loc @@ CCast(c1, DEFAULTcast, c2) 
                                                     );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm term)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("<<:")))))
                                                ((Pcoq.Symbol.nterml term ("200"))))
                                (fun c2 _ c1 loc -> 
# 160 "parsing/g_constr.mlg"
                   CAst.make ~loc @@ CCast(c1, NATIVEcast, c2) 
                                                    );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm term)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("<:")))))
                                                ((Pcoq.Symbol.nterml term ("200"))))
                                (fun c2 _ c1 loc -> 
# 158 "parsing/g_constr.mlg"
                   CAst.make ~loc @@ CCast(c1, VMcast, c2) 
                                                    )]);
                                (Some ("99"), Some (Gramlib.Gramext.RightA),
                                []);
                                (Some ("90"), Some (Gramlib.Gramext.RightA),
                                []);
                                (Some ("10"), Some (Gramlib.Gramext.LeftA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("@")))))
                                                                 ((Pcoq.Symbol.nterm pattern_ident)))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm identref)))))
                                 (fun args lid _ loc -> 
# 169 "parsing/g_constr.mlg"
          let { CAst.loc = locid; v = id } = lid in
          let args = List.map (fun x -> CAst.make @@ CRef (qualid_of_ident ?loc:x.CAst.loc x.CAst.v, None), None) args in
          CAst.make ~loc @@ CApp(CAst.make ?loc:locid @@ CPatVar id,args) 
                                                        );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("@")))))
                                                                ((Pcoq.Symbol.nterm global)))
                                                                ((Pcoq.Symbol.nterm univ_annot)))
                                                ((Pcoq.Symbol.list0 Pcoq.Symbol.next)))
                                (fun args i f _ loc -> 
# 167 "parsing/g_constr.mlg"
                                                                CAst.make ~loc @@ CAppExpl((f,i),args) 
                                                       );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm term)))
                                                ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm arg)))))
                                (fun args f loc -> 
# 166 "parsing/g_constr.mlg"
                                        CAst.make ~loc @@ CApp(f,args) 
                                                   )]);
                                (Some ("9"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("..")))))
                                                                 ((Pcoq.Symbol.nterml term ("0"))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("..")))))
                                 (fun _ c _ loc -> 
# 174 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CAppExpl ((qualid_of_ident ~loc ldots_var, None),[c]) 
                                                   )]);
                                (Some ("8"), None, []);
                                (Some ("1"), Some (Gramlib.Gramext.LeftA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm term)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("%")))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun key _ c loc -> 
# 182 "parsing/g_constr.mlg"
                                        CAst.make ~loc @@ CDelimiters (key,c) 
                                                     );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm term)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (".(")))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("@")))))
                                                                ((Pcoq.Symbol.nterm global)))
                                                                ((Pcoq.Symbol.nterm univ_annot)))
                                                                ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterml term ("9")))))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ args i f _ _ c loc -> 
# 181 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CProj(true, (f,i), List.map (fun a -> (a,None)) args, c) 
                                                             );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm term)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (".(")))))
                                                                ((Pcoq.Symbol.nterm global)))
                                                                ((Pcoq.Symbol.nterm univ_annot)))
                                                                ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm arg))))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ args i f _ c loc -> 
# 178 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CProj(false, (f,i), args, c) 
                                                           )]);
                                (Some ("0"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("`(")))))
                                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ loc -> 
# 209 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CGeneralization (Explicit, c) 
                                                   );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm test_array_opening)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                                ((Pcoq.Symbol.nterm array_elems)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                                ((Pcoq.Symbol.nterm lconstr)))
                                                                ((Pcoq.Symbol.nterm type_cstr)))
                                                                ((Pcoq.Symbol.nterm test_array_closing)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                                ((Pcoq.Symbol.nterm univ_annot)))
                                (fun u _ _ _ ty def _ ls _ _ _ loc -> 
# 204 "parsing/g_constr.mlg"
          let t = Array.make (List.length ls) def in
          List.iteri (fun i e -> t.(i) <- e) ls;
          CAst.make ~loc @@ CArray(u, t, def, ty)
        
                                                                    );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("`{")))))
                                                                ((Pcoq.Symbol.nterml term ("200"))))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                (fun _ c _ loc -> 
# 202 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CGeneralization (MaxImplicit, c) 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                ((Pcoq.Symbol.nterm binder_constr)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                (fun _ c _ loc -> 
# 200 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CNotation(None,(InConstrEntry,"{ _ }"),([c],[],[],[])) 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("{|")))))
                                                                ((Pcoq.Symbol.nterm record_declaration)))
                                                ((Pcoq.Symbol.nterm bar_cbrace)))
                                (fun _ c _ loc -> 
# 198 "parsing/g_constr.mlg"
                                                      c 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                ((Pcoq.Symbol.nterml term ("200"))))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ c _ loc -> 
# 192 "parsing/g_constr.mlg"
          (* Preserve parentheses around numbers so that constrintern does not
             collapse -(3) into the number -3. *)
          (match c.CAst.v with
            | CPrim (Number (NumTok.SPlus,n)) ->
                CAst.make ~loc @@ CNotation(None,(InConstrEntry,"( _ )"),([c],[],[],[]))
            | _ -> c) 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PNUMBER None))))
                                (fun n loc -> 
# 190 "parsing/g_constr.mlg"
                       CAst.make ~loc @@ CPrim (Number (NumTok.SPlus,n)) 
                                              );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ident)))
                                                ((Pcoq.Symbol.nterm univ_annot)))
                                (fun i id loc -> 
# 189 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CRef (qualid_of_ident ~loc id, i) 
                                                 );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ident)))
                                                                ((Pcoq.Symbol.nterm Prim.fields)))
                                                ((Pcoq.Symbol.nterm univ_annot)))
                                (fun i f id loc -> 
# 187 "parsing/g_constr.mlg"
          let (l,id') = f in CAst.make ~loc @@ CRef (make_qualid ~loc (DirPath.make (l@[id])) id', i) 
                                                   );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm term_match)))
                                (fun c loc -> 
# 185 "parsing/g_constr.mlg"
                            c 
                                              );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm atomic_constr)))
                                (fun c loc -> 
# 184 "parsing/g_constr.mlg"
                               c 
                                              )])]))
        in let () = assert (Pcoq.Entry.is_empty array_elems) in
        let () =
        Pcoq.grammar_extend array_elems
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm lconstr)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (";"))])) false)))
                                  (fun fs loc -> 
# 212 "parsing/g_constr.mlg"
                                        fs 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty record_declaration)
        in
        let () =
        Pcoq.grammar_extend record_declaration
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm fields_def)))
                                  (fun fs loc -> 
# 215 "parsing/g_constr.mlg"
                             CAst.make ~loc @@ CRecord fs 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty fields_def) in
        let () =
        Pcoq.grammar_extend fields_def
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 220 "parsing/g_constr.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm field_def)))
                                 (fun f loc -> 
# 219 "parsing/g_constr.mlg"
                           [f] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm field_def)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                 ((Pcoq.Symbol.nterm fields_def)))
                                 (fun fs _ f loc -> 
# 218 "parsing/g_constr.mlg"
                                                 f :: fs 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty field_def) in
        let () =
        Pcoq.grammar_extend field_def
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm global)))
                                                                  ((Pcoq.Symbol.nterm binders)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun c _ bl id loc -> 
# 224 "parsing/g_constr.mlg"
          (id, mkLambdaCN ~loc bl c) 
                                                        )])]))
        in let () = assert (Pcoq.Entry.is_empty binder_constr) in
        let () =
        Pcoq.grammar_extend binder_constr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("cofix")))))
                                                  ((Pcoq.Symbol.nterm cofix_decls)))
                                  (fun c _ loc -> 
# 268 "parsing/g_constr.mlg"
                                      let (id,dcls) = c in CAst.make ~loc @@ CCoFix (id,dcls) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("fix")))))
                                                 ((Pcoq.Symbol.nterm fix_decls)))
                                 (fun c _ loc -> 
# 267 "parsing/g_constr.mlg"
                                  let (id,dcls) = c in CAst.make ~loc @@ CFix (id,dcls) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("if")))))
                                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                                                 ((Pcoq.Symbol.nterm as_return_type)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("then")))))
                                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("else")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun b2 _ b1 _ po c _ loc -> 
# 266 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CIf (c, po, b1, b2) 
                                                              );
                                 Pcoq.Production.make
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
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("'")))))
                                                                 ((Pcoq.Symbol.nterml pattern ("200"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                                 ((Pcoq.Symbol.nterml pattern ("200"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                                                 ((Pcoq.Symbol.nterm case_type)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c2 _ rt c1 _ t _ p _ _ loc -> 
# 261 "parsing/g_constr.mlg"
          CAst.make ~loc @@
          CCases (LetPatternStyle, Some rt, [c1, aliasvar p, Some t], [CAst.make ~loc ([[p]], c2)]) 
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
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("'")))))
                                                                 ((Pcoq.Symbol.nterml pattern ("200"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                                                 ((Pcoq.Symbol.nterm case_type)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c2 _ rt c1 _ p _ _ loc -> 
# 256 "parsing/g_constr.mlg"
          CAst.make ~loc @@
          CCases (LetPatternStyle, Some rt, [c1, aliasvar p, None], [CAst.make ~loc ([[p]], c2)]) 
                                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("let")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("'")))))
                                                                 ((Pcoq.Symbol.nterml pattern ("200"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c2 _ c1 _ p _ _ loc -> 
# 252 "parsing/g_constr.mlg"
          CAst.make ~loc @@
          CCases (LetPatternStyle, None,    [c1, None, None],       [CAst.make ~loc ([[p]], c2)]) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("let")))))
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("()")))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 246 "parsing/g_constr.mlg"
                                                                         [] 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm name)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                                 (fun _ l _
                                                                 loc -> 
                                                                 
# 246 "parsing/g_constr.mlg"
                                                         l 
                                                                 )])))
                                                                 ((Pcoq.Symbol.nterm as_return_type)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c2 _ c1 _ po lb _ loc -> 
# 249 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CLetTuple (lb,po,c1,c2) 
                                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("let")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("cofix")))))
                                                                 ((Pcoq.Symbol.nterm cofix_body)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c _ fx _ _ loc -> 
# 243 "parsing/g_constr.mlg"
          let {CAst.loc=locf;CAst.v=({CAst.loc=li;CAst.v=id} as lid,_,_,_ as dcl)} = fx in
          let cofix = CAst.make ?loc:locf @@ CCoFix (lid,[dcl]) in
          CAst.make ~loc @@ CLetIn( CAst.make ?loc:li @@ Name id,cofix,None,c) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("let")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("fix")))))
                                                                 ((Pcoq.Symbol.nterm fix_decl)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c _ fx _ _ loc -> 
# 239 "parsing/g_constr.mlg"
          let {CAst.loc=locf;CAst.v=({CAst.loc=li;CAst.v=id} as lid,_,_,_,_ as dcl)} = fx in
          let fix = CAst.make ?loc:locf @@ CFix (lid,[dcl]) in
          CAst.make ~loc @@ CLetIn( CAst.make ?loc:li @@ Name id,fix,None,c) 
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
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.nterm binders)))
                                                                 ((Pcoq.Symbol.nterm let_type_cstr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c2 _ c1 _ ty bl id _ loc -> 
# 233 "parsing/g_constr.mlg"
          let ty,c1 = match ty, c1 with
          | (_,None), { CAst.v = CCast(c, DEFAULTcast, t) } -> (Loc.tag ?loc:(constr_loc t) @@ Some t), c (* Tolerance, see G_vernac.def_body *)
          | _, _ -> ty, c1 in
          CAst.make ~loc @@ CLetIn(id,mkLambdaCN ?loc:(constr_loc c1) bl c1,
                 Option.map (mkProdCN ?loc:(fst ty) bl) (snd ty), c2) 
                                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("fun")))))
                                                                 ((Pcoq.Symbol.nterm open_binders)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c _ bl _ loc -> 
# 230 "parsing/g_constr.mlg"
          mkLambdaCN ~loc bl c 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("forall")))))
                                                                 ((Pcoq.Symbol.nterm open_binders)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c _ bl _ loc -> 
# 228 "parsing/g_constr.mlg"
          mkProdCN ~loc bl c 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty arg) in
        let () =
        Pcoq.grammar_extend arg
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterml term ("9"))))
                                  (fun c loc -> 
# 273 "parsing/g_constr.mlg"
                              (c,None) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_lpar_nat_coloneq)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ n _ _ loc -> 
# 272 "parsing/g_constr.mlg"
                                                                             (c,Some (CAst.make ~loc @@ ExplByPos n)) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_coloneq)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ id _ _ loc -> 
# 271 "parsing/g_constr.mlg"
                                                                              (c,Some (CAst.make ?loc:id.CAst.loc @@ ExplByName id.CAst.v)) 
                                                          )])]))
        in let () = assert (Pcoq.Entry.is_empty atomic_constr) in
        let () =
        Pcoq.grammar_extend atomic_constr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm pattern_ident)))
                                                  ((Pcoq.Symbol.nterm evar_instance)))
                                  (fun inst id loc -> 
# 281 "parsing/g_constr.mlg"
                                                      CAst.make ~loc @@ CEvar(id,inst) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm pattern_ident)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ id _ _ loc -> 
# 280 "parsing/g_constr.mlg"
                                                CAst.make ~loc @@  CHole (None, IntroFresh id.CAst.v, None) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ id _ _ loc -> 
# 279 "parsing/g_constr.mlg"
                                           CAst.make ~loc @@  CHole (None, IntroIdentifier id.CAst.v, None) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                 (fun _ loc -> 
# 278 "parsing/g_constr.mlg"
                      CAst.make ~loc @@ CHole (None, IntroAnonymous, None) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm string)))
                                 (fun s loc -> 
# 277 "parsing/g_constr.mlg"
                        CAst.make ~loc @@ CPrim (String s) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm sort)))
                                 (fun s loc -> 
# 276 "parsing/g_constr.mlg"
                        CAst.make ~loc @@ CSort s 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty inst) in
        let () =
        Pcoq.grammar_extend inst
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm identref)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun c _ id loc -> 
# 284 "parsing/g_constr.mlg"
                                              (id,c) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty evar_instance) in
        let () =
        Pcoq.grammar_extend evar_instance
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 288 "parsing/g_constr.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("@{")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm inst)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (";"))])) false)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ l _ loc -> 
# 287 "parsing/g_constr.mlg"
                                               l 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty univ_annot) in
        let () =
        Pcoq.grammar_extend univ_annot
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 292 "parsing/g_constr.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("@{")))))
                                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm universe_level))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ l _ loc -> 
# 291 "parsing/g_constr.mlg"
                                                 Some l 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty universe_level) in
        let () =
        Pcoq.grammar_extend universe_level
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm global)))
                                  (fun id loc -> 
# 300 "parsing/g_constr.mlg"
                         UNamed (CType id) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                 (fun _ loc -> 
# 299 "parsing/g_constr.mlg"
                 UAnonymous {rigid=false} 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                 (fun _ loc -> 
# 298 "parsing/g_constr.mlg"
                    UAnonymous {rigid=true} 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Prop")))))
                                 (fun _ loc -> 
# 297 "parsing/g_constr.mlg"
                    UNamed CProp 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Set")))))
                                 (fun _ loc -> 
# 295 "parsing/g_constr.mlg"
                   UNamed CSet 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty fix_decls) in
        let () =
        Pcoq.grammar_extend fix_decls
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm fix_decl)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm fix_decl)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("for")))))
                                                  ((Pcoq.Symbol.nterm identref)))
                                  (fun id _ dcls _ dcl loc -> 
# 305 "parsing/g_constr.mlg"
          (id,List.map (fun x -> x.CAst.v) (dcl::dcls)) 
                                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm fix_decl)))
                                 (fun dcl loc -> 
# 303 "parsing/g_constr.mlg"
                            let (id,_,_,_,_) = dcl.CAst.v in (id,[dcl.CAst.v]) 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty cofix_decls) in
        let () =
        Pcoq.grammar_extend cofix_decls
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm cofix_body)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm cofix_body)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("for")))))
                                                  ((Pcoq.Symbol.nterm identref)))
                                  (fun id _ dcls _ dcl loc -> 
# 310 "parsing/g_constr.mlg"
          (id,List.map (fun x -> x.CAst.v) (dcl::dcls)) 
                                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm cofix_body)))
                                 (fun dcl loc -> 
# 308 "parsing/g_constr.mlg"
                              let (id,_,_,_) = dcl.CAst.v in (id,[dcl.CAst.v]) 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty fix_decl) in
        let () =
        Pcoq.grammar_extend fix_decl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm identref)))
                                                                  ((Pcoq.Symbol.nterm binders_fixannot)))
                                                                  ((Pcoq.Symbol.nterm type_cstr)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterml term ("200"))))
                                  (fun c _ ty bl id loc -> 
# 315 "parsing/g_constr.mlg"
          CAst.make ~loc (id,snd bl,fst bl,ty,c) 
                                                           )])]))
        in let () = assert (Pcoq.Entry.is_empty cofix_body) in
        let () =
        Pcoq.grammar_extend cofix_body
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm identref)))
                                                                  ((Pcoq.Symbol.nterm binders)))
                                                                  ((Pcoq.Symbol.nterm type_cstr)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterml term ("200"))))
                                  (fun c _ ty bl id loc -> 
# 320 "parsing/g_constr.mlg"
          CAst.make ~loc (id,bl,ty,c) 
                                                           )])]))
        in let () = assert (Pcoq.Entry.is_empty term_match) in
        let () =
        Pcoq.grammar_extend term_match
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("match")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm case_item)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm case_type))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                                  ((Pcoq.Symbol.nterm branches)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("end")))))
                                  (fun _ br _ ty ci _ loc -> 
# 324 "parsing/g_constr.mlg"
                                  CAst.make ~loc @@ CCases(RegularStyle,ty,ci,br) 
                                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty case_item) in
        let () =
        Pcoq.grammar_extend case_item
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterml term ("100"))))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                                  ((Pcoq.Symbol.nterm name)))
                                                                  (fun id _
                                                                  loc -> 
                                                                  
# 328 "parsing/g_constr.mlg"
                                        id 
                                                                  )]))))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                                   ((Pcoq.Symbol.nterml pattern ("200"))))
                                                                   (fun t _
                                                                   loc -> 
                                                                   
# 329 "parsing/g_constr.mlg"
                                                     t 
                                                                   )]))))
                                  (fun ty ona c loc -> 
# 330 "parsing/g_constr.mlg"
          (c,ona,ty) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty case_type) in
        let () =
        Pcoq.grammar_extend case_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("return")))))
                                                  ((Pcoq.Symbol.nterml term ("100"))))
                                  (fun ty _ loc -> 
# 333 "parsing/g_constr.mlg"
                                             ty 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty as_return_type) in
        let () =
        Pcoq.grammar_extend as_return_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                   [Pcoq.Rules.make 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                                   ((Pcoq.Symbol.nterm name)))
                                                                   (fun na _
                                                                   loc -> 
                                                                   
# 336 "parsing/g_constr.mlg"
                                                 na 
                                                                   )]))))
                                                                   ((Pcoq.Symbol.nterm case_type)))
                                                                   (fun ty na
                                                                   loc -> 
                                                                   
# 337 "parsing/g_constr.mlg"
                                      (na,ty) 
                                                                   )]))))
                                  (fun a loc -> 
# 338 "parsing/g_constr.mlg"
          match a with
          | None -> None, None
          | Some (na,t) -> (na, Some t) 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty branches) in
        let () =
        Pcoq.grammar_extend branches
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.token (Tok.PKEYWORD ("|"))))))
                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm eqn)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                  (fun br _ loc -> 
# 343 "parsing/g_constr.mlg"
                                            br 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty mult_pattern) in
        let () =
        Pcoq.grammar_extend mult_pattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterml pattern ("200"))) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                  (fun pl loc -> 
# 346 "parsing/g_constr.mlg"
                                                    pl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty eqn) in
        let () =
        Pcoq.grammar_extend eqn
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm mult_pattern)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("=>")))))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun rhs _ pll loc -> 
# 350 "parsing/g_constr.mlg"
                                 (CAst.make ~loc (pll,rhs)) 
                                                        )])]))
        in let () = assert (Pcoq.Entry.is_empty record_pattern) in
        let () =
        Pcoq.grammar_extend record_pattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm global)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterml pattern ("200"))))
                                  (fun pat _ id loc -> 
# 353 "parsing/g_constr.mlg"
                                                          (id, pat) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty record_patterns) in
        let () =
        Pcoq.grammar_extend record_patterns
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 358 "parsing/g_constr.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm record_pattern)))
                                 (fun p loc -> 
# 357 "parsing/g_constr.mlg"
                               [p] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm record_pattern)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                 ((Pcoq.Symbol.nterm record_patterns)))
                                 (fun ps _ p loc -> 
# 356 "parsing/g_constr.mlg"
                                                           p :: ps 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty pattern) in
        let () =
        Pcoq.grammar_extend pattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(Some ("200"), Some
                                 (Gramlib.Gramext.RightA), []);
                                (Some ("100"), Some (Gramlib.Gramext.RightA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm pattern)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun ty _ p loc -> 
# 364 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CPatCast (p, ty) 
                                                    )]);
                                (Some ("99"), Some (Gramlib.Gramext.RightA),
                                []);
                                (Some ("90"), Some (Gramlib.Gramext.RightA),
                                []);
                                (Some ("10"), Some (Gramlib.Gramext.LeftA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("@")))))
                                                                 ((Pcoq.Symbol.nterm Prim.reference)))
                                                 ((Pcoq.Symbol.list0 Pcoq.Symbol.next)))
                                 (fun lp r _ loc -> 
# 372 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CPatCstr (r, Some lp, []) 
                                                    );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm pattern)))
                                                ((Pcoq.Symbol.list1 (Pcoq.Symbol.next))))
                                (fun lp p loc -> 
# 370 "parsing/g_constr.mlg"
                                          mkAppPattern ~loc p lp 
                                                 );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm pattern)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                ((Pcoq.Symbol.nterm name)))
                                (fun na _ p loc -> 
# 369 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CPatAlias (p, na) 
                                                   )]);
                                (Some ("1"), Some (Gramlib.Gramext.LeftA),
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm pattern)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("%")))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun key _ c loc -> 
# 374 "parsing/g_constr.mlg"
                                           CAst.make ~loc @@ CPatDelimiters (key,c) 
                                                     )]);
                                (Some ("0"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm string)))
                                 (fun s loc -> 
# 389 "parsing/g_constr.mlg"
                        CAst.make ~loc @@ CPatPrim (String s) 
                                               );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PNUMBER None))))
                                (fun n loc -> 
# 388 "parsing/g_constr.mlg"
                       CAst.make ~loc @@ CPatPrim (Number (NumTok.SPlus,n)) 
                                              );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                ((Pcoq.Symbol.nterml pattern ("200"))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                                ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterml pattern ("200"))) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ pl _ p _ loc -> 
# 387 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CPatOr (p::pl) 
                                                       );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                ((Pcoq.Symbol.nterml pattern ("200"))))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ p _ loc -> 
# 380 "parsing/g_constr.mlg"
          (* Preserve parentheses around numbers so that constrintern does not
             collapse -(3) into the number -3. *)
          match p.CAst.v with
          | CPatPrim (Number (NumTok.SPlus,n)) ->
              CAst.make ~loc @@ CPatNotation(None,(InConstrEntry,"( _ )"),([p],[]),[])
          | _ -> p 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                (fun _ loc -> 
# 378 "parsing/g_constr.mlg"
                 CAst.make ~loc @@ CPatAtom None 
                                              );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("{|")))))
                                                                ((Pcoq.Symbol.nterm record_patterns)))
                                                ((Pcoq.Symbol.nterm bar_cbrace)))
                                (fun _ pat _ loc -> 
# 377 "parsing/g_constr.mlg"
                                                     CAst.make ~loc @@ CPatRecord pat 
                                                    );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm Prim.reference)))
                                (fun r loc -> 
# 376 "parsing/g_constr.mlg"
                                               CAst.make ~loc @@ CPatAtom (Some r) 
                                              )])]))
        in let () = assert (Pcoq.Entry.is_empty fixannot) in
        let () =
        Pcoq.grammar_extend fixannot
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("measure"))))))
                                                                  ((Pcoq.Symbol.nterm constr)))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm identref))))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm constr))))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                  (fun _ rel id m _ _ loc -> 
# 395 "parsing/g_constr.mlg"
          CAst.make ~loc @@ CMeasureRec (id,m,rel) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("wf"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ id rel _ _ loc -> 
# 393 "parsing/g_constr.mlg"
                                                               CAst.make ~loc @@ CWfRec(id,rel) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("struct"))))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ id _ _ loc -> 
# 392 "parsing/g_constr.mlg"
                                                     CAst.make ~loc @@ CStructRec id 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty binders_fixannot) in
        let () =
        Pcoq.grammar_extend binders_fixannot
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 400 "parsing/g_constr.mlg"
             [], None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm binder)))
                                                 ((Pcoq.Symbol.nterm binders_fixannot)))
                                 (fun bl b loc -> 
# 399 "parsing/g_constr.mlg"
                                               b @ fst bl, snd bl 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ensure_fixannot)))
                                                 ((Pcoq.Symbol.nterm fixannot)))
                                 (fun f _ loc -> 
# 398 "parsing/g_constr.mlg"
                                           [], Some f 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty open_binders) in
        let () =
        Pcoq.grammar_extend open_binders
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm closed_binder)))
                                                  ((Pcoq.Symbol.nterm binders)))
                                  (fun bl' bl loc -> 
# 414 "parsing/g_constr.mlg"
          bl@bl' 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("..")))))
                                                 ((Pcoq.Symbol.nterm name)))
                                 (fun id2 _ id1 loc -> 
# 411 "parsing/g_constr.mlg"
          [CLocalAssum ([id1;(CAst.make ~loc (Name ldots_var));id2],
                        Default Explicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))] 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm name))))
                                                 ((Pcoq.Symbol.nterm binders)))
                                 (fun bl idl id loc -> 
# 409 "parsing/g_constr.mlg"
          binders_of_names (id::idl) @ bl 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm name))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm lconstr)))
                                 (fun c _ idl id loc -> 
# 406 "parsing/g_constr.mlg"
          [CLocalAssum (id::idl,Default Explicit,c)] 
                                                        )])]))
        in let () = assert (Pcoq.Entry.is_empty binders) in
        let () =
        Pcoq.grammar_extend binders
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm binder))))
                                  (fun l loc -> 
# 417 "parsing/g_constr.mlg"
                              List.flatten l 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty binder) in
        let () =
        Pcoq.grammar_extend binder
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm closed_binder)))
                                  (fun bl loc -> 
# 421 "parsing/g_constr.mlg"
                                bl 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm name)))
                                 (fun id loc -> 
# 420 "parsing/g_constr.mlg"
                       [CLocalAssum ([id],Default Explicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))] 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty closed_binder) in
        let () =
        Pcoq.grammar_extend closed_binder
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("'")))))
                                                  ((Pcoq.Symbol.nterml pattern ("0"))))
                                  (fun p _ loc -> 
# 456 "parsing/g_constr.mlg"
                                        [CLocalPattern p] 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("`[")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm typeclass_constraint)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ tc _ loc -> 
# 455 "parsing/g_constr.mlg"
          List.map (fun (n, b, t) -> CLocalAssum ([n], Generalized (NonMaxImplicit, b), t)) tc 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("`{")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm typeclass_constraint)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ tc _ loc -> 
# 453 "parsing/g_constr.mlg"
          List.map (fun (n, b, t) -> CLocalAssum ([n], Generalized (MaxImplicit, b), t)) tc 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("`(")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm typeclass_constraint)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ tc _ loc -> 
# 451 "parsing/g_constr.mlg"
          List.map (fun (n, b, t) -> CLocalAssum ([n], Generalized (Explicit, b), t)) tc 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm name)))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ idl id _ loc -> 
# 449 "parsing/g_constr.mlg"
          List.map (fun id -> CLocalAssum ([id],Default NonMaxImplicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))) (id::idl) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ c _ id _ loc -> 
# 447 "parsing/g_constr.mlg"
          [CLocalAssum ([id],Default NonMaxImplicit,c)] 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm name)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ c _ idl id _ loc -> 
# 445 "parsing/g_constr.mlg"
          [CLocalAssum (id::idl,Default NonMaxImplicit,c)] 
                                                            );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ id _ loc -> 
# 443 "parsing/g_constr.mlg"
          [CLocalAssum ([id],Default NonMaxImplicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))] 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm name)))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ idl id _ loc -> 
# 441 "parsing/g_constr.mlg"
          List.map (fun id -> CLocalAssum ([id],Default MaxImplicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))) (id::idl) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ c _ id _ loc -> 
# 439 "parsing/g_constr.mlg"
          [CLocalAssum ([id],Default MaxImplicit,c)] 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm name)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ c _ idl id _ loc -> 
# 437 "parsing/g_constr.mlg"
          [CLocalAssum (id::idl,Default MaxImplicit,c)] 
                                                            );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ id _ loc -> 
# 435 "parsing/g_constr.mlg"
          [CLocalAssum ([id],Default MaxImplicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))] 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ t _ id _ loc -> 
# 433 "parsing/g_constr.mlg"
          [CLocalDef (id,c,Some t)] 
                                                            );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ id _ loc -> 
# 429 "parsing/g_constr.mlg"
          match c.CAst.v with
          | CCast(c, DEFAULTcast, t) -> [CLocalDef (id,c,Some t)]
          | _ -> [CLocalDef (id,c,None)] 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ id _ loc -> 
# 427 "parsing/g_constr.mlg"
          [CLocalAssum ([id],Default Explicit,c)] 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm name)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ idl id _ loc -> 
# 425 "parsing/g_constr.mlg"
          [CLocalAssum (id::idl,Default Explicit,c)] 
                                                            )])]))
        in let () = assert (Pcoq.Entry.is_empty one_open_binder) in
        let () =
        Pcoq.grammar_extend one_open_binder
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm one_closed_binder)))
                                  (fun b loc -> 
# 461 "parsing/g_constr.mlg"
                                   b 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm lconstr)))
                                 (fun t _ na loc -> 
# 460 "parsing/g_constr.mlg"
                                         (CAst.make ~loc @@ CPatCast (pat_of_name na, t), Explicit) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm name)))
                                 (fun na loc -> 
# 459 "parsing/g_constr.mlg"
                       (pat_of_name na, Explicit) 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty one_closed_binder) in
        let () =
        Pcoq.grammar_extend one_closed_binder
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("'")))))
                                                  ((Pcoq.Symbol.nterml pattern ("0"))))
                                  (fun p _ loc -> 
# 469 "parsing/g_constr.mlg"
                                        (p, Explicit) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ t _ na _ loc -> 
# 468 "parsing/g_constr.mlg"
                                                   (CAst.make ~loc @@ CPatCast (pat_of_name na, t), NonMaxImplicit) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ na _ loc -> 
# 467 "parsing/g_constr.mlg"
                                 (pat_of_name na, NonMaxImplicit) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ t _ na _ loc -> 
# 466 "parsing/g_constr.mlg"
                                                   (CAst.make ~loc @@ CPatCast (pat_of_name na, t), MaxImplicit) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ na _ loc -> 
# 465 "parsing/g_constr.mlg"
                                 (pat_of_name na, MaxImplicit) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ t _ na _ loc -> 
# 464 "parsing/g_constr.mlg"
                                                   (CAst.make ~loc @@ CPatCast (pat_of_name na, t), Explicit) 
                                                        )])]))
        in let () = assert (Pcoq.Entry.is_empty typeclass_constraint)
        in
        let () =
        Pcoq.grammar_extend typeclass_constraint
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterml term ("200"))))
                                  (fun c loc -> 
# 478 "parsing/g_constr.mlg"
            (CAst.make ~loc Anonymous), false, c 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_name_colon)))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.stop)
                                                                 (fun loc ->
                                                                 
# 475 "parsing/g_constr.mlg"
                                                                           false 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 475 "parsing/g_constr.mlg"
                                                             true 
                                                                 )])))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c expl _ iid _ loc -> 
# 476 "parsing/g_constr.mlg"
            iid, expl, c 
                                                            );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.stop)
                                                                 (fun loc ->
                                                                 
# 473 "parsing/g_constr.mlg"
                                                                   false 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 473 "parsing/g_constr.mlg"
                                                     true 
                                                                 )])))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c expl _ _ id _ loc -> 
# 474 "parsing/g_constr.mlg"
            id, expl, c 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                 (fun c _ loc -> 
# 472 "parsing/g_constr.mlg"
                                        (CAst.make ~loc Anonymous), true, c 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty type_cstr) in
        let () =
        Pcoq.grammar_extend type_cstr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 482 "parsing/g_constr.mlg"
             CAst.make ~loc @@ CHole (None, IntroAnonymous, None) 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm lconstr)))
                                 (fun c _ loc -> 
# 481 "parsing/g_constr.mlg"
                              c 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty let_type_cstr) in
        let () =
        Pcoq.grammar_extend let_type_cstr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                   ((Pcoq.Symbol.nterm lconstr)))
                                                                   (fun c _
                                                                   loc -> 
                                                                   
# 485 "parsing/g_constr.mlg"
                                       c 
                                                                   )]))))
                                  (fun c loc -> 
# 485 "parsing/g_constr.mlg"
                                                  Loc.tag ~loc c 
                                                )])]))
        in ()

