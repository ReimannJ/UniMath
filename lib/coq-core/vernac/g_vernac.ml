
# 11 "vernac/g_vernac.mlg"
 

open Pp
open CErrors
open Util
open Names
open Glob_term
open Vernacexpr
open Constrexpr
open Constrexpr_ops
open Extend
open Decls
open Declaremods
open Namegen

module C = Constr

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pcoq.Module
open Pvernac.Vernac_
open Attributes

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

let query_command = Entry.create "query_command"

let search_query = Entry.create "search_query"
let search_queries = Entry.create "search_queries"

let subprf = Entry.create "subprf"

let quoted_attributes = Entry.create "quoted_attributes"
let class_rawexpr = Entry.create "class_rawexpr"
let thm_token = Entry.create "thm_token"
let def_token = Entry.create "def_token"
let assumption_token = Entry.create "assumption_token"
let def_body = Entry.create "def_body"
let decl_notations = Entry.create "decl_notations"
let record_field = Entry.create "record_field"
let of_type = Entry.create "of_type"
let section_subset_expr = Entry.create "section_subset_expr"
let scope_delimiter = Entry.create "scope_delimiter"
let syntax_modifiers = Entry.create "syntax_modifiers"

let make_bullet s =
  let open Proof_bullet in
  let n = String.length s in
  match s.[0] with
  | '-' -> Dash n
  | '+' -> Plus n
  | '*' -> Star n
  | _ -> assert false

(* For now we just keep the top-level location of the whole
   vernacular, that is to say, including attributes and control flags;
   this is not very convenient for advanced clients tho, so in the
   future it'd be cool to actually locate the attributes and control
   flags individually too. *)
let add_control_flag ~loc ~flag { CAst.v = cmd } =
  CAst.make ~loc { cmd with control = flag :: cmd.control }

let test_hash_ident =
  let open Pcoq.Lookahead in
  to_entry "test_hash_ident" begin
    lk_kw "#" >> lk_ident >> check_no_space
  end

let test_id_colon =
  let open Pcoq.Lookahead in
  to_entry "test_id_colon" begin
    lk_ident >> lk_kw ":"
  end



let _ = let decorated_vernac = Pcoq.Entry.make "decorated_vernac"
        and attribute_list = Pcoq.Entry.make "attribute_list"
        and attribute = Pcoq.Entry.make "attribute"
        and attr_value = Pcoq.Entry.make "attr_value"
        and legacy_attr = Pcoq.Entry.make "legacy_attr"
        and vernac = Pcoq.Entry.make "vernac"
        and vernac_aux = Pcoq.Entry.make "vernac_aux"
        in
        let () =
        Pcoq.grammar_extend vernac_control
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm decorated_vernac)))
                                  (fun v loc -> 
# 103 "vernac/g_vernac.mlg"
          let (attrs, expr) = v in CAst.make ~loc { control = []; attrs; expr = expr } 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Succeed"))))))
                                                 ((Pcoq.Symbol.nterm vernac_control)))
                                 (fun c _ loc -> 
# 101 "vernac/g_vernac.mlg"
          add_control_flag ~loc ~flag:ControlSucceed c 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Fail"))))))
                                                 ((Pcoq.Symbol.nterm vernac_control)))
                                 (fun c _ loc -> 
# 99 "vernac/g_vernac.mlg"
          add_control_flag ~loc ~flag:ControlFail c 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Timeout"))))))
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                 ((Pcoq.Symbol.nterm vernac_control)))
                                 (fun c n _ loc -> 
# 97 "vernac/g_vernac.mlg"
          add_control_flag ~loc ~flag:(ControlTimeout n) c 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Redirect"))))))
                                                                 ((Pcoq.Symbol.nterm ne_string)))
                                                 ((Pcoq.Symbol.nterm vernac_control)))
                                 (fun c s _ loc -> 
# 95 "vernac/g_vernac.mlg"
          add_control_flag ~loc ~flag:(ControlRedirect s) c 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Time"))))))
                                                 ((Pcoq.Symbol.nterm vernac_control)))
                                 (fun c _ loc -> 
# 93 "vernac/g_vernac.mlg"
          add_control_flag ~loc ~flag:(ControlTime false) c 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty decorated_vernac) in
        let () =
        Pcoq.grammar_extend decorated_vernac
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm quoted_attributes))))
                                                  ((Pcoq.Symbol.nterm vernac)))
                                  (fun fv a loc -> 
# 108 "vernac/g_vernac.mlg"
          let (f, v) = fv in (List.append (List.flatten a) f, v) 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty quoted_attributes) in
        let () =
        Pcoq.grammar_extend quoted_attributes
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("#[")))))
                                                                  ((Pcoq.Symbol.nterm attribute_list)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                  (fun _ a _ loc -> 
# 111 "vernac/g_vernac.mlg"
                                             a 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty attribute_list) in
        let () =
        Pcoq.grammar_extend attribute_list
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm attribute)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                  (fun a loc -> 
# 115 "vernac/g_vernac.mlg"
                                         a 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty attribute) in
        let () =
        Pcoq.grammar_extend attribute
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("using"))))))
                                                  ((Pcoq.Symbol.nterm attr_value)))
                                  (fun v _ loc -> 
# 121 "vernac/g_vernac.mlg"
                                            CAst.make ~loc ("using", v) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ident)))
                                                 ((Pcoq.Symbol.nterm attr_value)))
                                 (fun v k loc -> 
# 119 "vernac/g_vernac.mlg"
                                        CAst.make ~loc (Names.Id.to_string k, v) 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty attr_value) in
        let () =
        Pcoq.grammar_extend attr_value
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 128 "vernac/g_vernac.mlg"
             VernacFlagEmpty 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm attribute_list)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ a _ loc -> 
# 127 "vernac/g_vernac.mlg"
                                            VernacFlagList a 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun v _ loc -> 
# 126 "vernac/g_vernac.mlg"
                             VernacFlagLeaf (FlagIdent v) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                                                 ((Pcoq.Symbol.nterm string)))
                                 (fun v _ loc -> 
# 125 "vernac/g_vernac.mlg"
                              VernacFlagLeaf (FlagString v) 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty legacy_attr) in
        let () =
        Pcoq.grammar_extend legacy_attr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("Program"))))))
                                  (fun _ loc -> 
# 147 "vernac/g_vernac.mlg"
          CAst.make ~loc ("program", VernacFlagEmpty) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Private"))))))
                                 (fun _ loc -> 
# 145 "vernac/g_vernac.mlg"
          CAst.make ~loc ("private", VernacFlagList [CAst.make ~loc ("matching", VernacFlagEmpty)]) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("NonCumulative"))))))
                                 (fun _ loc -> 
# 143 "vernac/g_vernac.mlg"
          CAst.make ~loc ("universes", VernacFlagList [CAst.make ~loc ("cumulative", VernacFlagLeaf (FlagIdent "no"))]) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Cumulative"))))))
                                 (fun _ loc -> 
# 141 "vernac/g_vernac.mlg"
          CAst.make ~loc ("universes", VernacFlagList [CAst.make ~loc ("cumulative", VernacFlagEmpty)]) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Monomorphic"))))))
                                 (fun _ loc -> 
# 139 "vernac/g_vernac.mlg"
          Attributes.vernac_monomorphic_flag (Some loc) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Polymorphic"))))))
                                 (fun _ loc -> 
# 137 "vernac/g_vernac.mlg"
          Attributes.vernac_polymorphic_flag (Some loc) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Global"))))))
                                 (fun _ loc -> 
# 135 "vernac/g_vernac.mlg"
          CAst.make ~loc ("global", VernacFlagEmpty) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Local"))))))
                                 (fun _ loc -> 
# 133 "vernac/g_vernac.mlg"
          CAst.make ~loc ("local", VernacFlagEmpty) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty vernac) in
        let () =
        Pcoq.grammar_extend vernac
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm legacy_attr))))
                                                  ((Pcoq.Symbol.nterm vernac_aux)))
                                  (fun v attrs loc -> 
# 151 "vernac/g_vernac.mlg"
                                                       (attrs, v) 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty vernac_aux) in
        let () =
        Pcoq.grammar_extend vernac_aux
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm subprf)))
                                  (fun c loc -> 
# 160 "vernac/g_vernac.mlg"
                        c 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm syntax)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ c loc -> 
# 159 "vernac/g_vernac.mlg"
                             c 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm command)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ c loc -> 
# 158 "vernac/g_vernac.mlg"
                              c 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm gallina_ext)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ g loc -> 
# 157 "vernac/g_vernac.mlg"
                                  g 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm gallina)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ g loc -> 
# 156 "vernac/g_vernac.mlg"
                              g 
                                                 )])]))
        in let () =
        Pcoq.grammar_extend vernac_aux
        (Pcoq.Fresh
        (Gramlib.Gramext.Last, [(None, None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm command_entry)))
                                 (fun prfcom loc -> 
# 164 "vernac/g_vernac.mlg"
                                    prfcom 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty noedit_mode) in
        let () =
        Pcoq.grammar_extend noedit_mode
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm query_command)))
                                  (fun c loc -> 
# 167 "vernac/g_vernac.mlg"
                               c None 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty subprf) in
        let () =
        Pcoq.grammar_extend subprf
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                  (fun _ loc -> 
# 173 "vernac/g_vernac.mlg"
               VernacEndSubproof 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                 (fun _ loc -> 
# 172 "vernac/g_vernac.mlg"
               VernacSubproof None 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PBULLET (None)))))
                                 (fun s loc -> 
# 171 "vernac/g_vernac.mlg"
                      VernacBullet (make_bullet s) 
                                               )])]))
        in ()


# 179 "vernac/g_vernac.mlg"
 

let warn_plural_command =
  CWarnings.create ~name:"plural-command" ~category:"pedantic" ~default:CWarnings.Disabled
         (fun kwd -> strbrk (Printf.sprintf "Command \"%s\" expects more than one assumption." kwd))

let test_plural_form loc kwd = function
  | [(_,([_],_))] ->
     warn_plural_command ~loc kwd
  | _ -> ()

let test_plural_form_types loc kwd = function
  | [([_],_)] ->
     warn_plural_command ~loc kwd
  | _ -> ()

let lname_of_lident : lident -> lname =
  CAst.map (fun s -> Name s)

let name_of_ident_decl : ident_decl -> name_decl =
  on_fst lname_of_lident

let test_variance_ident =
  let open Pcoq.Lookahead in
  to_entry "test_variance_ident" begin
    lk_kws ["=";"+";"*"] >> lk_ident
  end



let _ = let register_token = Pcoq.Entry.make "register_token"
        and assumptions_token = Pcoq.Entry.make "assumptions_token"
        and inline = Pcoq.Entry.make "inline"
        and univ_constraint = Pcoq.Entry.make "univ_constraint"
        and variance = Pcoq.Entry.make "variance"
        and variance_identref = Pcoq.Entry.make "variance_identref"
        and cumul_univ_decl = Pcoq.Entry.make "cumul_univ_decl"
        and cumul_ident_decl = Pcoq.Entry.make "cumul_ident_decl"
        and inductive_token = Pcoq.Entry.make "inductive_token"
        and finite_token = Pcoq.Entry.make "finite_token"
        and reduce = Pcoq.Entry.make "reduce"
        and decl_notation = Pcoq.Entry.make "decl_notation"
        and decl_sep = Pcoq.Entry.make "decl_sep"
        and opt_constructors_or_fields =
          Pcoq.Entry.make "opt_constructors_or_fields"
        and constructors_or_record = Pcoq.Entry.make "constructors_or_record"
        and default_inhabitant_ident =
          Pcoq.Entry.make "default_inhabitant_ident"
        and opt_coercion = Pcoq.Entry.make "opt_coercion"
        and cofix_definition = Pcoq.Entry.make "cofix_definition"
        and scheme = Pcoq.Entry.make "scheme"
        and scheme_kind = Pcoq.Entry.make "scheme_kind"
        and scheme_type = Pcoq.Entry.make "scheme_type"
        and record_fields = Pcoq.Entry.make "record_fields"
        and field_body = Pcoq.Entry.make "field_body"
        and record_binder = Pcoq.Entry.make "record_binder"
        and assum_list = Pcoq.Entry.make "assum_list"
        and assum_coe = Pcoq.Entry.make "assum_coe"
        and assumpt = Pcoq.Entry.make "assumpt"
        and constructor_type = Pcoq.Entry.make "constructor_type"
        and constructor = Pcoq.Entry.make "constructor"
        in
        let () = assert (Pcoq.Entry.is_empty gallina) in
        let () =
        Pcoq.grammar_extend gallina
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Constraint"))))))
                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm univ_constraint)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                  (fun l _ loc -> 
# 259 "vernac/g_vernac.mlg"
                                                                   VernacConstraint l 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Universes"))))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm identref)))))
                                 (fun l _ loc -> 
# 258 "vernac/g_vernac.mlg"
                                                   VernacUniverse l 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Universe"))))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm identref)))))
                                 (fun l _ loc -> 
# 257 "vernac/g_vernac.mlg"
                                                  VernacUniverse l 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Primitive"))))))
                                                                 ((Pcoq.Symbol.nterm ident_decl)))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                                 (fun typ _
                                                                 loc -> 
                                                                 
# 255 "vernac/g_vernac.mlg"
                                                                                   typ 
                                                                 )]))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterm register_token)))
                                 (fun r _ typopt id _ loc -> 
# 256 "vernac/g_vernac.mlg"
            VernacPrimitive(id, r, typopt) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Register"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Inline"))))))
                                                 ((Pcoq.Symbol.nterm global)))
                                 (fun g _ _ loc -> 
# 254 "vernac/g_vernac.mlg"
            VernacRegister(g, RegisterInline) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Register"))))))
                                                                 ((Pcoq.Symbol.nterm global)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm qualid)))
                                 (fun quid _ g _ loc -> 
# 252 "vernac/g_vernac.mlg"
            VernacRegister(g, RegisterCoqlib quid) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Combined"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scheme"))))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("from"))))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm identref)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                 (fun l _ id _ _ loc -> 
# 250 "vernac/g_vernac.mlg"
                                              VernacCombinedScheme (id, l) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scheme"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Boolean"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Equality"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("for"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun id _ _ _ _ loc -> 
# 248 "vernac/g_vernac.mlg"
            VernacSchemeEquality (SchemeBooleanEquality,id) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scheme"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Equality"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("for"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun id _ _ _ loc -> 
# 246 "vernac/g_vernac.mlg"
            VernacSchemeEquality (SchemeEquality,id) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scheme"))))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm scheme)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                 (fun l _ loc -> 
# 244 "vernac/g_vernac.mlg"
                                                         VernacScheme l 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Let"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("CoFixpoint")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm cofix_definition)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                 (fun corecs _ _ loc -> 
# 243 "vernac/g_vernac.mlg"
            VernacCoFixpoint (DoDischarge, corecs) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("CoFixpoint")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm cofix_definition)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                 (fun corecs _ loc -> 
# 241 "vernac/g_vernac.mlg"
            VernacCoFixpoint (NoDischarge, corecs) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Let"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Fixpoint")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm fix_definition)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                 (fun recs _ _ loc -> 
# 239 "vernac/g_vernac.mlg"
            VernacFixpoint (DoDischarge, recs) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Fixpoint")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm fix_definition)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                 (fun recs _ loc -> 
# 237 "vernac/g_vernac.mlg"
            VernacFixpoint (NoDischarge, recs) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm inductive_token)))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm inductive_or_record_definition)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("with"))])) false)))
                                 (fun indl f loc -> 
# 235 "vernac/g_vernac.mlg"
            VernacInductive (f, indl) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm finite_token)))
                                                 ((Pcoq.Symbol.nterm inductive_or_record_definition)))
                                 (fun ind f loc -> 
# 233 "vernac/g_vernac.mlg"
            VernacInductive (f, [ind]) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Let"))))))
                                                                 ((Pcoq.Symbol.nterm ident_decl)))
                                                 ((Pcoq.Symbol.nterm def_body)))
                                 (fun b id _ loc -> 
# 230 "vernac/g_vernac.mlg"
            VernacDefinition ((DoDischarge, Let), name_of_ident_decl id, b) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm def_token)))
                                                                 ((Pcoq.Symbol.nterm ident_decl)))
                                                 ((Pcoq.Symbol.nterm def_body)))
                                 (fun b id d loc -> 
# 228 "vernac/g_vernac.mlg"
            VernacDefinition (d, name_of_ident_decl id, b) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm assumptions_token)))
                                                                 ((Pcoq.Symbol.nterm inline)))
                                                 ((Pcoq.Symbol.nterm assum_list)))
                                 (fun bl nl tk loc -> 
# 224 "vernac/g_vernac.mlg"
            let (kwd,stre) = tk in
            test_plural_form loc kwd bl;
            VernacAssumption (stre, nl, bl) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm assumption_token)))
                                                                 ((Pcoq.Symbol.nterm inline)))
                                                 ((Pcoq.Symbol.nterm assum_list)))
                                 (fun bl nl stre loc -> 
# 222 "vernac/g_vernac.mlg"
            VernacAssumption (stre, nl, bl) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm thm_token)))
                                                                 ((Pcoq.Symbol.nterm ident_decl)))
                                                                 ((Pcoq.Symbol.nterm binders)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                                  ((Pcoq.Symbol.nterm ident_decl)))
                                                                  ((Pcoq.Symbol.nterm binders)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                                  (fun c _ bl
                                                                  id _ loc ->
                                                                  
# 219 "vernac/g_vernac.mlg"
            (id,(bl,c)) 
                                                                  )]))))
                                 (fun l c _ bl id thm loc -> 
# 220 "vernac/g_vernac.mlg"
            VernacStartTheoremProof (thm, (id,(bl,c))::l) 
                                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty register_token) in
        let () =
        Pcoq.grammar_extend register_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm test_hash_ident)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("#")))))
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                  (fun r _ _ loc -> 
# 263 "vernac/g_vernac.mlg"
                                             CPrimitives.parse_op_or_type ~loc r 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty thm_token) in
        let () =
        Pcoq.grammar_extend thm_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("Property"))))))
                                  (fun _ loc -> 
# 272 "vernac/g_vernac.mlg"
                              Property 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Proposition"))))))
                                 (fun _ loc -> 
# 271 "vernac/g_vernac.mlg"
                                 Proposition 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Corollary"))))))
                                 (fun _ loc -> 
# 270 "vernac/g_vernac.mlg"
                               Corollary 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Remark"))))))
                                 (fun _ loc -> 
# 269 "vernac/g_vernac.mlg"
                            Remark 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Fact"))))))
                                 (fun _ loc -> 
# 268 "vernac/g_vernac.mlg"
                          Fact 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Lemma"))))))
                                 (fun _ loc -> 
# 267 "vernac/g_vernac.mlg"
                           Lemma 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Theorem")))))
                                 (fun _ loc -> 
# 266 "vernac/g_vernac.mlg"
                       Theorem 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty def_token) in
        let () =
        Pcoq.grammar_extend def_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("SubClass"))))))
                                  (fun _ loc -> 
# 277 "vernac/g_vernac.mlg"
                              (NoDischarge,SubClass) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Example"))))))
                                 (fun _ loc -> 
# 276 "vernac/g_vernac.mlg"
                             (NoDischarge,Example) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Definition")))))
                                 (fun _ loc -> 
# 275 "vernac/g_vernac.mlg"
                          (NoDischarge,Definition) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty assumption_token) in
        let () =
        Pcoq.grammar_extend assumption_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("Conjecture"))))))
                                  (fun _ loc -> 
# 284 "vernac/g_vernac.mlg"
                                (NoDischarge, Conjectural) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Parameter")))))
                                 (fun _ loc -> 
# 283 "vernac/g_vernac.mlg"
                         (NoDischarge, Definitional) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Axiom")))))
                                 (fun _ loc -> 
# 282 "vernac/g_vernac.mlg"
                     (NoDischarge, Logical) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Variable")))))
                                 (fun _ loc -> 
# 281 "vernac/g_vernac.mlg"
                        (DoDischarge, Definitional) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Hypothesis")))))
                                 (fun _ loc -> 
# 280 "vernac/g_vernac.mlg"
                          (DoDischarge, Logical) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty assumptions_token) in
        let () =
        Pcoq.grammar_extend assumptions_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("Conjectures"))))))
                                  (fun _ loc -> 
# 291 "vernac/g_vernac.mlg"
                                 ("Conjectures", (NoDischarge, Conjectural)) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Parameters"))))))
                                 (fun _ loc -> 
# 290 "vernac/g_vernac.mlg"
                                ("Parameters", (NoDischarge, Definitional)) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Axioms"))))))
                                 (fun _ loc -> 
# 289 "vernac/g_vernac.mlg"
                            ("Axioms", (NoDischarge, Logical)) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Variables"))))))
                                 (fun _ loc -> 
# 288 "vernac/g_vernac.mlg"
                               ("Variables", (DoDischarge, Definitional)) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Hypotheses"))))))
                                 (fun _ loc -> 
# 287 "vernac/g_vernac.mlg"
                                ("Hypotheses", (DoDischarge, Logical)) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty inline) in
        let () =
        Pcoq.grammar_extend inline
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 296 "vernac/g_vernac.mlg"
             NoInline 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Inline"))))))
                                 (fun _ loc -> 
# 295 "vernac/g_vernac.mlg"
                            DefaultInline 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Inline"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ i _ _ loc -> 
# 294 "vernac/g_vernac.mlg"
                                                   InlineAt i 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty univ_constraint) in
        let () =
        Pcoq.grammar_extend univ_constraint
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm universe_name)))
                                                                  ((Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("<=")))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 299 "vernac/g_vernac.mlg"
                                                                                       Univ.Le 
                                                                  );
                                                                  Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 299 "vernac/g_vernac.mlg"
                                                                 Univ.Eq 
                                                                  );
                                                                  Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("<")))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 299 "vernac/g_vernac.mlg"
                                            Univ.Lt 
                                                                  )])))
                                                  ((Pcoq.Symbol.nterm universe_name)))
                                  (fun r ord l loc -> 
# 300 "vernac/g_vernac.mlg"
                               (l, ord, r) 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty univ_decl) in
        let () =
        Pcoq.grammar_extend univ_decl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("@{")))))
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm identref))))
                                                                  ((Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.stop)
                                                                  (fun loc ->
                                                                  
# 303 "vernac/g_vernac.mlg"
                                                                   false 
                                                                  );
                                                                  Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 303 "vernac/g_vernac.mlg"
                                                     true 
                                                                  )])))
                                                  ((Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.rules 
                                                                   [Pcoq.Rules.make 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.nterm bar_cbrace)))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 306 "vernac/g_vernac.mlg"
                                                          false 
                                                                   );
                                                                   Pcoq.Rules.make 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 306 "vernac/g_vernac.mlg"
                                 true 
                                                                   )]))) (fun
                                                                   ext loc ->
                                                                   
# 306 "vernac/g_vernac.mlg"
                                                                         ([], ext) 
                                                                   );
                                                  Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm univ_constraint)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                  ((Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.stop)
                                                                  (fun loc ->
                                                                  
# 305 "vernac/g_vernac.mlg"
                                               false 
                                                                  );
                                                                  Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 305 "vernac/g_vernac.mlg"
                                 true 
                                                                  )])))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                                                  (fun _ ext
                                                                  l' _ loc ->
                                                                  
# 305 "vernac/g_vernac.mlg"
                                                                   (l',ext) 
                                                                  )])))
                                  (fun cs ext l _ loc -> 
# 308 "vernac/g_vernac.mlg"
           let open UState in
         { univdecl_instance = l;
           univdecl_extensible_instance = ext;
           univdecl_constraints = fst cs;
           univdecl_extensible_constraints = snd cs } 
                                                         )])]))
        in let () = assert (Pcoq.Entry.is_empty variance) in
        let () =
        Pcoq.grammar_extend variance
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                  (fun _ loc -> 
# 318 "vernac/g_vernac.mlg"
                 Univ.Variance.Irrelevant 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("=")))))
                                 (fun _ loc -> 
# 317 "vernac/g_vernac.mlg"
                 Univ.Variance.Invariant 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                 (fun _ loc -> 
# 316 "vernac/g_vernac.mlg"
                 Univ.Variance.Covariant 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty variance_identref) in
        let () =
        Pcoq.grammar_extend variance_identref
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm test_variance_ident)))
                                                                  ((Pcoq.Symbol.nterm variance)))
                                                  ((Pcoq.Symbol.nterm identref)))
                                  (fun id v _ loc -> 
# 323 "vernac/g_vernac.mlg"
                                                              (id, Some v) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm identref)))
                                 (fun id loc -> 
# 322 "vernac/g_vernac.mlg"
                           (id, None) 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty cumul_univ_decl) in
        let () =
        Pcoq.grammar_extend cumul_univ_decl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("@{")))))
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm variance_identref))))
                                                                  ((Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.stop)
                                                                  (fun loc ->
                                                                  
# 329 "vernac/g_vernac.mlg"
                                                                            false 
                                                                  );
                                                                  Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 329 "vernac/g_vernac.mlg"
                                                              true 
                                                                  )])))
                                                  ((Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.rules 
                                                                   [Pcoq.Rules.make 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.nterm bar_cbrace)))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 332 "vernac/g_vernac.mlg"
                                                          false 
                                                                   );
                                                                   Pcoq.Rules.make 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 332 "vernac/g_vernac.mlg"
                                 true 
                                                                   )]))) (fun
                                                                   ext loc ->
                                                                   
# 332 "vernac/g_vernac.mlg"
                                                                         ([], ext) 
                                                                   );
                                                  Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                                  ((Pcoq.Symbol.list0sep ((Pcoq.Symbol.nterm univ_constraint)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                  ((Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.stop)
                                                                  (fun loc ->
                                                                  
# 331 "vernac/g_vernac.mlg"
                                               false 
                                                                  );
                                                                  Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 331 "vernac/g_vernac.mlg"
                                 true 
                                                                  )])))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                                                  (fun _ ext
                                                                  l' _ loc ->
                                                                  
# 331 "vernac/g_vernac.mlg"
                                                                   (l',ext) 
                                                                  )])))
                                  (fun cs ext l _ loc -> 
# 334 "vernac/g_vernac.mlg"
           let open UState in
         { univdecl_instance = l;
           univdecl_extensible_instance = ext;
           univdecl_constraints = fst cs;
           univdecl_extensible_constraints = snd cs } 
                                                         )])]))
        in let () = assert (Pcoq.Entry.is_empty ident_decl) in
        let () =
        Pcoq.grammar_extend ident_decl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm identref)))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm univ_decl))))
                                  (fun l i loc -> 
# 342 "vernac/g_vernac.mlg"
                                             (i, l) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty cumul_ident_decl) in
        let () =
        Pcoq.grammar_extend cumul_ident_decl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm identref)))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm cumul_univ_decl))))
                                  (fun l i loc -> 
# 346 "vernac/g_vernac.mlg"
                                                   (i, l) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty inductive_token) in
        let () =
        Pcoq.grammar_extend inductive_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("CoInductive"))))))
                                  (fun _ loc -> 
# 351 "vernac/g_vernac.mlg"
                                 CoInductive 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Inductive"))))))
                                 (fun _ loc -> 
# 350 "vernac/g_vernac.mlg"
                               Inductive_kw 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty finite_token) in
        let () =
        Pcoq.grammar_extend finite_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("Class"))))))
                                  (fun _ loc -> 
# 357 "vernac/g_vernac.mlg"
                           Class true 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Structure"))))))
                                 (fun _ loc -> 
# 356 "vernac/g_vernac.mlg"
                               Structure 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Record"))))))
                                 (fun _ loc -> 
# 355 "vernac/g_vernac.mlg"
                            Record 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Variant"))))))
                                 (fun _ loc -> 
# 354 "vernac/g_vernac.mlg"
                             Variant 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty def_body) in
        let () =
        Pcoq.grammar_extend def_body
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm binders)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun t _ bl loc -> 
# 368 "vernac/g_vernac.mlg"
          ProveBody (bl, t) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm binders)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm reduce)))
                                                 ((Pcoq.Symbol.nterm lconstr)))
                                 (fun c red _ t _ bl loc -> 
# 366 "vernac/g_vernac.mlg"
          DefineBody (bl, red, c, Some t) 
                                                            );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm binders)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm reduce)))
                                                 ((Pcoq.Symbol.nterm lconstr)))
                                 (fun c red _ bl loc -> 
# 362 "vernac/g_vernac.mlg"
          match c.CAst.v with
          | CCast(c, C.DEFAULTcast, t) -> DefineBody (bl, red, c, Some t)
          | _ -> DefineBody (bl, red, c, None) 
                                                        )])]))
        in let () = assert (Pcoq.Entry.is_empty reduce) in
        let () =
        Pcoq.grammar_extend reduce
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 372 "vernac/g_vernac.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Eval"))))))
                                                                 ((Pcoq.Symbol.nterm red_expr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                 (fun _ r _ loc -> 
# 371 "vernac/g_vernac.mlg"
                                              Some r 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty decl_notation) in
        let () =
        Pcoq.grammar_extend decl_notation
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ne_lstring)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                  ((Pcoq.Symbol.nterm constr)))
                                                                  ((Pcoq.Symbol.nterm syntax_modifiers)))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                   ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                   (fun sc _
                                                                   loc -> 
                                                                   
# 377 "vernac/g_vernac.mlg"
                                           sc 
                                                                   )]))))
                                  (fun scopt modl c _ ntn loc -> 
# 378 "vernac/g_vernac.mlg"
        { decl_ntn_string = ntn; decl_ntn_interp = c;
          decl_ntn_scope = scopt;
          decl_ntn_modifiers = modl;
      } 
                                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty decl_sep) in
        let () =
        Pcoq.grammar_extend decl_sep
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("and"))))))
                                  (fun _ loc -> 
# 384 "vernac/g_vernac.mlg"
                         () 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty decl_notations) in
        let () =
        Pcoq.grammar_extend decl_notations
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 388 "vernac/g_vernac.mlg"
           [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("where")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm decl_notation)) ((Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm decl_sep)))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 0 ""
()
                                                                  )])) false)))
                                 (fun l _ loc -> 
# 387 "vernac/g_vernac.mlg"
                                                           l 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty opt_constructors_or_fields)
        in
        let () =
        Pcoq.grammar_extend opt_constructors_or_fields
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 393 "vernac/g_vernac.mlg"
             RecordDecl (None, [], None) 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterm constructors_or_record)))
                                 (fun lc _ loc -> 
# 392 "vernac/g_vernac.mlg"
                                               lc 
                                                  )])]))
        in let () =
        assert (Pcoq.Entry.is_empty inductive_or_record_definition)
        in
        let () =
        Pcoq.grammar_extend inductive_or_record_definition
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm opt_coercion)))
                                                                  ((Pcoq.Symbol.nterm cumul_ident_decl)))
                                                                  ((Pcoq.Symbol.nterm binders)))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                                  ((Pcoq.Symbol.nterm binders)))
                                                                  (fun p _
                                                                  loc -> 
                                                                  
# 397 "vernac/g_vernac.mlg"
                                               p 
                                                                  )]))))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                                  (fun c _
                                                                  loc -> 
                                                                  
# 398 "vernac/g_vernac.mlg"
                                        c 
                                                                  )]))))
                                                                  ((Pcoq.Symbol.nterm opt_constructors_or_fields)))
                                                  ((Pcoq.Symbol.nterm decl_notations)))
                                  (fun ntn lc c extrapar indpar id oc loc ->
                                  
# 400 "vernac/g_vernac.mlg"
             (((oc,id),(indpar,extrapar),c,lc),ntn) 
                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty constructors_or_record)
        in
        let () =
        Pcoq.grammar_extend constructors_or_record
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 410 "vernac/g_vernac.mlg"
              Constructors [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.nterm record_fields)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                                 ((Pcoq.Symbol.nterm default_inhabitant_ident)))
                                 (fun id _ fs _ loc -> 
# 409 "vernac/g_vernac.mlg"
                                                                        RecordDecl (None,fs,id) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.nterm record_fields)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                                 ((Pcoq.Symbol.nterm default_inhabitant_ident)))
                                 (fun id _ fs _ cstr loc -> 
# 408 "vernac/g_vernac.mlg"
            RecordDecl (Some cstr,fs,id) 
                                                            );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                 ((Pcoq.Symbol.nterm constructor_type)))
                                 (fun c id loc -> 
# 406 "vernac/g_vernac.mlg"
                                                  Constructors [ c id ] 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.nterm constructor_type)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm constructor)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun l _ c id loc -> 
# 405 "vernac/g_vernac.mlg"
            Constructors ((c id)::l) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm constructor)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                 (fun l _ loc -> 
# 403 "vernac/g_vernac.mlg"
                                                Constructors l 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty default_inhabitant_ident)
        in
        let () =
        Pcoq.grammar_extend default_inhabitant_ident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 414 "vernac/g_vernac.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm identref)))
                                 (fun id _ loc -> 
# 413 "vernac/g_vernac.mlg"
                                 Some id 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty opt_coercion) in
        let () =
        Pcoq.grammar_extend opt_coercion
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 423 "vernac/g_vernac.mlg"
              false 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (">")))))
                                 (fun _ loc -> 
# 422 "vernac/g_vernac.mlg"
                 true 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty fix_definition) in
        let () =
        Pcoq.grammar_extend fix_definition
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ident_decl)))
                                                                  ((Pcoq.Symbol.nterm binders_fixannot)))
                                                                  ((Pcoq.Symbol.nterm type_cstr)))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                                  (fun def _
                                                                  loc -> 
                                                                  
# 430 "vernac/g_vernac.mlg"
                                                 def 
                                                                  )]))))
                                                  ((Pcoq.Symbol.nterm decl_notations)))
                                  (fun notations body_def rtype bl id_decl
                                  loc -> 
# 431 "vernac/g_vernac.mlg"
            let binders, rec_order = bl in
            {fname = fst id_decl; univs = snd id_decl; rec_order; binders; rtype; body_def; notations}
          
                                         )])]))
        in let () = assert (Pcoq.Entry.is_empty cofix_definition) in
        let () =
        Pcoq.grammar_extend cofix_definition
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ident_decl)))
                                                                  ((Pcoq.Symbol.nterm binders)))
                                                                  ((Pcoq.Symbol.nterm type_cstr)))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                                  (fun def _
                                                                  loc -> 
                                                                  
# 437 "vernac/g_vernac.mlg"
                                                 def 
                                                                  )]))))
                                                  ((Pcoq.Symbol.nterm decl_notations)))
                                  (fun notations body_def rtype binders
                                  id_decl loc -> 
# 438 "vernac/g_vernac.mlg"
          {fname = fst id_decl; univs = snd id_decl; rec_order = (); binders; rtype; body_def; notations}
        
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty scheme) in
        let () =
        Pcoq.grammar_extend scheme
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm identref)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm scheme_kind)))
                                  (fun kind _ id loc -> 
# 444 "vernac/g_vernac.mlg"
                                                     (Some id,kind) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm scheme_kind)))
                                 (fun kind loc -> 
# 443 "vernac/g_vernac.mlg"
                                (None,kind) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty scheme_kind) in
        let () =
        Pcoq.grammar_extend scheme_kind
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm scheme_type)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("for")))))
                                                                  ((Pcoq.Symbol.nterm smart_global)))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Sort"))))))
                                                  ((Pcoq.Symbol.nterm sort_family)))
                                  (fun sch_sort _ sch_qualid _ sch_type
                                  loc -> 
# 448 "vernac/g_vernac.mlg"
           {sch_type; sch_qualid; sch_sort} 
                                         )])]))
        in let () = assert (Pcoq.Entry.is_empty scheme_type) in
        let () =
        Pcoq.grammar_extend scheme_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("Case"))))))
                                  (fun _ loc -> 
# 455 "vernac/g_vernac.mlg"
                          SchemeCase 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Elimination"))))))
                                 (fun _ loc -> 
# 454 "vernac/g_vernac.mlg"
                                 SchemeElimination 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Minimality"))))))
                                 (fun _ loc -> 
# 453 "vernac/g_vernac.mlg"
                                SchemeMinimality 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Induction"))))))
                                 (fun _ loc -> 
# 452 "vernac/g_vernac.mlg"
                               SchemeInduction 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty record_field) in
        let () =
        Pcoq.grammar_extend record_field
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm quoted_attributes))))
                                                                  ((Pcoq.Symbol.nterm record_binder)))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                  [Pcoq.Rules.make 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                                  ((Pcoq.Symbol.nterm natural)))
                                                                  (fun n _
                                                                  loc -> 
                                                                  
# 473 "vernac/g_vernac.mlg"
                                                                    n 
                                                                  )]))))
                                                  ((Pcoq.Symbol.nterm decl_notations)))
                                  (fun rf_notation rf_priority bd attr loc ->
                                  
# 474 "vernac/g_vernac.mlg"
                                       
      let rf_canonical, rf_reverse = attr |> List.flatten |> parse Notations.(canonical_field ++ reversible) in
      let rf_subclass, rf_decl = bd in
      rf_decl, { rf_subclass ; rf_reverse ; rf_priority ; rf_notation ; rf_canonical } 
                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty record_fields) in
        let () =
        Pcoq.grammar_extend record_fields
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 482 "vernac/g_vernac.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm record_field)))
                                 (fun f loc -> 
# 481 "vernac/g_vernac.mlg"
                              [f] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm record_field)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (";")))))
                                                 ((Pcoq.Symbol.nterm record_fields)))
                                 (fun fs _ f loc -> 
# 480 "vernac/g_vernac.mlg"
                                                       f :: fs 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty field_body) in
        let () =
        Pcoq.grammar_extend field_body
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm binders)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun b _ l loc -> 
# 491 "vernac/g_vernac.mlg"
                                            fun id ->
        (* Why are we dropping cast info here? *)
         match b.CAst.v with
         | CCast(b', _, t) ->
             (NoInstance,DefExpr(id,l,b',Some t))
         | _ ->
             (NoInstance,DefExpr(id,l,b,None)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm binders)))
                                                                 ((Pcoq.Symbol.nterm of_type)))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterm lconstr)))
                                 (fun b _ t oc l loc -> 
# 489 "vernac/g_vernac.mlg"
                                             fun id ->
           (oc,DefExpr (id,l,b,Some t)) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm binders)))
                                                                 ((Pcoq.Symbol.nterm of_type)))
                                                 ((Pcoq.Symbol.nterm lconstr)))
                                 (fun t oc l loc -> 
# 487 "vernac/g_vernac.mlg"
                          fun id -> (oc,AssumExpr (id,l,t)) 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty record_binder) in
        let () =
        Pcoq.grammar_extend record_binder
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm name)))
                                                  ((Pcoq.Symbol.nterm field_body)))
                                  (fun f id loc -> 
# 501 "vernac/g_vernac.mlg"
                                       f id 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm name)))
                                 (fun id loc -> 
# 500 "vernac/g_vernac.mlg"
                       (NoInstance,AssumExpr(id, [], CAst.make ~loc @@ CHole (None, IntroAnonymous, None))) 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty assum_list) in
        let () =
        Pcoq.grammar_extend assum_list
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm assumpt)))
                                  (fun b loc -> 
# 504 "vernac/g_vernac.mlg"
                                                          [b] 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm assum_coe)))))
                                 (fun bl loc -> 
# 504 "vernac/g_vernac.mlg"
                                  bl 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty assum_coe) in
        let () =
        Pcoq.grammar_extend assum_coe
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm assumpt)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ a _ loc -> 
# 507 "vernac/g_vernac.mlg"
                                   a 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty assumpt) in
        let () =
        Pcoq.grammar_extend assumpt
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ident_decl)))))
                                                                  ((Pcoq.Symbol.nterm of_type)))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun c oc idl loc -> 
# 511 "vernac/g_vernac.mlg"
          (oc <> NoInstance,(idl,c)) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty constructor_type) in
        let () =
        Pcoq.grammar_extend constructor_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm binders)))
                                                  ((Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.stop)
                                                                   (fun
                                                                   loc -> 
                                                                   
# 519 "vernac/g_vernac.mlg"
                   fun l id -> (false,(id,mkProdCN ~loc l (CAst.make ~loc @@ CHole (None, IntroAnonymous, None)))) 
                                                                   );
                                                  Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm of_type)))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                                  (fun c coe
                                                                  loc -> 
                                                                  
# 517 "vernac/g_vernac.mlg"
                      fun l id -> (coe <> NoInstance,(id,mkProdCN ~loc l c)) 
                                                                  )])))
                                  (fun t l loc -> 
# 520 "vernac/g_vernac.mlg"
              t l 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty constructor) in
        let () =
        Pcoq.grammar_extend constructor
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm identref)))
                                                  ((Pcoq.Symbol.nterm constructor_type)))
                                  (fun c id loc -> 
# 525 "vernac/g_vernac.mlg"
                                               c id 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty of_type) in
        let () =
        Pcoq.grammar_extend of_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                  (fun _ loc -> 
# 530 "vernac/g_vernac.mlg"
                   NoInstance 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (">")))))
                                 (fun _ _ loc -> 
# 529 "vernac/g_vernac.mlg"
                        BackInstance 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":>")))))
                                 (fun _ loc -> 
# 528 "vernac/g_vernac.mlg"
                    BackInstance 
                                               )])]))
        in ()


# 534 "vernac/g_vernac.mlg"
 

let test_only_starredidentrefs =
  let open Pcoq.Lookahead in
  to_entry "test_only_starredidentrefs" begin
    lk_list (lk_ident <+> lk_kws ["Type"; "*"]) >> (lk_kws [".";")"])
  end

let starredidentreflist_to_expr l =
  match l with
  | [] -> SsEmpty
  | x :: xs -> List.fold_right (fun i acc -> SsUnion(i,acc)) xs x

let warn_deprecated_include_type =
  CWarnings.create ~name:"deprecated-include-type" ~category:"deprecated"
         (fun () -> strbrk "Include Type is deprecated; use Include instead")

let warn_deprecated_as_ident_kind =
  CWarnings.create ~name:"deprecated-as-ident-kind" ~category:"deprecated"
         (fun () -> strbrk "grammar kind \"as ident\" no longer accepts \"_\"; use \"as name\" instead to accept \"_\", too, or silence the warning if you actually intended to accept only identifiers.")



let _ = let import_categories = Pcoq.Entry.make "import_categories"
        and filtered_import = Pcoq.Entry.make "filtered_import"
        and one_import_filter_name = Pcoq.Entry.make "one_import_filter_name"
        and export_token = Pcoq.Entry.make "export_token"
        and ext_module_type = Pcoq.Entry.make "ext_module_type"
        and ext_module_expr = Pcoq.Entry.make "ext_module_expr"
        and check_module_type = Pcoq.Entry.make "check_module_type"
        and check_module_types = Pcoq.Entry.make "check_module_types"
        and of_module_type = Pcoq.Entry.make "of_module_type"
        and is_module_type = Pcoq.Entry.make "is_module_type"
        and is_module_expr = Pcoq.Entry.make "is_module_expr"
        and functor_app_annot = Pcoq.Entry.make "functor_app_annot"
        and module_expr_inl = Pcoq.Entry.make "module_expr_inl"
        and module_type_inl = Pcoq.Entry.make "module_type_inl"
        and module_binder = Pcoq.Entry.make "module_binder"
        and module_expr_atom = Pcoq.Entry.make "module_expr_atom"
        and with_declaration = Pcoq.Entry.make "with_declaration"
        and starredidentref = Pcoq.Entry.make "starredidentref"
        and ssexpr = Pcoq.Entry.make "ssexpr"
        in
        let () = assert (Pcoq.Entry.is_empty gallina_ext) in
        let () =
        Pcoq.grammar_extend gallina_ext
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Include"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                                                  ((Pcoq.Symbol.nterm module_type_inl)))
                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ext_module_type))))
                                  (fun l e _ _ loc -> 
# 603 "vernac/g_vernac.mlg"
           warn_deprecated_include_type ~loc ();
        VernacInclude(e::l) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Include"))))))
                                                                 ((Pcoq.Symbol.nterm module_type_inl)))
                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ext_module_expr))))
                                 (fun l e _ loc -> 
# 601 "vernac/g_vernac.mlg"
            VernacInclude(e::l) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Export"))))))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm import_categories))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm filtered_import)))))
                                 (fun qidl cats _ loc -> 
# 599 "vernac/g_vernac.mlg"
          VernacImport ((Export,cats),qidl) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Import"))))))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm import_categories))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm filtered_import)))))
                                 (fun qidl cats _ loc -> 
# 597 "vernac/g_vernac.mlg"
          VernacImport ((Import,cats),qidl) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("From"))))))
                                                                 ((Pcoq.Symbol.nterm global)))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Require"))))))
                                                                 ((Pcoq.Symbol.nterm export_token)))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm filtered_import)))))
                                 (fun qidl export _ ns _ loc -> 
# 595 "vernac/g_vernac.mlg"
          VernacRequire (Some ns, export, qidl) 
                                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Require"))))))
                                                                 ((Pcoq.Symbol.nterm export_token)))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm filtered_import)))))
                                 (fun qidl export _ loc -> 
# 592 "vernac/g_vernac.mlg"
            VernacRequire (None, export, qidl) 
                                                           );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("From"))))))
                                                                 ((Pcoq.Symbol.nterm global)))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Extra"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Dependency"))))))
                                                                 ((Pcoq.Symbol.nterm ne_string)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                  (fun id _
                                                                  loc -> 
                                                                  
# 587 "vernac/g_vernac.mlg"
                                         id 
                                                                  )]))))
                                 (fun id f _ _ ns _ loc -> 
# 588 "vernac/g_vernac.mlg"
            VernacExtraDependency (ns, f, Option.map Id.of_string id) 
                                                           );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Collection"))))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterm section_subset_expr)))
                                 (fun expr _ id _ loc -> 
# 582 "vernac/g_vernac.mlg"
            VernacNameSectionHypSet (id, expr) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("End"))))))
                                                 ((Pcoq.Symbol.nterm identref)))
                                 (fun id _ loc -> 
# 578 "vernac/g_vernac.mlg"
                                        VernacEndSegment id 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Section"))))))
                                                 ((Pcoq.Symbol.nterm identref)))
                                 (fun id _ loc -> 
# 575 "vernac/g_vernac.mlg"
                                            VernacBeginSection id 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Declare"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Module"))))))
                                                                 ((Pcoq.Symbol.nterm export_token)))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm module_binder))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm module_type_inl)))
                                 (fun mty _ bl id export _ _ loc -> 
# 573 "vernac/g_vernac.mlg"
            VernacDeclareModule (export, id, bl, mty) 
                                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Module"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm module_binder))))
                                                                 ((Pcoq.Symbol.nterm check_module_types)))
                                                 ((Pcoq.Symbol.nterm is_module_type)))
                                 (fun body sign bl id _ _ loc -> 
# 570 "vernac/g_vernac.mlg"
            VernacDeclareModuleType (id, bl, sign, body) 
                                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Module"))))))
                                                                 ((Pcoq.Symbol.nterm export_token)))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm module_binder))))
                                                                 ((Pcoq.Symbol.nterm of_module_type)))
                                                 ((Pcoq.Symbol.nterm is_module_expr)))
                                 (fun body sign bl id export _ loc -> 
# 566 "vernac/g_vernac.mlg"
            VernacDefineModule (export, id, bl, sign, body) 
                                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty import_categories) in
        let () =
        Pcoq.grammar_extend import_categories
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.token (Tok.PKEYWORD ("-"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm qualid)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ cats _ negative loc -> 
# 608 "vernac/g_vernac.mlg"
        let cats = List.map (fun cat -> CAst.make ?loc:cat.CAst.loc (Libnames.string_of_qualid cat)) cats in
        { negative=Option.has_some negative; import_cats = cats } 
                                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty filtered_import) in
        let () =
        Pcoq.grammar_extend filtered_import
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm global)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm one_import_filter_name)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ ns _ m loc -> 
# 614 "vernac/g_vernac.mlg"
                                                                             (m, ImportNames ns) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm global)))
                                 (fun m loc -> 
# 613 "vernac/g_vernac.mlg"
                        (m, ImportAll) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty one_import_filter_name)
        in
        let () =
        Pcoq.grammar_extend one_import_filter_name
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm global)))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD ("..")))))
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                                   (fun _ _ _
                                                                   loc -> 
                                                                   
# 617 "vernac/g_vernac.mlg"
                                                    () 
                                                                   )]))))
                                  (fun etc n loc -> 
# 617 "vernac/g_vernac.mlg"
                                                                n, Option.has_some etc 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty export_token) in
        let () =
        Pcoq.grammar_extend export_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 622 "vernac/g_vernac.mlg"
              None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Export"))))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm import_categories))))
                                 (fun cats _ loc -> 
# 621 "vernac/g_vernac.mlg"
                                                          Some (Export,cats) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Import"))))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm import_categories))))
                                 (fun cats _ loc -> 
# 620 "vernac/g_vernac.mlg"
                                                          Some (Import,cats) 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty ext_module_type) in
        let () =
        Pcoq.grammar_extend ext_module_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("<+")))))
                                                  ((Pcoq.Symbol.nterm module_type_inl)))
                                  (fun mty _ loc -> 
# 625 "vernac/g_vernac.mlg"
                                         mty 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty ext_module_expr) in
        let () =
        Pcoq.grammar_extend ext_module_expr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("<+")))))
                                                  ((Pcoq.Symbol.nterm module_expr_inl)))
                                  (fun mexpr _ loc -> 
# 628 "vernac/g_vernac.mlg"
                                           mexpr 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty check_module_type) in
        let () =
        Pcoq.grammar_extend check_module_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("<:")))))
                                                  ((Pcoq.Symbol.nterm module_type_inl)))
                                  (fun mty _ loc -> 
# 631 "vernac/g_vernac.mlg"
                                         mty 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty check_module_types)
        in
        let () =
        Pcoq.grammar_extend check_module_types
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm check_module_type))))
                                  (fun mtys loc -> 
# 634 "vernac/g_vernac.mlg"
                                            mtys 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty of_module_type) in
        let () =
        Pcoq.grammar_extend of_module_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm check_module_types)))
                                  (fun mtys loc -> 
# 638 "vernac/g_vernac.mlg"
                                       Check mtys 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm module_type_inl)))
                                 (fun mty _ loc -> 
# 637 "vernac/g_vernac.mlg"
                                        Enforce mty 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty is_module_type) in
        let () =
        Pcoq.grammar_extend is_module_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 642 "vernac/g_vernac.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm module_type_inl)))
                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ext_module_type))))
                                 (fun l mty _ loc -> 
# 641 "vernac/g_vernac.mlg"
                                                                     (mty::l) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty is_module_expr) in
        let () =
        Pcoq.grammar_extend is_module_expr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 646 "vernac/g_vernac.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm module_expr_inl)))
                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ext_module_expr))))
                                 (fun l mexpr _ loc -> 
# 645 "vernac/g_vernac.mlg"
                                                                      (mexpr::l) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty functor_app_annot) in
        let () =
        Pcoq.grammar_extend functor_app_annot
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 652 "vernac/g_vernac.mlg"
             DefaultInline 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("no"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inline"))))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ _ _ _ loc -> 
# 651 "vernac/g_vernac.mlg"
                                                  NoInline 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inline"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("level"))))))
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ i _ _ _ _ loc -> 
# 650 "vernac/g_vernac.mlg"
          InlineAt i 
                                                         )])]))
        in let () = assert (Pcoq.Entry.is_empty module_expr_inl) in
        let () =
        Pcoq.grammar_extend module_expr_inl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm module_expr)))
                                                  ((Pcoq.Symbol.nterm functor_app_annot)))
                                  (fun a me loc -> 
# 657 "vernac/g_vernac.mlg"
                                                     (me,a) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                 ((Pcoq.Symbol.nterm module_expr)))
                                 (fun me _ loc -> 
# 656 "vernac/g_vernac.mlg"
                                   (me,NoInline) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty module_type_inl) in
        let () =
        Pcoq.grammar_extend module_type_inl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm module_type)))
                                                  ((Pcoq.Symbol.nterm functor_app_annot)))
                                  (fun a me loc -> 
# 661 "vernac/g_vernac.mlg"
                                                     (me,a) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                 ((Pcoq.Symbol.nterm module_type)))
                                 (fun me _ loc -> 
# 660 "vernac/g_vernac.mlg"
                                   (me,NoInline) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty module_binder) in
        let () =
        Pcoq.grammar_extend module_binder
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm export_token)))
                                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm identref)))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.nterm module_type_inl)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ mty _ idl export _ loc -> 
# 666 "vernac/g_vernac.mlg"
                                         (export,idl,mty) 
                                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty module_expr) in
        let () =
        Pcoq.grammar_extend module_expr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm module_expr)))
                                                  ((Pcoq.Symbol.nterm module_expr_atom)))
                                  (fun me2 me1 loc -> 
# 671 "vernac/g_vernac.mlg"
                                                       CAst.make ~loc @@ CMapply (me1,me2) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm module_expr_atom)))
                                 (fun me loc -> 
# 670 "vernac/g_vernac.mlg"
                                   CAst.make ~loc @@ CMident me 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty module_expr_atom) in
        let () =
        Pcoq.grammar_extend module_expr_atom
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm module_expr_atom)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ me _ loc -> 
# 675 "vernac/g_vernac.mlg"
                                                                       me 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm qualid)))
                                 (fun qid loc -> 
# 675 "vernac/g_vernac.mlg"
                          qid 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty with_declaration) in
        let () =
        Pcoq.grammar_extend with_declaration
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Module"))))))
                                                                  ((Pcoq.Symbol.nterm fullyqualid)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm qualid)))
                                  (fun qid _ fqid _ loc -> 
# 681 "vernac/g_vernac.mlg"
            CWith_Module (fqid,qid) 
                                                           );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Definition")))))
                                                                 ((Pcoq.Symbol.nterm fullyqualid)))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm univ_decl))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterm Constr.lconstr)))
                                 (fun c _ udecl fqid _ loc -> 
# 679 "vernac/g_vernac.mlg"
            CWith_Definition (fqid,udecl,c) 
                                                              )])]))
        in let () = assert (Pcoq.Entry.is_empty module_type) in
        let () =
        Pcoq.grammar_extend module_type
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm module_type)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                  ((Pcoq.Symbol.nterm with_declaration)))
                                  (fun decl _ mty loc -> 
# 690 "vernac/g_vernac.mlg"
            CAst.make ~loc @@ CMwith (mty,decl) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm module_type)))
                                                 ((Pcoq.Symbol.nterm module_expr_atom)))
                                 (fun me mty loc -> 
# 688 "vernac/g_vernac.mlg"
            CAst.make ~loc @@ CMapply (mty,me) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm module_type)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ mt _ loc -> 
# 686 "vernac/g_vernac.mlg"
                                        mt 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm qualid)))
                                 (fun qid loc -> 
# 685 "vernac/g_vernac.mlg"
                          CAst.make ~loc @@ CMident qid 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty section_subset_expr)
        in
        let () =
        Pcoq.grammar_extend section_subset_expr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ssexpr)))
                                  (fun e loc -> 
# 697 "vernac/g_vernac.mlg"
                        e 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_only_starredidentrefs)))
                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm starredidentref))))
                                 (fun l _ loc -> 
# 696 "vernac/g_vernac.mlg"
            starredidentreflist_to_expr l 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty starredidentref) in
        let () =
        Pcoq.grammar_extend starredidentref
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                  (fun _ _ loc -> 
# 703 "vernac/g_vernac.mlg"
                         SsFwdClose SsType 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                 (fun _ loc -> 
# 702 "vernac/g_vernac.mlg"
                    SsType 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                 (fun _ i loc -> 
# 701 "vernac/g_vernac.mlg"
                               SsFwdClose(SsSingl i) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm identref)))
                                 (fun i loc -> 
# 700 "vernac/g_vernac.mlg"
                          SsSingl i 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty ssexpr) in
        let () =
        Pcoq.grammar_extend ssexpr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(Some ("35"), None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                  ((Pcoq.Symbol.nterm ssexpr)))
                                  (fun e _ loc -> 
# 707 "vernac/g_vernac.mlg"
                             SsCompl e 
                                                  )]);
                                (Some ("50"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ssexpr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                                 ((Pcoq.Symbol.nterm ssexpr)))
                                 (fun e2 _ e1 loc -> 
# 710 "vernac/g_vernac.mlg"
                                          SsUnion(e1,e2) 
                                                     );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm ssexpr)))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                ((Pcoq.Symbol.nterm ssexpr)))
                                (fun e2 _ e1 loc -> 
# 709 "vernac/g_vernac.mlg"
                                          SsSubstr(e1,e2) 
                                                    )]);
                                (Some ("0"), None,
                                [Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm ssexpr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                 (fun _ _ e _ loc -> 
# 719 "vernac/g_vernac.mlg"
                                       SsFwdClose e 
                                                     );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                ((Pcoq.Symbol.nterm ssexpr)))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ e _ loc -> 
# 718 "vernac/g_vernac.mlg"
                                 e 
                                                  );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                ((Pcoq.Symbol.nterm test_only_starredidentrefs)))
                                                                ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm starredidentref))))
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                (fun _ _ l _ _ loc -> 
# 717 "vernac/g_vernac.mlg"
            SsFwdClose(starredidentreflist_to_expr l) 
                                                      );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                ((Pcoq.Symbol.nterm test_only_starredidentrefs)))
                                                                ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm starredidentref))))
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                (fun _ l _ _ loc -> 
# 715 "vernac/g_vernac.mlg"
            starredidentreflist_to_expr l 
                                                    );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("()")))))
                                (fun _ loc -> 
# 713 "vernac/g_vernac.mlg"
                  SsEmpty 
                                              );
                                Pcoq.Production.make
                                (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                ((Pcoq.Symbol.nterm starredidentref)))
                                (fun i loc -> 
# 712 "vernac/g_vernac.mlg"
                                 i 
                                              )])]))
        in ()

let _ = let args_modifier = Pcoq.Entry.make "args_modifier"
        and argument_spec = Pcoq.Entry.make "argument_spec"
        and arg_specs = Pcoq.Entry.make "arg_specs"
        and implicits_alt = Pcoq.Entry.make "implicits_alt"
        and instance_name = Pcoq.Entry.make "instance_name"
        and reserv_list = Pcoq.Entry.make "reserv_list"
        and reserv_tuple = Pcoq.Entry.make "reserv_tuple"
        and simple_reserv = Pcoq.Entry.make "simple_reserv"
        in
        let () =
        Pcoq.grammar_extend gallina_ext
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Generalizable"))))))
                                            ((Pcoq.Symbol.rules [Pcoq.Rules.make 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.rules 
                                                                [Pcoq.Rules.make 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("Variables"))))))
                                                                (fun _ loc ->
                                                                
# 807 "vernac/g_vernac.mlg"
                                                              () 
                                                                );
                                                                Pcoq.Rules.make 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PKEYWORD ("Variable")))))
                                                                (fun _ loc ->
                                                                
# 807 "vernac/g_vernac.mlg"
                                () 
                                                                )])))
                                                                ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm identref)))))
                                                                (fun idl _
                                                                loc -> 
                                                                
# 808 "vernac/g_vernac.mlg"
                                            Some idl 
                                                                );
                                                                Pcoq.Rules.make 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("No"))))))
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("Variables"))))))
                                                                (fun _ _
                                                                loc -> 
                                                                
# 806 "vernac/g_vernac.mlg"
                                                  None 
                                                                );
                                                                Pcoq.Rules.make 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.next_norec 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("All"))))))
                                                                ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                ("Variables"))))))
                                                                (fun _ _
                                                                loc -> 
                                                                
# 805 "vernac/g_vernac.mlg"
                                                      Some [] 
                                                                )])))
                            (fun gen _ loc -> 
# 809 "vernac/g_vernac.mlg"
               VernacGeneralizable gen 
                                              );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Implicit"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Types"))))))
                                           ((Pcoq.Symbol.nterm reserv_list)))
                           (fun bl _ _ loc -> 
# 801 "vernac/g_vernac.mlg"
            test_plural_form_types loc "Implicit Types" bl;
           VernacReserve bl 
                                              );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Implicit"))))))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                           ((Pcoq.Symbol.nterm reserv_list)))
                           (fun bl _ _ loc -> 
# 798 "vernac/g_vernac.mlg"
             VernacReserve bl 
                                              );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Arguments"))))))
                                                           ((Pcoq.Symbol.nterm smart_global)))
                                                           ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm arg_specs))))
                                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                           [Pcoq.Rules.make 
                                                           (Pcoq.Rule.next_norec 
                                                           (Pcoq.Rule.next_norec 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                                                           ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.rules 
                                                           [Pcoq.Rules.make 
                                                           (Pcoq.Rule.next_norec 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm implicits_alt))))
                                                           (fun impl loc -> 
                                                           
# 789 "vernac/g_vernac.mlg"
                                              List.flatten impl 
                                                           )])) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                           (fun impl _ loc ->
                                                           
# 790 "vernac/g_vernac.mlg"
                         impl 
                                                           )]))))
                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                           [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                            ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm args_modifier)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                            (fun l _ loc -> 
                                                            
# 792 "vernac/g_vernac.mlg"
                                                               l 
                                                            )]))))
                           (fun mods more_implicits args qid _ loc -> 
# 793 "vernac/g_vernac.mlg"
           let mods = match mods with None -> [] | Some l -> List.flatten l in
         let more_implicits = Option.default [] more_implicits in
         VernacArguments (qid, List.flatten args, more_implicits, mods) 
                                                                    );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Existing"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Class"))))))
                                           ((Pcoq.Symbol.nterm global)))
                           (fun is _ _ loc -> 
# 782 "vernac/g_vernac.mlg"
                                                          VernacExistingClass is 
                                              );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Existing"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Instances"))))))
                                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                           [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                            ((Pcoq.Symbol.nterm natural)))
                                                            (fun i _ loc -> 
                                                            
# 777 "vernac/g_vernac.mlg"
                                          i 
                                                            )]))))
                           (fun pri ids _ _ loc -> 
# 778 "vernac/g_vernac.mlg"
           let info = { Typeclasses.hint_priority = pri; hint_pattern = None } in
         let insts = List.map (fun i -> (i, info)) ids in
          VernacExistingInstance insts 
                                                   );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Existing"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Instance"))))))
                                                           ((Pcoq.Symbol.nterm global)))
                                           ((Pcoq.Symbol.nterm hint_info)))
                           (fun info id _ _ loc -> 
# 774 "vernac/g_vernac.mlg"
            VernacExistingInstance [id, info] 
                                                   );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Instance"))))))
                                                           ((Pcoq.Symbol.nterm instance_name)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                           ((Pcoq.Symbol.nterml term ("200"))))
                                                           ((Pcoq.Symbol.nterm hint_info)))
                                           ((Pcoq.Symbol.rules [Pcoq.Rules.make 
                                                               (Pcoq.Rule.stop)
                                                               (fun loc -> 
                                                               
# 769 "vernac/g_vernac.mlg"
                                                            None 
                                                               );
                                                               Pcoq.Rules.make 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                               ((Pcoq.Symbol.nterm lconstr)))
                                                               (fun c _
                                                               loc -> 
                                                               
# 769 "vernac/g_vernac.mlg"
                                    Some (false,c) 
                                                               );
                                                               Pcoq.Rules.make 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                               ((Pcoq.Symbol.nterm record_declaration)))
                                                               ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                                               (fun _ r _ _
                                                               loc -> 
                                                               
# 768 "vernac/g_vernac.mlg"
                                                               Some (true,r) 
                                                               )])))
                           (fun props info t _ namesup _ loc -> 
# 770 "vernac/g_vernac.mlg"
             VernacInstance (fst namesup,snd namesup,t,props,info) 
                                                                );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Context"))))))
                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm binder)))))
                           (fun c _ loc -> 
# 763 "vernac/g_vernac.mlg"
            VernacContext (List.flatten c) 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Coercion"))))))
                                                           ((Pcoq.Symbol.nterm by_notation)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                           ((Pcoq.Symbol.nterm class_rawexpr)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (">->")))))
                                           ((Pcoq.Symbol.nterm class_rawexpr)))
                           (fun t _ s _ ntn _ loc -> 
# 760 "vernac/g_vernac.mlg"
            VernacCoercion (CAst.make ~loc @@ ByNotation ntn, Some (s, t)) 
                                                     );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Coercion"))))))
                                                           ((Pcoq.Symbol.nterm global)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                           ((Pcoq.Symbol.nterm class_rawexpr)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (">->")))))
                                           ((Pcoq.Symbol.nterm class_rawexpr)))
                           (fun t _ s _ qid _ loc -> 
# 757 "vernac/g_vernac.mlg"
            VernacCoercion (CAst.make ~loc @@ AN qid, Some(s, t)) 
                                                     );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Identity"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Coercion"))))))
                                                           ((Pcoq.Symbol.nterm identref)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                           ((Pcoq.Symbol.nterm class_rawexpr)))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (">->")))))
                                           ((Pcoq.Symbol.nterm class_rawexpr)))
                           (fun t _ s _ f _ _ loc -> 
# 754 "vernac/g_vernac.mlg"
             VernacIdentityCoercion (f, s, t) 
                                                     );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Coercion"))))))
                                                           ((Pcoq.Symbol.nterm global)))
                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                           [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm univ_decl))))
                                                            ((Pcoq.Symbol.nterm def_body)))
                                                            (fun d u loc -> 
                                                            
# 748 "vernac/g_vernac.mlg"
                                                                                        u, d 
                                                            )]))))
                           (fun ud qid _ loc -> 
# 749 "vernac/g_vernac.mlg"
            match ud with Some (u, d) -> let s = coerce_reference_to_id qid in
          VernacDefinition ((NoDischarge,Coercion),((CAst.make ?loc:qid.CAst.loc (Name s)),u),d)
          | None -> VernacCoercion (CAst.make ~loc @@ AN qid, None) 
                                                );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Canonical"))))))
                                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                           [Pcoq.Rules.make 
                                                           (Pcoq.Rule.next_norec 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Structure"))))))
                                                           (fun _ loc -> 
                                                           
# 744 "vernac/g_vernac.mlg"
                                                       ()
                                                           )]))))
                                           ((Pcoq.Symbol.nterm by_notation)))
                           (fun ntn _ _ loc -> 
# 745 "vernac/g_vernac.mlg"
            VernacCanonical CAst.(make ~loc @@ ByNotation ntn) 
                                               );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Canonical"))))))
                                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                           [Pcoq.Rules.make 
                                                           (Pcoq.Rule.next_norec 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Structure"))))))
                                                           (fun _ loc -> 
                                                           
# 737 "vernac/g_vernac.mlg"
                                                       ()
                                                           )]))))
                                                           ((Pcoq.Symbol.nterm global)))
                                           ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                           [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm univ_decl))))
                                                            ((Pcoq.Symbol.nterm def_body)))
                                                            (fun d u loc -> 
                                                            
# 737 "vernac/g_vernac.mlg"
                                                                                                                            (u,d) 
                                                            )]))))
                           (fun ud qid _ _ loc -> 
# 738 "vernac/g_vernac.mlg"
            match ud with
           | None ->
             VernacCanonical CAst.(make ?loc:qid.CAst.loc @@ AN qid)
           | Some (u,d) ->
             let s = coerce_reference_to_id qid in
             VernacDefinition ((NoDischarge,CanonicalStructure),((CAst.make ?loc:qid.CAst.loc (Name s)),u),d) 
                                                  );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Strategy"))))))
                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.rules 
                                           [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.next_norec 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.nterm strategy_level)))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                            ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm smart_global)))))
                                                            ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                                            (fun _ q _ v
                                                            loc -> 
# 734 "vernac/g_vernac.mlg"
                                                                        (v,q) 
                                                                   )])))))
                           (fun l _ loc -> 
# 735 "vernac/g_vernac.mlg"
              VernacSetStrategy l 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Opaque"))))))
                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm smart_global)))))
                           (fun l _ loc -> 
# 732 "vernac/g_vernac.mlg"
            VernacSetOpacity (Conv_oracle.Opaque, l) 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Transparent"))))))
                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm smart_global)))))
                           (fun l _ loc -> 
# 730 "vernac/g_vernac.mlg"
            VernacSetOpacity (Conv_oracle.transparent, l) 
                                           )]))
        in let () = assert (Pcoq.Entry.is_empty args_modifier) in
        let () =
        Pcoq.grammar_extend args_modifier
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("clear"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("implicits"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("and"))))))
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("scopes"))))))
                                  (fun _ _ _ _ loc -> 
# 824 "vernac/g_vernac.mlg"
            [`ClearImplicits; `ClearScopes] 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("clear"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("scopes"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("and"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("implicits"))))))
                                 (fun _ _ _ _ loc -> 
# 822 "vernac/g_vernac.mlg"
            [`ClearImplicits; `ClearScopes] 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("extra"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("scopes"))))))
                                 (fun _ _ loc -> 
# 820 "vernac/g_vernac.mlg"
                                           [`ExtraScopes] 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("assert"))))))
                                 (fun _ loc -> 
# 819 "vernac/g_vernac.mlg"
                            [`Assert] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("rename"))))))
                                 (fun _ loc -> 
# 818 "vernac/g_vernac.mlg"
                            [`Rename] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("clear"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("bidirectionality"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("hint"))))))
                                 (fun _ _ _ loc -> 
# 817 "vernac/g_vernac.mlg"
                                                                   [`ClearBidiHint] 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("clear"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("scopes"))))))
                                 (fun _ _ loc -> 
# 816 "vernac/g_vernac.mlg"
                                           [`ClearScopes] 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("clear"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("implicits"))))))
                                 (fun _ _ loc -> 
# 815 "vernac/g_vernac.mlg"
                                              [`ClearImplicits] 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("default"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("implicits"))))))
                                 (fun _ _ loc -> 
# 814 "vernac/g_vernac.mlg"
                                                [`DefaultImplicits] 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("simpl"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("never"))))))
                                 (fun _ _ loc -> 
# 813 "vernac/g_vernac.mlg"
                                          [`ReductionNeverUnfold] 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("simpl"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("nomatch"))))))
                                 (fun _ _ loc -> 
# 812 "vernac/g_vernac.mlg"
                                            [`ReductionDontExposeCase] 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty scope_delimiter) in
        let () =
        Pcoq.grammar_extend scope_delimiter
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("%")))))
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                  (fun key _ loc -> 
# 828 "vernac/g_vernac.mlg"
                              key 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty argument_spec) in
        let () =
        Pcoq.grammar_extend argument_spec
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.token (Tok.PKEYWORD ("!"))))))
                                                                  ((Pcoq.Symbol.nterm name)))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm scope_delimiter))))
                                  (fun s id b loc -> 
# 832 "vernac/g_vernac.mlg"
         id.CAst.v, not (Option.is_empty b), Option.map (fun x -> CAst.make ~loc x) s 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty arg_specs) in
        let () =
        Pcoq.grammar_extend arg_specs
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm argument_spec)))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm scope_delimiter))))
                                  (fun sc _ items _ loc -> 
# 861 "vernac/g_vernac.mlg"
         let f x = match sc, x with
         | None, x -> x | x, None -> Option.map (fun y -> CAst.make ~loc y) x
         | Some _, Some _ -> user_err ~loc Pp.(str "scope declared twice") in
       List.map (fun (name,recarg_like,notation_scope) ->
           RealArg { name=name; recarg_like=recarg_like;
                 notation_scope=f notation_scope;
                 implicit_status = MaxImplicit}) items 
                                                           );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm argument_spec)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm scope_delimiter))))
                                 (fun sc _ items _ loc -> 
# 853 "vernac/g_vernac.mlg"
         let f x = match sc, x with
         | None, x -> x | x, None -> Option.map (fun y -> CAst.make ~loc y) x
         | Some _, Some _ -> user_err ~loc Pp.(str "scope declared twice") in
       List.map (fun (name,recarg_like,notation_scope) ->
           RealArg { name=name; recarg_like=recarg_like;
                 notation_scope=f notation_scope;
                 implicit_status = NonMaxImplicit}) items 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm argument_spec)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm scope_delimiter))))
                                 (fun sc _ items _ loc -> 
# 845 "vernac/g_vernac.mlg"
         let f x = match sc, x with
         | None, x -> x | x, None -> Option.map (fun y -> CAst.make ~loc y) x
         | Some _, Some _ -> user_err ~loc Pp.(str "scope declared twice") in
       List.map (fun (name,recarg_like,notation_scope) ->
           RealArg { name=name; recarg_like=recarg_like;
                 notation_scope=f notation_scope;
                 implicit_status = Explicit}) items 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("&")))))
                                 (fun _ loc -> 
# 843 "vernac/g_vernac.mlg"
               [BidiArg] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("/")))))
                                 (fun _ loc -> 
# 842 "vernac/g_vernac.mlg"
               [VolatileArg] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm argument_spec)))
                                 (fun item loc -> 
# 838 "vernac/g_vernac.mlg"
        let name, recarg_like, notation_scope = item in
      [RealArg { name=name; recarg_like=recarg_like;
             notation_scope=notation_scope;
             implicit_status = Explicit}] 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty implicits_alt) in
        let () =
        Pcoq.grammar_extend implicits_alt
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm name)))))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                  (fun _ items _ loc -> 
# 876 "vernac/g_vernac.mlg"
         List.map (fun name -> (name.CAst.v, MaxImplicit)) items 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm name)))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ items _ loc -> 
# 874 "vernac/g_vernac.mlg"
         List.map (fun name -> (name.CAst.v, NonMaxImplicit)) items 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm name)))
                                 (fun name loc -> 
# 872 "vernac/g_vernac.mlg"
                       [(name.CAst.v, Explicit)] 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty instance_name) in
        let () =
        Pcoq.grammar_extend instance_name
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 882 "vernac/g_vernac.mlg"
             ((CAst.make ~loc Anonymous), None), []  
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ident_decl)))
                                                 ((Pcoq.Symbol.nterm binders)))
                                 (fun bl name loc -> 
# 881 "vernac/g_vernac.mlg"
            (CAst.map (fun id -> Name id) (fst name), snd name), bl 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty hint_info) in
        let () =
        Pcoq.grammar_extend hint_info
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 887 "vernac/g_vernac.mlg"
             { Typeclasses.hint_priority = None; hint_pattern = None } 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm natural))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm constr_pattern))))
                                 (fun pat i _ loc -> 
# 886 "vernac/g_vernac.mlg"
           { Typeclasses.hint_priority = i; hint_pattern = pat } 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty reserv_list) in
        let () =
        Pcoq.grammar_extend reserv_list
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm simple_reserv)))
                                  (fun b loc -> 
# 890 "vernac/g_vernac.mlg"
                                                                   [b] 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm reserv_tuple)))))
                                 (fun bl loc -> 
# 890 "vernac/g_vernac.mlg"
                                     bl 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty reserv_tuple) in
        let () =
        Pcoq.grammar_extend reserv_tuple
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm simple_reserv)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ a _ loc -> 
# 893 "vernac/g_vernac.mlg"
                                         a 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty simple_reserv) in
        let () =
        Pcoq.grammar_extend simple_reserv
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm identref)))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun c _ idl loc -> 
# 896 "vernac/g_vernac.mlg"
                                                    (idl,c) 
                                                      )])]))
        in ()

let _ = let printable = Pcoq.Entry.make "printable"
        and printunivs_subgraph = Pcoq.Entry.make "printunivs_subgraph"
        and locatable = Pcoq.Entry.make "locatable"
        and option_setting = Pcoq.Entry.make "option_setting"
        and table_value = Pcoq.Entry.make "table_value"
        and setting_name = Pcoq.Entry.make "setting_name"
        and ne_in_or_out_modules = Pcoq.Entry.make "ne_in_or_out_modules"
        and in_or_out_modules = Pcoq.Entry.make "in_or_out_modules"
        and comment = Pcoq.Entry.make "comment"
        and positive_search_mark = Pcoq.Entry.make "positive_search_mark"
        and search_item = Pcoq.Entry.make "search_item"
        and logical_kind = Pcoq.Entry.make "logical_kind"
        and extended_def_token = Pcoq.Entry.make "extended_def_token"
        and search_where = Pcoq.Entry.make "search_where"
        and univ_name_list = Pcoq.Entry.make "univ_name_list"
        in
        let () =
        Pcoq.grammar_extend gallina_ext
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Export"))))))
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Unset"))))))
                                            ((Pcoq.Symbol.nterm setting_name)))
                            (fun table _ _ loc -> 
# 908 "vernac/g_vernac.mlg"
            VernacSetOption (true, table, OptionUnset) 
                                                  );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Export"))))))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD ("Set")))))
                                                           ((Pcoq.Symbol.nterm setting_name)))
                                           ((Pcoq.Symbol.nterm option_setting)))
                           (fun v table _ _ loc -> 
# 906 "vernac/g_vernac.mlg"
          VernacSetOption (true, table, v) 
                                                   )]))
        in let () = assert (Pcoq.Entry.is_empty command) in
        let () =
        Pcoq.grammar_extend command
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Remove"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm table_value)))))
                                  (fun v table _ loc -> 
# 989 "vernac/g_vernac.mlg"
            VernacRemoveOption ([table], v) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Remove"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm table_value)))))
                                 (fun v field table _ loc -> 
# 987 "vernac/g_vernac.mlg"
             VernacRemoveOption ([table;field], v) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Test"))))))
                                                 ((Pcoq.Symbol.nterm setting_name)))
                                 (fun table _ loc -> 
# 984 "vernac/g_vernac.mlg"
            VernacPrintOption table 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Test"))))))
                                                                 ((Pcoq.Symbol.nterm setting_name)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("for")))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm table_value)))))
                                 (fun v _ table _ loc -> 
# 982 "vernac/g_vernac.mlg"
             VernacMemOption (table, v) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Add"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm table_value)))))
                                 (fun v table _ loc -> 
# 979 "vernac/g_vernac.mlg"
            VernacAddOption ([table], v) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Add"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm table_value)))))
                                 (fun v field table _ loc -> 
# 973 "vernac/g_vernac.mlg"
             VernacAddOption ([table;field], v) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Print"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Table"))))))
                                                 ((Pcoq.Symbol.nterm setting_name)))
                                 (fun table _ _ loc -> 
# 970 "vernac/g_vernac.mlg"
            VernacPrintOption table 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Unset"))))))
                                                 ((Pcoq.Symbol.nterm setting_name)))
                                 (fun table _ loc -> 
# 967 "vernac/g_vernac.mlg"
            VernacSetOption (false, table, OptionUnset) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Set")))))
                                                                 ((Pcoq.Symbol.nterm setting_name)))
                                                 ((Pcoq.Symbol.nterm option_setting)))
                                 (fun v table _ loc -> 
# 965 "vernac/g_vernac.mlg"
            VernacSetOption (false, table, v) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Add"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("ML"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Path"))))))
                                                 ((Pcoq.Symbol.nterm ne_string)))
                                 (fun dir _ _ _ loc -> 
# 961 "vernac/g_vernac.mlg"
            VernacAddMLPath dir 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Inspect"))))))
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n _ loc -> 
# 958 "vernac/g_vernac.mlg"
                                          VernacPrint (PrintInspect n) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Print"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Namespace"))))))
                                                 ((Pcoq.Symbol.nterm dirpath)))
                                 (fun ns _ _ loc -> 
# 957 "vernac/g_vernac.mlg"
            VernacPrint (PrintNamespace ns) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Print"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Module"))))))
                                                 ((Pcoq.Symbol.nterm global)))
                                 (fun qid _ _ loc -> 
# 955 "vernac/g_vernac.mlg"
            VernacPrint (PrintModule qid) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Print"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Module"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                                 ((Pcoq.Symbol.nterm global)))
                                 (fun qid _ _ _ loc -> 
# 953 "vernac/g_vernac.mlg"
            VernacPrint (PrintModuleType qid) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Print"))))))
                                                                 ((Pcoq.Symbol.nterm smart_global)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm univ_name_list))))
                                 (fun l qid _ loc -> 
# 951 "vernac/g_vernac.mlg"
                                                                       VernacPrint (PrintName (qid,l)) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Print"))))))
                                                 ((Pcoq.Symbol.nterm printable)))
                                 (fun p _ loc -> 
# 950 "vernac/g_vernac.mlg"
                                          VernacPrint p 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("Type")))))
                                                 ((Pcoq.Symbol.nterm lconstr)))
                                 (fun c _ loc -> 
# 947 "vernac/g_vernac.mlg"
                                 VernacGlobalCheck c 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Remove"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("LoadPath"))))))
                                                 ((Pcoq.Symbol.nterm ne_string)))
                                 (fun dir _ _ loc -> 
# 944 "vernac/g_vernac.mlg"
            VernacRemoveLoadPath dir 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Add"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Rec"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("LoadPath"))))))
                                                                 ((Pcoq.Symbol.nterm ne_string)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm dirpath)))
                                 (fun logical_path _ physical_path _ _ _
                                 loc -> 
# 941 "vernac/g_vernac.mlg"
            VernacAddLoadPath { implicit = true; logical_path; physical_path } 
                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Add"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("LoadPath"))))))
                                                                 ((Pcoq.Symbol.nterm ne_string)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm dirpath)))
                                 (fun logical_path _ physical_path _ _ loc ->
                                 
# 939 "vernac/g_vernac.mlg"
            VernacAddLoadPath { implicit = false; logical_path; physical_path } 
                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Locate"))))))
                                                 ((Pcoq.Symbol.nterm locatable)))
                                 (fun l _ loc -> 
# 935 "vernac/g_vernac.mlg"
                                           VernacLocate l 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Declare"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("ML"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Module"))))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm ne_string)))))
                                 (fun l _ _ _ loc -> 
# 933 "vernac/g_vernac.mlg"
            VernacDeclareMLModule l 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Load"))))))
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.stop)
                                                                 (fun loc ->
                                                                 
# 929 "vernac/g_vernac.mlg"
                                                                       false 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Verbose"))))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 929 "vernac/g_vernac.mlg"
                                                         true 
                                                                 )])))
                                                 ((Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                  (fun s
                                                                  loc -> 
                                                                  
# 930 "vernac/g_vernac.mlg"
                                                      s 
                                                                  );
                                                 Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ne_string)))
                                                                 (fun s
                                                                 loc -> 
                                                                 
# 930 "vernac/g_vernac.mlg"
                                 s 
                                                                 )])))
                                 (fun s verbosely _ loc -> 
# 931 "vernac/g_vernac.mlg"
            VernacLoad (verbosely, s) 
                                                           );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Cd"))))))
                                                 ((Pcoq.Symbol.nterm ne_string)))
                                 (fun dir _ loc -> 
# 927 "vernac/g_vernac.mlg"
                                         VernacChdir (Some dir) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Cd"))))))
                                 (fun _ loc -> 
# 926 "vernac/g_vernac.mlg"
                        VernacChdir None 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Pwd"))))))
                                 (fun _ loc -> 
# 925 "vernac/g_vernac.mlg"
                         VernacChdir None 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Declare"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scope"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun sc _ _ loc -> 
# 922 "vernac/g_vernac.mlg"
            VernacDeclareScope sc 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Declare"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Instance"))))))
                                                                 ((Pcoq.Symbol.nterm ident_decl)))
                                                                 ((Pcoq.Symbol.nterm binders)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterml term ("200"))))
                                                 ((Pcoq.Symbol.nterm hint_info)))
                                 (fun info t _ bl id _ _ loc -> 
# 918 "vernac/g_vernac.mlg"
             VernacDeclareInstance (id, bl, t, info) 
                                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Comments"))))))
                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm comment))))
                                 (fun l _ loc -> 
# 912 "vernac/g_vernac.mlg"
                                                 VernacComments l 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty query_command) in
        let () =
        Pcoq.grammar_extend query_command
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Search"))))))
                                                                  ((Pcoq.Symbol.nterm search_query)))
                                                                  ((Pcoq.Symbol.nterm search_queries)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                  (fun _ l s _ loc -> 
# 1006 "vernac/g_vernac.mlg"
            let (sl,m) = l in fun g -> VernacSearch (Search (s::sl),g, m) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("SearchRewrite"))))))
                                                                 ((Pcoq.Symbol.nterm constr_pattern)))
                                                                 ((Pcoq.Symbol.nterm in_or_out_modules)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ l c _ loc -> 
# 1004 "vernac/g_vernac.mlg"
            fun g -> VernacSearch (SearchRewrite c,g, l) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("SearchPattern"))))))
                                                                 ((Pcoq.Symbol.nterm constr_pattern)))
                                                                 ((Pcoq.Symbol.nterm in_or_out_modules)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ l c _ loc -> 
# 1002 "vernac/g_vernac.mlg"
            fun g -> VernacSearch (SearchPattern c,g, l) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("About"))))))
                                                                 ((Pcoq.Symbol.nterm smart_global)))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm univ_name_list))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ l qid _ loc -> 
# 1000 "vernac/g_vernac.mlg"
           fun g -> VernacPrint (PrintAbout (qid,l,g)) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Check"))))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ c _ loc -> 
# 997 "vernac/g_vernac.mlg"
           fun g -> VernacCheckMayEval (None, g, c) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Compute"))))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ c _ loc -> 
# 995 "vernac/g_vernac.mlg"
            fun g -> VernacCheckMayEval (Some (Genredexpr.CbvVm None), g, c) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Eval"))))))
                                                                 ((Pcoq.Symbol.nterm red_expr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ c _ r _ loc -> 
# 993 "vernac/g_vernac.mlg"
            fun g -> VernacCheckMayEval (Some r, g, c) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty printable) in
        let () =
        Pcoq.grammar_extend printable
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("Registered"))))))
                                  (fun _ loc -> 
# 1059 "vernac/g_vernac.mlg"
                                PrintRegistered 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Strategies"))))))
                                 (fun _ loc -> 
# 1058 "vernac/g_vernac.mlg"
                                PrintStrategy None 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Strategy"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid _ loc -> 
# 1057 "vernac/g_vernac.mlg"
                                                  PrintStrategy (Some qid) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("All"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Dependencies"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid _ _ loc -> 
# 1056 "vernac/g_vernac.mlg"
                                                                   PrintAssumptions (true, true, qid) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Transparent"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Dependencies"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid _ _ loc -> 
# 1055 "vernac/g_vernac.mlg"
                                                                           PrintAssumptions (false, true, qid) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Opaque"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Dependencies"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid _ _ loc -> 
# 1054 "vernac/g_vernac.mlg"
                                                                      PrintAssumptions (true, false, qid) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Assumptions"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid _ loc -> 
# 1053 "vernac/g_vernac.mlg"
                                                     PrintAssumptions (false, false, qid) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.stop)
                                                                 (fun loc ->
                                                                 
# 1050 "vernac/g_vernac.mlg"
                                                false 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Sorted"))))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 1050 "vernac/g_vernac.mlg"
                                  true 
                                                                 )])))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Universes"))))))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm printunivs_subgraph))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ne_string))))
                                 (fun fopt g _ b loc -> 
# 1052 "vernac/g_vernac.mlg"
          PrintUniverses (b, g, fopt) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Implicit"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid _ loc -> 
# 1049 "vernac/g_vernac.mlg"
                                                  PrintImplicit qid 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Visibility"))))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.token (Tok.PIDENT (None))))))
                                 (fun s _ loc -> 
# 1048 "vernac/g_vernac.mlg"
                                               PrintVisibility s 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scope"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun s _ loc -> 
# 1047 "vernac/g_vernac.mlg"
                                      PrintScope s 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Scopes"))))))
                                 (fun _ loc -> 
# 1046 "vernac/g_vernac.mlg"
                            PrintScopes 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("HintDb"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun s _ loc -> 
# 1045 "vernac/g_vernac.mlg"
                                       PrintHintDbName s 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Hint"))))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                 (fun _ _ loc -> 
# 1044 "vernac/g_vernac.mlg"
                               PrintHintDb 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Hint"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid _ loc -> 
# 1043 "vernac/g_vernac.mlg"
                                              PrintHint qid 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Hint"))))))
                                 (fun _ loc -> 
# 1042 "vernac/g_vernac.mlg"
                          PrintHintGoal 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Options"))))))
                                 (fun _ loc -> 
# 1041 "vernac/g_vernac.mlg"
                             PrintTables (* A Synonymous to Tables *) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Tables"))))))
                                 (fun _ loc -> 
# 1040 "vernac/g_vernac.mlg"
                            PrintTables 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Typing"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Flags"))))))
                                 (fun _ _ loc -> 
# 1039 "vernac/g_vernac.mlg"
                                           PrintTypingFlags 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Canonical"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Projections"))))))
                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm smart_global))))
                                 (fun qids _ _ loc -> 
# 1038 "vernac/g_vernac.mlg"
            PrintCanonicalConversions qids 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Coercion"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Paths"))))))
                                                                 ((Pcoq.Symbol.nterm class_rawexpr)))
                                                 ((Pcoq.Symbol.nterm class_rawexpr)))
                                 (fun t s _ _ loc -> 
# 1036 "vernac/g_vernac.mlg"
            PrintCoercionPaths (s,t) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Coercions"))))))
                                 (fun _ loc -> 
# 1034 "vernac/g_vernac.mlg"
                               PrintCoercions 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Instances"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid _ loc -> 
# 1033 "vernac/g_vernac.mlg"
                                                   PrintInstances qid 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("TypeClasses"))))))
                                 (fun _ loc -> 
# 1032 "vernac/g_vernac.mlg"
                                 PrintTypeClasses 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Classes"))))))
                                 (fun _ loc -> 
# 1031 "vernac/g_vernac.mlg"
                              PrintClasses 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Graph"))))))
                                 (fun _ loc -> 
# 1030 "vernac/g_vernac.mlg"
                           PrintGraph 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Debug"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("GC"))))))
                                 (fun _ _ loc -> 
# 1029 "vernac/g_vernac.mlg"
                                       PrintDebugGC 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("ML"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Modules"))))))
                                 (fun _ _ loc -> 
# 1028 "vernac/g_vernac.mlg"
                                         PrintMLModules 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("ML"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Path"))))))
                                 (fun _ _ loc -> 
# 1027 "vernac/g_vernac.mlg"
                                      PrintMLLoadPath 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Notation"))))))
                                                                 ((Pcoq.Symbol.nterm string)))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("in"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("custom"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun ent _ _ ntn _ loc -> 
# 1025 "vernac/g_vernac.mlg"
          PrintNotation (Constrexpr.InCustomEntry ent, ntn) 
                                                           );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Notation"))))))
                                                 ((Pcoq.Symbol.nterm string)))
                                 (fun ntn _ loc -> 
# 1023 "vernac/g_vernac.mlg"
          PrintNotation (Constrexpr.InConstrEntry, ntn) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Libraries"))))))
                                 (fun _ loc -> 
# 1020 "vernac/g_vernac.mlg"
                               PrintLibraries 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("LoadPath"))))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm dirpath))))
                                 (fun dir _ loc -> 
# 1019 "vernac/g_vernac.mlg"
                                                 PrintLoadPath dir 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Custom"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Grammar"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun ent _ _ loc -> 
# 1018 "vernac/g_vernac.mlg"
            PrintCustomGrammar ent 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Grammar"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun ent _ loc -> 
# 1015 "vernac/g_vernac.mlg"
            PrintGrammar ent 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Section"))))))
                                                 ((Pcoq.Symbol.nterm global)))
                                 (fun s _ loc -> 
# 1012 "vernac/g_vernac.mlg"
                                         PrintSectionContext s 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("All"))))))
                                 (fun _ loc -> 
# 1011 "vernac/g_vernac.mlg"
                         PrintFullContext 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Term"))))))
                                                                 ((Pcoq.Symbol.nterm smart_global)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm univ_name_list))))
                                 (fun l qid _ loc -> 
# 1010 "vernac/g_vernac.mlg"
                                                                      PrintName (qid,l) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty printunivs_subgraph)
        in
        let () =
        Pcoq.grammar_extend printunivs_subgraph
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Subgraph"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm reference))))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ l _ _ loc -> 
# 1063 "vernac/g_vernac.mlg"
                                                             l 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty class_rawexpr) in
        let () =
        Pcoq.grammar_extend class_rawexpr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm smart_global)))
                                  (fun qid loc -> 
# 1068 "vernac/g_vernac.mlg"
                                RefClass qid 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Sortclass"))))))
                                 (fun _ loc -> 
# 1067 "vernac/g_vernac.mlg"
                               SortClass 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Funclass"))))))
                                 (fun _ loc -> 
# 1066 "vernac/g_vernac.mlg"
                              FunClass 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty locatable) in
        let () =
        Pcoq.grammar_extend locatable
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Module"))))))
                                                  ((Pcoq.Symbol.nterm global)))
                                  (fun qid _ loc -> 
# 1075 "vernac/g_vernac.mlg"
                                          LocateModule qid 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Library"))))))
                                                 ((Pcoq.Symbol.nterm global)))
                                 (fun qid _ loc -> 
# 1074 "vernac/g_vernac.mlg"
                                           LocateLibrary qid 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("File"))))))
                                                 ((Pcoq.Symbol.nterm ne_string)))
                                 (fun f _ loc -> 
# 1073 "vernac/g_vernac.mlg"
                                         LocateFile f 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Term"))))))
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid _ loc -> 
# 1072 "vernac/g_vernac.mlg"
                                              LocateTerm qid 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm smart_global)))
                                 (fun qid loc -> 
# 1071 "vernac/g_vernac.mlg"
                                LocateAny qid 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty option_setting) in
        let () =
        Pcoq.grammar_extend option_setting
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                  (fun s loc -> 
# 1080 "vernac/g_vernac.mlg"
                            OptionSetString s 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm integer)))
                                 (fun n loc -> 
# 1079 "vernac/g_vernac.mlg"
                            OptionSetInt n 
                                               );
                                 Pcoq.Production.make (Pcoq.Rule.stop)
                                 (fun loc -> 
# 1078 "vernac/g_vernac.mlg"
             OptionSetTrue 
                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty table_value) in
        let () =
        Pcoq.grammar_extend table_value
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                  (fun s loc -> 
# 1084 "vernac/g_vernac.mlg"
                           Goptions.StringRefValue s 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm global)))
                                 (fun id loc -> 
# 1083 "vernac/g_vernac.mlg"
                           Goptions.QualidRefValue id 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty setting_name) in
        let () =
        Pcoq.grammar_extend setting_name
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                   (fun x
                                                                   loc -> 
                                                                   
# 1087 "vernac/g_vernac.mlg"
                                    x 
                                                                   )])))))
                                  (fun fl loc -> 
# 1087 "vernac/g_vernac.mlg"
                                               fl 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty ne_in_or_out_modules)
        in
        let () =
        Pcoq.grammar_extend ne_in_or_out_modules
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("outside"))))))
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                  (fun l _ loc -> 
# 1092 "vernac/g_vernac.mlg"
                                               SearchOutside l 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                 (fun l _ loc -> 
# 1091 "vernac/g_vernac.mlg"
                                    SearchInside l 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inside"))))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                 (fun l _ loc -> 
# 1090 "vernac/g_vernac.mlg"
                                              SearchInside l 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty in_or_out_modules) in
        let () =
        Pcoq.grammar_extend in_or_out_modules
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 1096 "vernac/g_vernac.mlg"
             SearchOutside [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm ne_in_or_out_modules)))
                                 (fun m loc -> 
# 1095 "vernac/g_vernac.mlg"
                                      m 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty comment) in
        let () =
        Pcoq.grammar_extend comment
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm natural)))
                                  (fun n loc -> 
# 1101 "vernac/g_vernac.mlg"
                         CommentInt n 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                 (fun s loc -> 
# 1100 "vernac/g_vernac.mlg"
                        CommentString s 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm constr)))
                                 (fun c loc -> 
# 1099 "vernac/g_vernac.mlg"
                        CommentConstr c 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty positive_search_mark)
        in
        let () =
        Pcoq.grammar_extend positive_search_mark
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 1104 "vernac/g_vernac.mlg"
                                true 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                 (fun _ loc -> 
# 1104 "vernac/g_vernac.mlg"
                 false 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty search_query) in
        let () =
        Pcoq.grammar_extend search_query
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm positive_search_mark)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm search_query)))) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                  (fun _ l _ b loc -> 
# 1108 "vernac/g_vernac.mlg"
                                                                                        (b, SearchDisjConj l) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm positive_search_mark)))
                                                 ((Pcoq.Symbol.nterm search_item)))
                                 (fun s b loc -> 
# 1107 "vernac/g_vernac.mlg"
                                                       (b, SearchLiteral s) 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty search_item) in
        let () =
        Pcoq.grammar_extend search_item
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr_pattern)))
                                  (fun p loc -> 
# 1121 "vernac/g_vernac.mlg"
              SearchSubPattern ((Anywhere,false),p) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_id_colon)))
                                                                 ((Pcoq.Symbol.nterm search_where)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm constr_pattern)))
                                 (fun p _ where _ loc -> 
# 1119 "vernac/g_vernac.mlg"
              SearchSubPattern (where,p) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ne_string)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm scope_delimiter))))
                                 (fun sc s loc -> 
# 1117 "vernac/g_vernac.mlg"
              SearchString ((Anywhere,false),s,sc) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("is"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                 ((Pcoq.Symbol.nterm logical_kind)))
                                 (fun kl _ _ loc -> 
# 1115 "vernac/g_vernac.mlg"
              SearchKind kl 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_id_colon)))
                                                                 ((Pcoq.Symbol.nterm search_where)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm ne_string)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm scope_delimiter))))
                                 (fun sc s _ where _ loc -> 
# 1113 "vernac/g_vernac.mlg"
              SearchString (where,s,sc) 
                                                            )])]))
        in let () = assert (Pcoq.Entry.is_empty logical_kind) in
        let () =
        Pcoq.grammar_extend logical_kind
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("Primitive"))))))
                                  (fun _ loc -> 
# 1129 "vernac/g_vernac.mlg"
                               IsPrimitive 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm extended_def_token)))
                                 (fun k loc -> 
# 1128 "vernac/g_vernac.mlg"
                                    IsDefinition k 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Context"))))))
                                 (fun k loc -> 
# 1127 "vernac/g_vernac.mlg"
                                 IsAssumption Context 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm assumption_token)))
                                 (fun k loc -> 
# 1126 "vernac/g_vernac.mlg"
                                  IsAssumption (snd k) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm thm_token)))
                                 (fun k loc -> 
# 1125 "vernac/g_vernac.mlg"
                           IsProof k 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty extended_def_token)
        in
        let () =
        Pcoq.grammar_extend extended_def_token
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("Method"))))))
                                  (fun _ loc -> 
# 1138 "vernac/g_vernac.mlg"
                            Method 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Field"))))))
                                 (fun _ loc -> 
# 1137 "vernac/g_vernac.mlg"
                           StructureComponent 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Canonical"))))))
                                 (fun _ loc -> 
# 1136 "vernac/g_vernac.mlg"
                               CanonicalStructure 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Scheme"))))))
                                 (fun _ loc -> 
# 1135 "vernac/g_vernac.mlg"
                            Scheme 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Instance"))))))
                                 (fun _ loc -> 
# 1134 "vernac/g_vernac.mlg"
                              Instance 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Coercion"))))))
                                 (fun _ loc -> 
# 1133 "vernac/g_vernac.mlg"
                              Coercion 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm def_token)))
                                 (fun k loc -> 
# 1132 "vernac/g_vernac.mlg"
                           snd k 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty search_where) in
        let () =
        Pcoq.grammar_extend search_where
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("headconcl"))))))
                                  (fun _ loc -> 
# 1145 "vernac/g_vernac.mlg"
                               InConcl, true 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("headhyp"))))))
                                 (fun _ loc -> 
# 1144 "vernac/g_vernac.mlg"
                             InHyp, true 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("concl"))))))
                                 (fun _ loc -> 
# 1143 "vernac/g_vernac.mlg"
                           InConcl, false 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("hyp"))))))
                                 (fun _ loc -> 
# 1142 "vernac/g_vernac.mlg"
                         InHyp, false 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("head"))))))
                                 (fun _ loc -> 
# 1141 "vernac/g_vernac.mlg"
                          Anywhere, true 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty search_queries) in
        let () =
        Pcoq.grammar_extend search_queries
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 1151 "vernac/g_vernac.mlg"
             ([],SearchOutside []) 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm search_query)))
                                                 ((Pcoq.Symbol.nterm search_queries)))
                                 (fun l s loc -> 
# 1150 "vernac/g_vernac.mlg"
          let (sl,m) = l in (s::sl,m) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm ne_in_or_out_modules)))
                                 (fun m loc -> 
# 1148 "vernac/g_vernac.mlg"
                                      ([],m) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty univ_name_list) in
        let () =
        Pcoq.grammar_extend univ_name_list
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("@{")))))
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm name))))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                  (fun _ l _ loc -> 
# 1155 "vernac/g_vernac.mlg"
                                         l 
                                                    )])]))
        in ()

let _ = let () =
        Pcoq.grammar_extend command
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Declare"))))))
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Custom"))))))
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Entry"))))))
                                            ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                            (fun s _ _ _ loc -> 
# 1186 "vernac/g_vernac.mlg"
             VernacDeclareCustomEntry s 
                                                );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Declare"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Reduction"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                           ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                           ((Pcoq.Symbol.nterm red_expr)))
                           (fun r _ s _ _ loc -> 
# 1181 "vernac/g_vernac.mlg"
             VernacDeclareReduction (s,r) 
                                                 );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Debug"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Off"))))))
                           (fun _ _ loc -> 
# 1175 "vernac/g_vernac.mlg"
            VernacSetOption (false, ["Ltac";"Debug"], OptionUnset) 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Debug"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("On"))))))
                           (fun _ _ loc -> 
# 1172 "vernac/g_vernac.mlg"
            VernacSetOption (false, ["Ltac";"Debug"], OptionSetTrue) 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Back"))))))
                                           ((Pcoq.Symbol.nterm natural)))
                           (fun n _ loc -> 
# 1168 "vernac/g_vernac.mlg"
                                       VernacBack n 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Back"))))))
                           (fun _ loc -> 
# 1167 "vernac/g_vernac.mlg"
                          VernacBack 1 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Reset"))))))
                                           ((Pcoq.Symbol.nterm identref)))
                           (fun id _ loc -> 
# 1166 "vernac/g_vernac.mlg"
                                          VernacResetName id 
                                            );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Reset"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Initial"))))))
                           (fun _ _ loc -> 
# 1165 "vernac/g_vernac.mlg"
                                            VernacResetInitial 
                                           )]))
        in ()

let _ = let level = Pcoq.Entry.make "level"
        and syntax_modifier = Pcoq.Entry.make "syntax_modifier"
        and explicit_subentry = Pcoq.Entry.make "explicit_subentry"
        and at_level_opt = Pcoq.Entry.make "at_level_opt"
        and binder_interp = Pcoq.Entry.make "binder_interp"
        in
        let () = assert (Pcoq.Entry.is_empty syntax) in
        let () =
        Pcoq.grammar_extend syntax
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Reserved"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Notation"))))))
                                                                  ((Pcoq.Symbol.nterm ne_lstring)))
                                                  ((Pcoq.Symbol.nterm syntax_modifiers)))
                                  (fun l s _ _ loc -> 
# 1229 "vernac/g_vernac.mlg"
             VernacReservedNotation (false,(s,l)) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Reserved"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Infix"))))))
                                                                 ((Pcoq.Symbol.nterm ne_lstring)))
                                                 ((Pcoq.Symbol.nterm syntax_modifiers)))
                                 (fun l s _ _ loc -> 
# 1227 "vernac/g_vernac.mlg"
             VernacReservedNotation (true,(s,l)) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Format"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Notation"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                                                 ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                                 ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                 (fun fmt s n _ _ loc -> 
# 1224 "vernac/g_vernac.mlg"
             VernacNotationAddFormat (n,s,fmt) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Notation"))))))
                                                                 ((Pcoq.Symbol.nterm lstring)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm syntax_modifiers)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                  (fun sc _
                                                                  loc -> 
                                                                  
# 1221 "vernac/g_vernac.mlg"
                                         sc 
                                                                  )]))))
                                 (fun sc modl c _ s _ loc -> 
# 1222 "vernac/g_vernac.mlg"
             VernacNotation (false,c,(s,modl),sc) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Notation"))))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm ident))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                 ((Pcoq.Symbol.nterm syntax_modifiers)))
                                 (fun modl c _ idl id _ loc -> 
# 1217 "vernac/g_vernac.mlg"
             VernacSyntacticDefinition (id,(idl,c), modl) 
                                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Infix"))))))
                                                                 ((Pcoq.Symbol.nterm ne_lstring)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm syntax_modifiers)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                  (fun sc _
                                                                  loc -> 
                                                                  
# 1213 "vernac/g_vernac.mlg"
                                         sc 
                                                                  )]))))
                                 (fun sc modl p _ op _ loc -> 
# 1214 "vernac/g_vernac.mlg"
           VernacNotation (true,p,(op,modl),sc) 
                                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Bind"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scope"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm class_rawexpr)))))
                                 (fun refl _ sc _ _ loc -> 
# 1209 "vernac/g_vernac.mlg"
                                       VernacBindScope (sc,refl) 
                                                           );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Undelimit"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scope"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun sc _ _ loc -> 
# 1206 "vernac/g_vernac.mlg"
           VernacDelimiters (sc, None) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Delimit"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scope"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun key _ sc _ _ loc -> 
# 1204 "vernac/g_vernac.mlg"
           VernacDelimiters (sc, Some key) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Close"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scope"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun sc _ _ loc -> 
# 1201 "vernac/g_vernac.mlg"
           VernacOpenCloseScope (false,sc) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Open"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Scope"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun sc _ _ loc -> 
# 1198 "vernac/g_vernac.mlg"
           VernacOpenCloseScope (true,sc) 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty level) in
        let () =
        Pcoq.grammar_extend level
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("next"))))))
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("level"))))))
                                  (fun _ _ loc -> 
# 1237 "vernac/g_vernac.mlg"
                                         NextLevel 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("level"))))))
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n _ loc -> 
# 1236 "vernac/g_vernac.mlg"
                                        NumLevel n 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty syntax_modifier) in
        let () =
        Pcoq.grammar_extend syntax_modifier
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                  ((Pcoq.Symbol.nterm explicit_subentry)))
                                  (fun typ x loc -> 
# 1261 "vernac/g_vernac.mlg"
                                                SetEntryType (x,typ) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                 ((Pcoq.Symbol.nterm binder_interp)))
                                 (fun b x loc -> 
# 1260 "vernac/g_vernac.mlg"
                                          SetItemLevel ([x],Some b,DefaultLevel) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("scope"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun k _ _ x loc -> 
# 1259 "vernac/g_vernac.mlg"
                                                       SetItemScope([x],k) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                                 ((Pcoq.Symbol.nterm level)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm binder_interp))))
                                 (fun b lev _ x loc -> 
# 1258 "vernac/g_vernac.mlg"
          SetItemLevel ([x],b,lev) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.token (Tok.PIDENT (None)))) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("scope"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                  (fun k _ _
                                                                  loc -> 
                                                                  
# 1256 "vernac/g_vernac.mlg"
                                                fun x l -> SetItemScope(x::l,k) 
                                                                  );
                                                 Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                                 ((Pcoq.Symbol.nterm level)))
                                                                 (fun lev _
                                                                 loc -> 
                                                                 
# 1255 "vernac/g_vernac.mlg"
                                   fun x l -> SetItemLevel (x::l,None,lev) 
                                                                 )])))
                                 (fun v l _ x loc -> 
# 1256 "vernac/g_vernac.mlg"
                                                                                         v x l 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("format"))))))
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                                                 (fun s
                                                                 loc -> 
                                                                 
# 1249 "vernac/g_vernac.mlg"
                                              CAst.make ~loc s 
                                                                 )])))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                                                  (fun s
                                                                  loc -> 
                                                                  
# 1250 "vernac/g_vernac.mlg"
                                                  CAst.make ~loc s 
                                                                  )]))))
                                 (fun s2 s1 _ loc -> 
# 1251 "vernac/g_vernac.mlg"
            begin match s1, s2 with
          | { CAst.v = k }, Some s -> SetFormat (ExtraFormat (k,s))
          | s, None -> SetFormat (TextFormat s) end 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("only"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("parsing"))))))
                                 (fun _ _ loc -> 
# 1248 "vernac/g_vernac.mlg"
                                           SetOnlyParsing 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("only"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("printing"))))))
                                 (fun _ _ loc -> 
# 1247 "vernac/g_vernac.mlg"
                                            SetOnlyPrinting 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("no"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("associativity"))))))
                                 (fun _ _ loc -> 
# 1246 "vernac/g_vernac.mlg"
                                               SetAssoc Gramlib.Gramext.NonA 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("right"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("associativity"))))))
                                 (fun _ _ loc -> 
# 1245 "vernac/g_vernac.mlg"
                                                  SetAssoc Gramlib.Gramext.RightA 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("left"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("associativity"))))))
                                 (fun _ _ loc -> 
# 1244 "vernac/g_vernac.mlg"
                                                 SetAssoc Gramlib.Gramext.LeftA 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("custom"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("level"))))))
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n _ _ x _ _ loc -> 
# 1243 "vernac/g_vernac.mlg"
           SetCustomEntry (x,Some n) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("custom"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                 (fun x _ _ loc -> 
# 1241 "vernac/g_vernac.mlg"
                                             SetCustomEntry (x,None) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("level"))))))
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n _ _ loc -> 
# 1240 "vernac/g_vernac.mlg"
                                              SetLevel n 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty syntax_modifiers) in
        let () =
        Pcoq.grammar_extend syntax_modifiers
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 1266 "vernac/g_vernac.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm syntax_modifier)))
                                                                 (fun s
                                                                 loc -> 
                                                                 
# 1265 "vernac/g_vernac.mlg"
                                                  CAst.make ~loc s 
                                                                 )])) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ l _ loc -> 
# 1265 "vernac/g_vernac.mlg"
                                                                                         l 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty explicit_subentry) in
        let () =
        Pcoq.grammar_extend explicit_subentry
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("custom"))))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                  ((Pcoq.Symbol.nterm at_level_opt)))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm binder_interp))))
                                  (fun b n x _ loc -> 
# 1283 "vernac/g_vernac.mlg"
             ETConstr (InCustomEntry x,b,n) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("closed"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("binder"))))))
                                 (fun _ _ loc -> 
# 1281 "vernac/g_vernac.mlg"
                                            ETBinder false 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("strict"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("pattern"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("level"))))))
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n _ _ _ _ loc -> 
# 1280 "vernac/g_vernac.mlg"
                                                                               ETPattern (true,Some n) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("strict"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("pattern"))))))
                                 (fun _ _ loc -> 
# 1279 "vernac/g_vernac.mlg"
                                             ETPattern (true,None) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("pattern"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("level"))))))
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n _ _ _ loc -> 
# 1278 "vernac/g_vernac.mlg"
                                                               ETPattern (false,Some n) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("pattern"))))))
                                 (fun _ loc -> 
# 1277 "vernac/g_vernac.mlg"
                             ETPattern (false,None) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("constr"))))))
                                                                 ((Pcoq.Symbol.nterm at_level_opt)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm binder_interp))))
                                 (fun b n _ loc -> 
# 1276 "vernac/g_vernac.mlg"
                                                                     ETConstr (InConstrEntry,b,n) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("constr"))))))
                                 (fun _ loc -> 
# 1275 "vernac/g_vernac.mlg"
                            ETConstr (InConstrEntry,None,DefaultLevel) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("binder"))))))
                                 (fun _ loc -> 
# 1274 "vernac/g_vernac.mlg"
                            ETBinder true 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("bigint"))))))
                                 (fun _ loc -> 
# 1273 "vernac/g_vernac.mlg"
                            ETBigint 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("global"))))))
                                 (fun _ loc -> 
# 1272 "vernac/g_vernac.mlg"
                            ETGlobal 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("name"))))))
                                 (fun _ loc -> 
# 1271 "vernac/g_vernac.mlg"
                          ETName 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("ident"))))))
                                 (fun _ loc -> 
# 1270 "vernac/g_vernac.mlg"
                           ETIdent 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty at_level_opt) in
        let () =
        Pcoq.grammar_extend at_level_opt
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 1288 "vernac/g_vernac.mlg"
             DefaultLevel 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                 ((Pcoq.Symbol.nterm level)))
                                 (fun n _ loc -> 
# 1287 "vernac/g_vernac.mlg"
                             n 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty binder_interp) in
        let () =
        Pcoq.grammar_extend binder_interp
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("strict"))))))
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("pattern"))))))
                                  (fun _ _ _ loc -> 
# 1294 "vernac/g_vernac.mlg"
                                                   Notation_term.AsStrictPattern 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("pattern"))))))
                                 (fun _ _ loc -> 
# 1293 "vernac/g_vernac.mlg"
                                   Notation_term.AsNameOrPattern 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("name"))))))
                                 (fun _ _ loc -> 
# 1292 "vernac/g_vernac.mlg"
                                Notation_term.AsName 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("ident"))))))
                                 (fun _ _ loc -> 
# 1291 "vernac/g_vernac.mlg"
                                 warn_deprecated_as_ident_kind (); Notation_term.AsIdent 
                                                 )])]))
        in ()

