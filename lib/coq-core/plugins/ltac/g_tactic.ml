
# 11 "plugins/ltac/g_tactic.mlg"
 

open Pp
open CErrors
open Util
open Names
open Namegen
open Tacexpr
open Genredexpr
open Constrexpr
open Libnames
open Tok
open Tactypes
open Tactics
open Inv
open Locus

open Pcoq


let all_with delta = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;delta]

let err () = raise Stream.Failure

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let test_lpar_id_coloneq =
  let open Pcoq.Lookahead in
  to_entry "lpar_id_coloneq" begin
    lk_kw "(" >> lk_ident >> lk_kw ":="
  end

(* Hack to recognize "(x)" *)
let test_lpar_id_rpar =
  let open Pcoq.Lookahead in
  to_entry "lpar_id_coloneq" begin
    lk_kw "(" >> lk_ident >> lk_kw ")"
  end

(* idem for (x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  let open Pcoq.Lookahead in
  to_entry "test_lpar_idnum_coloneq" begin
    lk_kw "(" >> (lk_ident <+> lk_nat) >> lk_kw ":="
  end

(* idem for (x:t) *)
open Extraargs

(* idem for (x1..xn:t) [n^2 complexity but exceptional use] *)
let check_for_coloneq =
  Pcoq.Entry.(of_parser "lpar_id_colon"
    { parser_fun = fun strm ->
      let rec skip_to_rpar p n =
        match List.last (LStream.npeek n strm) with
        | KEYWORD "(" -> skip_to_rpar (p+1) (n+1)
        | KEYWORD ")" -> if Int.equal p 0 then n+1 else skip_to_rpar (p-1) (n+1)
        | KEYWORD "." -> err ()
        | _ -> skip_to_rpar p (n+1) in
      let rec skip_names n =
        match List.last (LStream.npeek n strm) with
        | IDENT _ | KEYWORD "_" -> skip_names (n+1)
        | KEYWORD ":" -> skip_to_rpar 0 (n+1) (* skip a constr *)
        | _ -> err () in
      let rec skip_binders n =
        match List.last (LStream.npeek n strm) with
        | KEYWORD "(" -> skip_binders (skip_names (n+1))
        | IDENT _ | KEYWORD "_" -> skip_binders (n+1)
        | KEYWORD ":=" -> ()
        | _ -> err () in
      match LStream.peek_nth 0 strm with
      | KEYWORD "(" -> skip_binders 2
      | _ -> err () })

let lookup_at_as_comma =
  let open Pcoq.Lookahead in
  to_entry "lookup_at_as_comma" begin
    lk_kws [",";"at";"as"]
  end

open Constr
open Prim
open Pltac

let mk_fix_tac (loc,id,bl,ann,ty) =
  let n =
    match bl,ann with
        [([_],_,_)], None -> 1
      | _, Some x ->
          let ids = List.map (fun x -> x.CAst.v) (List.flatten (List.map (fun (nal,_,_) -> nal) bl)) in
          (try List.index Names.Name.equal x.CAst.v ids
          with Not_found -> user_err ~loc Pp.(str "No such fix variable."))
      | _ -> user_err ~loc Pp.(str "Cannot guess decreasing argument of fix.") in
  let bl = List.map (fun (nal,bk,t) -> CLocalAssum (nal,bk,t)) bl in
  (id,n, CAst.make ~loc @@ CProdN(bl,ty))

let mk_cofix_tac (loc,id,bl,ann,ty) =
  let () = Option.iter (fun { CAst.loc = aloc } ->
      user_err ?loc:aloc
        (Pp.str"Annotation forbidden in cofix expression."))
      ann
  in
  let bl = List.map (fun (nal,bk,t) -> CLocalAssum (nal,bk,t)) bl in
  (id,if bl = [] then ty else CAst.make ~loc @@ CProdN(bl,ty))

(* Functions overloaded by quotifier *)
let destruction_arg_of_constr (c,lbind as clbind) = match lbind with
  | NoBindings ->
    begin
      try ElimOnIdent (CAst.make ?loc:(Constrexpr_ops.constr_loc c) (Constrexpr_ops.coerce_to_id c).CAst.v)
      with e when CErrors.noncritical e -> ElimOnConstr clbind
    end
  | _ -> ElimOnConstr clbind

let mkNumber n =
  Number (NumTok.Signed.of_int_string (string_of_int n))

let mkTacCase with_evar = function
  | [(clear,ElimOnConstr cl),(None,None),None],None ->
      TacCase (with_evar,(clear,cl))
  (* Reinterpret numbers as a notation for terms *)
  | [(clear,ElimOnAnonHyp n),(None,None),None],None ->
      TacCase (with_evar,
        (clear,(CAst.make @@ CPrim (mkNumber n),
         NoBindings)))
  (* Reinterpret ident as notations for variables in the context *)
  (* because we don't know if they are quantified or not *)
  | [(clear,ElimOnIdent id),(None,None),None],None ->
      TacCase (with_evar,(clear,(CAst.make @@ CRef (qualid_of_ident ?loc:id.CAst.loc id.CAst.v,None),NoBindings)))
  | ic ->
      if List.exists (function ((_, ElimOnAnonHyp _),_,_) -> true | _ -> false) (fst ic)
      then
        user_err Pp.(str "Use of numbers as direct arguments of 'case' is not supported.");
      TacInductionDestruct (false,with_evar,ic)

let rec mkCLambdaN_simple_loc ?loc bll c =
  match bll with
  | ({CAst.loc = loc1}::_ as idl,bk,t) :: bll ->
      CAst.make ?loc @@ CLambdaN ([CLocalAssum (idl,bk,t)],mkCLambdaN_simple_loc ?loc:(Loc.merge_opt loc1 loc) bll c)
  | ([],_,_) :: bll -> mkCLambdaN_simple_loc ?loc bll c
  | [] -> c

let mkCLambdaN_simple bl c = match bl with
  | [] -> c
  | h :: _ ->
    let loc = Loc.merge_opt (List.hd (pi1 h)).CAst.loc (Constrexpr_ops.constr_loc c) in
    mkCLambdaN_simple_loc ?loc bl c

let loc_of_ne_list l = Loc.merge_opt (List.hd l).CAst.loc (List.last l).CAst.loc

let all_concl_occs_clause = { onhyps=Some[]; concl_occs=AllOccurrences }

let merge_occurrences loc cl = function
  | None ->
      if Locusops.clause_with_generic_occurrences cl then (None, cl)
      else
        user_err ~loc (str "Found an \"at\" clause without \"with\" clause.")
  | Some (occs, p) ->
    let ans = match occs with
    | AllOccurrences -> cl
    | _ ->
      begin match cl with
      | { onhyps = Some []; concl_occs = AllOccurrences } ->
        { onhyps = Some []; concl_occs = occs }
      | { onhyps = Some [(AllOccurrences, id), l]; concl_occs = NoOccurrences } ->
        { cl with onhyps = Some [(occs, id), l] }
      | _ ->
        if Locusops.clause_with_generic_occurrences cl then
          user_err ~loc  (str "Unable to interpret the \"at\" clause; move it in the \"in\" clause.")
        else
          user_err ~loc  (str "Cannot use clause \"at\" twice.")
      end
    in
    (Some p, ans)

let deprecated_conversion_at_with =
  CWarnings.create
    ~name:"conversion_at_with" ~category:"deprecated"
    (fun () -> Pp.str "The syntax [at ... with ...] is deprecated. Use [with ... at ...] instead.")

(* Auxiliary grammar rules *)

open Pvernac.Vernac_



let _ = let id_or_meta = Pcoq.Entry.make "id_or_meta"
        and constr_with_bindings_arg =
          Pcoq.Entry.make "constr_with_bindings_arg"
        and conversion = Pcoq.Entry.make "conversion"
        and occs_nums = Pcoq.Entry.make "occs_nums"
        and occs = Pcoq.Entry.make "occs"
        and pattern_occ = Pcoq.Entry.make "pattern_occ"
        and ref_or_pattern_occ = Pcoq.Entry.make "ref_or_pattern_occ"
        and unfold_occ = Pcoq.Entry.make "unfold_occ"
        and intropatterns = Pcoq.Entry.make "intropatterns"
        and ne_intropatterns = Pcoq.Entry.make "ne_intropatterns"
        and or_and_intropattern = Pcoq.Entry.make "or_and_intropattern"
        and equality_intropattern = Pcoq.Entry.make "equality_intropattern"
        and naming_intropattern = Pcoq.Entry.make "naming_intropattern"
        and intropattern = Pcoq.Entry.make "intropattern"
        and simple_intropattern_closed =
          Pcoq.Entry.make "simple_intropattern_closed"
        and simple_binding = Pcoq.Entry.make "simple_binding"
        and with_bindings = Pcoq.Entry.make "with_bindings"
        and red_flag = Pcoq.Entry.make "red_flag"
        and delta_flag = Pcoq.Entry.make "delta_flag"
        and strategy_flag = Pcoq.Entry.make "strategy_flag"
        and hypident_occ = Pcoq.Entry.make "hypident_occ"
        and clause_dft_all = Pcoq.Entry.make "clause_dft_all"
        and opt_clause = Pcoq.Entry.make "opt_clause"
        and concl_occ = Pcoq.Entry.make "concl_occ"
        and in_hyp_list = Pcoq.Entry.make "in_hyp_list"
        and in_hyp_as = Pcoq.Entry.make "in_hyp_as"
        and orient_rw = Pcoq.Entry.make "orient_rw"
        and simple_binder = Pcoq.Entry.make "simple_binder"
        and fixdecl = Pcoq.Entry.make "fixdecl"
        and struct_annot = Pcoq.Entry.make "struct_annot"
        and cofixdecl = Pcoq.Entry.make "cofixdecl"
        and bindings_with_parameters =
          Pcoq.Entry.make "bindings_with_parameters"
        and eliminator = Pcoq.Entry.make "eliminator"
        and as_ipat = Pcoq.Entry.make "as_ipat"
        and or_and_intropattern_loc =
          Pcoq.Entry.make "or_and_intropattern_loc"
        and as_or_and_ipat = Pcoq.Entry.make "as_or_and_ipat"
        and eqn_ipat = Pcoq.Entry.make "eqn_ipat"
        and as_name = Pcoq.Entry.make "as_name"
        and by_tactic = Pcoq.Entry.make "by_tactic"
        and rewriter = Pcoq.Entry.make "rewriter"
        and oriented_rewriter = Pcoq.Entry.make "oriented_rewriter"
        and induction_clause = Pcoq.Entry.make "induction_clause"
        and induction_clause_list = Pcoq.Entry.make "induction_clause_list"
        in
        let () = assert (Pcoq.Entry.is_empty int_or_var) in
        let () =
        Pcoq.grammar_extend int_or_var
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm identref)))
                                  (fun id loc -> 
# 204 "plugins/ltac/g_tactic.mlg"
                           ArgVar id 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm integer)))
                                 (fun n loc -> 
# 203 "plugins/ltac/g_tactic.mlg"
                          ArgArg n 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty nat_or_var) in
        let () =
        Pcoq.grammar_extend nat_or_var
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm identref)))
                                  (fun id loc -> 
# 208 "plugins/ltac/g_tactic.mlg"
                           ArgVar id 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n loc -> 
# 207 "plugins/ltac/g_tactic.mlg"
                          ArgArg n 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty id_or_meta) in
        let () =
        Pcoq.grammar_extend id_or_meta
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm identref)))
                                  (fun id loc -> 
# 212 "plugins/ltac/g_tactic.mlg"
                           id 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty open_constr) in
        let () =
        Pcoq.grammar_extend open_constr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr)))
                                  (fun c loc -> 
# 215 "plugins/ltac/g_tactic.mlg"
                        c 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty uconstr) in
        let () =
        Pcoq.grammar_extend uconstr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr)))
                                  (fun c loc -> 
# 218 "plugins/ltac/g_tactic.mlg"
                        c 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty destruction_arg) in
        let () =
        Pcoq.grammar_extend destruction_arg
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr_with_bindings_arg)))
                                  (fun c loc -> 
# 224 "plugins/ltac/g_tactic.mlg"
                                          on_snd destruction_arg_of_constr c 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_rpar)))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings)))
                                 (fun c _ loc -> 
# 223 "plugins/ltac/g_tactic.mlg"
          (Some false,destruction_arg_of_constr c) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm natural)))
                                 (fun n loc -> 
# 221 "plugins/ltac/g_tactic.mlg"
                         (None,ElimOnAnonHyp n) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty constr_with_bindings_arg)
        in
        let () =
        Pcoq.grammar_extend constr_with_bindings_arg
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr_with_bindings)))
                                  (fun c loc -> 
# 229 "plugins/ltac/g_tactic.mlg"
                                      (None,c) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (">")))))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings)))
                                 (fun c _ loc -> 
# 228 "plugins/ltac/g_tactic.mlg"
                                           (Some true,c) 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty quantified_hypothesis)
        in
        let () =
        Pcoq.grammar_extend quantified_hypothesis
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm natural)))
                                  (fun n loc -> 
# 233 "plugins/ltac/g_tactic.mlg"
                         AnonHyp n 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm ident)))
                                 (fun id loc -> 
# 232 "plugins/ltac/g_tactic.mlg"
                        NamedHyp (CAst.make ~loc id) 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty conversion) in
        let () =
        Pcoq.grammar_extend conversion
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm constr)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                                  ((Pcoq.Symbol.nterm occs_nums)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                  ((Pcoq.Symbol.nterm constr)))
                                  (fun c2 _ occs _ c1 loc -> 
# 239 "plugins/ltac/g_tactic.mlg"
            deprecated_conversion_at_with ();  (* 8.14 *)
          (Some (occs,c1), c2) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                 ((Pcoq.Symbol.nterm constr)))
                                 (fun c2 _ c1 loc -> 
# 237 "plugins/ltac/g_tactic.mlg"
                                              (Some (AllOccurrences,c1),c2) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm constr)))
                                 (fun c loc -> 
# 236 "plugins/ltac/g_tactic.mlg"
                        (None, c) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty occs_nums) in
        let () =
        Pcoq.grammar_extend occs_nums
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm nat_or_var)))))
                                  (fun nl _ loc -> 
# 244 "plugins/ltac/g_tactic.mlg"
                                        AllOccurrencesBut nl 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm nat_or_var)))))
                                 (fun nl loc -> 
# 243 "plugins/ltac/g_tactic.mlg"
                                   OnlyOccurrences nl 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty occs) in
        let () =
        Pcoq.grammar_extend occs
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 247 "plugins/ltac/g_tactic.mlg"
                                                  AllOccurrences 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                 ((Pcoq.Symbol.nterm occs_nums)))
                                 (fun occs _ loc -> 
# 247 "plugins/ltac/g_tactic.mlg"
                                    occs 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty pattern_occ) in
        let () =
        Pcoq.grammar_extend pattern_occ
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm constr)))
                                                  ((Pcoq.Symbol.nterm occs)))
                                  (fun nl c loc -> 
# 250 "plugins/ltac/g_tactic.mlg"
                                   (nl,c) 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty ref_or_pattern_occ)
        in
        let () =
        Pcoq.grammar_extend ref_or_pattern_occ
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm constr)))
                                                  ((Pcoq.Symbol.nterm occs)))
                                  (fun nl c loc -> 
# 256 "plugins/ltac/g_tactic.mlg"
                                   nl,Inr c 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm smart_global)))
                                                 ((Pcoq.Symbol.nterm occs)))
                                 (fun nl c loc -> 
# 255 "plugins/ltac/g_tactic.mlg"
                                         nl,Inl c 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty unfold_occ) in
        let () =
        Pcoq.grammar_extend unfold_occ
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm smart_global)))
                                                  ((Pcoq.Symbol.nterm occs)))
                                  (fun nl c loc -> 
# 259 "plugins/ltac/g_tactic.mlg"
                                         (nl,c) 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty intropatterns) in
        let () =
        Pcoq.grammar_extend intropatterns
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm intropattern))))
                                  (fun l loc -> 
# 262 "plugins/ltac/g_tactic.mlg"
                                    l 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty ne_intropatterns) in
        let () =
        Pcoq.grammar_extend ne_intropatterns
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm intropattern)))))
                                  (fun l loc -> 
# 265 "plugins/ltac/g_tactic.mlg"
                                    l 
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
# 277 "plugins/ltac/g_tactic.mlg"
            let rec pairify = function
            | ([]|[_]|[_;_]) as l -> l
            | t::q -> [t; CAst.make ?loc:(loc_of_ne_list q) (IntroAction (IntroOrAndPattern (IntroAndPattern (pairify q))))]
          in IntroAndPattern (pairify (si::tc)) 
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
# 273 "plugins/ltac/g_tactic.mlg"
               IntroAndPattern (si::tc) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm simple_intropattern)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ si _ loc -> 
# 270 "plugins/ltac/g_tactic.mlg"
                                                IntroAndPattern [si] 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("()")))))
                                 (fun _ loc -> 
# 269 "plugins/ltac/g_tactic.mlg"
                  IntroAndPattern [] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm intropatterns)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD ("|"))])) false)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ tc _ loc -> 
# 268 "plugins/ltac/g_tactic.mlg"
                                                        IntroOrPattern tc 
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
# 285 "plugins/ltac/g_tactic.mlg"
                                           IntroInjection tc 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("<-")))))
                                 (fun _ loc -> 
# 284 "plugins/ltac/g_tactic.mlg"
                  IntroRewrite false 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("->")))))
                                 (fun _ loc -> 
# 283 "plugins/ltac/g_tactic.mlg"
                  IntroRewrite true 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty naming_intropattern)
        in
        let () =
        Pcoq.grammar_extend naming_intropattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ident)))
                                  (fun id loc -> 
# 290 "plugins/ltac/g_tactic.mlg"
                        IntroIdentifier id 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                 (fun _ loc -> 
# 289 "plugins/ltac/g_tactic.mlg"
                 IntroAnonymous 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm pattern_ident)))
                                 (fun prefix loc -> 
# 288 "plugins/ltac/g_tactic.mlg"
                                    IntroFresh prefix.CAst.v 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty intropattern) in
        let () =
        Pcoq.grammar_extend intropattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("**")))))
                                  (fun _ loc -> 
# 295 "plugins/ltac/g_tactic.mlg"
                  CAst.make ~loc @@ IntroForthcoming false 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                 (fun _ loc -> 
# 294 "plugins/ltac/g_tactic.mlg"
                  CAst.make ~loc @@ IntroForthcoming true 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm simple_intropattern)))
                                 (fun l loc -> 
# 293 "plugins/ltac/g_tactic.mlg"
                                     l 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty simple_intropattern)
        in
        let () =
        Pcoq.grammar_extend simple_intropattern
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm simple_intropattern_closed)))
                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD ("%")))))
                                                                   ((Pcoq.Symbol.nterml term ("0"))))
                                                                   (fun c _
                                                                   loc -> 
                                                                   
# 299 "plugins/ltac/g_tactic.mlg"
                                                c 
                                                                   )]))))
                                  (fun l pat loc -> 
# 300 "plugins/ltac/g_tactic.mlg"
            let {CAst.loc=loc0;v=pat} = pat in
          let f c pat =
            let loc1 = Constrexpr_ops.constr_loc c in
            let loc = Loc.merge_opt loc0 loc1 in
            IntroAction (IntroApplyOn (CAst.(make ?loc:loc1 c),CAst.(make ?loc pat))) in
          CAst.make ~loc @@ List.fold_right f l pat 
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
# 311 "plugins/ltac/g_tactic.mlg"
                                       CAst.make ~loc @@ IntroNaming pat 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("_")))))
                                 (fun _ loc -> 
# 310 "plugins/ltac/g_tactic.mlg"
                 CAst.make ~loc @@ IntroAction IntroWildcard 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm equality_intropattern)))
                                 (fun pat loc -> 
# 309 "plugins/ltac/g_tactic.mlg"
                                         CAst.make ~loc @@ IntroAction pat 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm or_and_intropattern)))
                                 (fun pat loc -> 
# 308 "plugins/ltac/g_tactic.mlg"
                                         CAst.make ~loc @@ IntroAction (IntroOrAndPattern pat) 
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
                                                                  ((Pcoq.Symbol.nterm natural)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ c _ n _ loc -> 
# 315 "plugins/ltac/g_tactic.mlg"
                                                      CAst.make ~loc (AnonHyp n, c) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ id _ loc -> 
# 314 "plugins/ltac/g_tactic.mlg"
                                                        CAst.make ~loc (NamedHyp id, c) 
                                                        )])]))
        in let () = assert (Pcoq.Entry.is_empty bindings) in
        let () =
        Pcoq.grammar_extend bindings
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm constr)))))
                                  (fun bl loc -> 
# 320 "plugins/ltac/g_tactic.mlg"
                               ImplicitBindings bl 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_lpar_idnum_coloneq)))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm simple_binding)))))
                                 (fun bl _ loc -> 
# 319 "plugins/ltac/g_tactic.mlg"
            ExplicitBindings bl 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty constr_with_bindings)
        in
        let () =
        Pcoq.grammar_extend constr_with_bindings
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm constr)))
                                                  ((Pcoq.Symbol.nterm with_bindings)))
                                  (fun l c loc -> 
# 323 "plugins/ltac/g_tactic.mlg"
                                           (c, l) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty with_bindings) in
        let () =
        Pcoq.grammar_extend with_bindings
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 326 "plugins/ltac/g_tactic.mlg"
                                               NoBindings 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                 ((Pcoq.Symbol.nterm bindings)))
                                 (fun bl _ loc -> 
# 326 "plugins/ltac/g_tactic.mlg"
                                   bl 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty red_flag) in
        let () =
        Pcoq.grammar_extend red_flag
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("delta"))))))
                                                  ((Pcoq.Symbol.nterm delta_flag)))
                                  (fun d _ loc -> 
# 335 "plugins/ltac/g_tactic.mlg"
                                           [d] 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("zeta"))))))
                                 (fun _ loc -> 
# 334 "plugins/ltac/g_tactic.mlg"
                          [FZeta] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("cofix"))))))
                                 (fun _ loc -> 
# 333 "plugins/ltac/g_tactic.mlg"
                           [FCofix] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("fix"))))))
                                 (fun _ loc -> 
# 332 "plugins/ltac/g_tactic.mlg"
                         [FFix] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("match"))))))
                                 (fun _ loc -> 
# 331 "plugins/ltac/g_tactic.mlg"
                           [FMatch] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("iota"))))))
                                 (fun _ loc -> 
# 330 "plugins/ltac/g_tactic.mlg"
                          [FMatch;FFix;FCofix] 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("beta"))))))
                                 (fun _ loc -> 
# 329 "plugins/ltac/g_tactic.mlg"
                          [FBeta] 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty delta_flag) in
        let () =
        Pcoq.grammar_extend delta_flag
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 341 "plugins/ltac/g_tactic.mlg"
             FDeltaBut [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm smart_global)))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ idl _ loc -> 
# 340 "plugins/ltac/g_tactic.mlg"
                                                FConst idl 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("[")))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm smart_global)))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("]")))))
                                 (fun _ idl _ _ loc -> 
# 339 "plugins/ltac/g_tactic.mlg"
                                                     FDeltaBut idl 
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
# 346 "plugins/ltac/g_tactic.mlg"
                            all_with d 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm red_flag)))))
                                 (fun s loc -> 
# 345 "plugins/ltac/g_tactic.mlg"
                                Redops.make_red_flag (List.flatten s) 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty red_expr) in
        let () =
        Pcoq.grammar_extend red_expr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                  (fun s loc -> 
# 362 "plugins/ltac/g_tactic.mlg"
                       ExtraRedExpr s 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("pattern"))))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm pattern_occ)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                 (fun pl _ loc -> 
# 361 "plugins/ltac/g_tactic.mlg"
                                                            Pattern pl 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("fold"))))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm constr)))))
                                 (fun cl _ loc -> 
# 360 "plugins/ltac/g_tactic.mlg"
                                             Fold cl 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("unfold"))))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm unfold_occ)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                 (fun ul _ loc -> 
# 359 "plugins/ltac/g_tactic.mlg"
                                                           Unfold ul 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("native_compute"))))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ref_or_pattern_occ))))
                                 (fun po _ loc -> 
# 358 "plugins/ltac/g_tactic.mlg"
                                                                 CbvNative po 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("vm_compute"))))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ref_or_pattern_occ))))
                                 (fun po _ loc -> 
# 357 "plugins/ltac/g_tactic.mlg"
                                                             CbvVm po 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("compute"))))))
                                                 ((Pcoq.Symbol.nterm delta_flag)))
                                 (fun delta _ loc -> 
# 356 "plugins/ltac/g_tactic.mlg"
                                                 Cbv (all_with delta) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("lazy"))))))
                                                 ((Pcoq.Symbol.nterm strategy_flag)))
                                 (fun s _ loc -> 
# 355 "plugins/ltac/g_tactic.mlg"
                                             Lazy s 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("cbn"))))))
                                                 ((Pcoq.Symbol.nterm strategy_flag)))
                                 (fun s _ loc -> 
# 354 "plugins/ltac/g_tactic.mlg"
                                            Cbn s 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("cbv"))))))
                                                 ((Pcoq.Symbol.nterm strategy_flag)))
                                 (fun s _ loc -> 
# 353 "plugins/ltac/g_tactic.mlg"
                                            Cbv s 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("simpl"))))))
                                                                 ((Pcoq.Symbol.nterm delta_flag)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ref_or_pattern_occ))))
                                 (fun po d _ loc -> 
# 352 "plugins/ltac/g_tactic.mlg"
                                                                        Simpl (all_with d,po) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("hnf"))))))
                                 (fun _ loc -> 
# 351 "plugins/ltac/g_tactic.mlg"
                         Hnf 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("red"))))))
                                 (fun _ loc -> 
# 350 "plugins/ltac/g_tactic.mlg"
                         Red false 
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
                                                                  ((Pcoq.Symbol.nterm id_or_meta)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ id _ _ _ loc -> 
# 372 "plugins/ltac/g_tactic.mlg"
          let id : lident = id in
        id,InHypValueOnly 
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
                                                                 ((Pcoq.Symbol.nterm id_or_meta)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ id _ _ _ loc -> 
# 369 "plugins/ltac/g_tactic.mlg"
          let id : lident = id in
        id,InHypTypeOnly 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm id_or_meta)))
                                 (fun id loc -> 
# 366 "plugins/ltac/g_tactic.mlg"
          let id : lident = id in
        id,InHyp 
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
# 378 "plugins/ltac/g_tactic.mlg"
          let (id,l) = h in
        let id : lident = id in
        ((occs,id),l) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty in_clause) in
        let () =
        Pcoq.grammar_extend in_clause
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm hypident_occ)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                  (fun hl loc -> 
# 392 "plugins/ltac/g_tactic.mlg"
            {onhyps=Some hl; concl_occs=NoOccurrences} 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm hypident_occ)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                 ((Pcoq.Symbol.nterm concl_occ)))
                                 (fun occs _ hl loc -> 
# 390 "plugins/ltac/g_tactic.mlg"
            {onhyps=Some hl; concl_occs=occs} 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                 ((Pcoq.Symbol.nterm concl_occ)))
                                 (fun occs _ loc -> 
# 388 "plugins/ltac/g_tactic.mlg"
            {onhyps=Some []; concl_occs=occs} 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("|-")))))
                                                 ((Pcoq.Symbol.nterm concl_occ)))
                                 (fun occs _ _ loc -> 
# 386 "plugins/ltac/g_tactic.mlg"
            {onhyps=None; concl_occs=occs} 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                                 ((Pcoq.Symbol.nterm occs)))
                                 (fun occs _ loc -> 
# 384 "plugins/ltac/g_tactic.mlg"
            {onhyps=None; concl_occs=occs} 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty clause_dft_concl) in
        let () =
        Pcoq.grammar_extend clause_dft_concl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 397 "plugins/ltac/g_tactic.mlg"
             all_concl_occs_clause 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm occs)))
                                 (fun occs loc -> 
# 396 "plugins/ltac/g_tactic.mlg"
                       {onhyps=Some[]; concl_occs=occs} 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterm in_clause)))
                                 (fun cl _ loc -> 
# 395 "plugins/ltac/g_tactic.mlg"
                                  cl 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty clause_dft_all) in
        let () =
        Pcoq.grammar_extend clause_dft_all
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 401 "plugins/ltac/g_tactic.mlg"
             {onhyps=None; concl_occs=AllOccurrences} 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterm in_clause)))
                                 (fun cl _ loc -> 
# 400 "plugins/ltac/g_tactic.mlg"
                                  cl 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty opt_clause) in
        let () =
        Pcoq.grammar_extend opt_clause
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 406 "plugins/ltac/g_tactic.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("at")))))
                                                 ((Pcoq.Symbol.nterm occs_nums)))
                                 (fun occs _ loc -> 
# 405 "plugins/ltac/g_tactic.mlg"
                                    Some {onhyps=Some[]; concl_occs=occs} 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.nterm in_clause)))
                                 (fun cl _ loc -> 
# 404 "plugins/ltac/g_tactic.mlg"
                                  Some cl 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty concl_occ) in
        let () =
        Pcoq.grammar_extend concl_occ
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 410 "plugins/ltac/g_tactic.mlg"
             NoOccurrences 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("*")))))
                                                 ((Pcoq.Symbol.nterm occs)))
                                 (fun occs _ loc -> 
# 409 "plugins/ltac/g_tactic.mlg"
                              occs 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty in_hyp_list) in
        let () =
        Pcoq.grammar_extend in_hyp_list
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 414 "plugins/ltac/g_tactic.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm id_or_meta)))))
                                 (fun idl _ loc -> 
# 413 "plugins/ltac/g_tactic.mlg"
                                          idl 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty in_hyp_as) in
        let () =
        Pcoq.grammar_extend in_hyp_as
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 418 "plugins/ltac/g_tactic.mlg"
             [] 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("in")))))
                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm id_or_meta)))
                                                                  ((Pcoq.Symbol.nterm as_ipat)))
                                                                  (fun ipat
                                                                  id loc -> 
                                                                  
# 417 "plugins/ltac/g_tactic.mlg"
                                                              (id,ipat) 
                                                                  )])) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                 (fun l _ loc -> 
# 417 "plugins/ltac/g_tactic.mlg"
                                                                                         l 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty orient_rw) in
        let () =
        Pcoq.grammar_extend orient_rw
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 423 "plugins/ltac/g_tactic.mlg"
             true 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("<-")))))
                                 (fun _ loc -> 
# 422 "plugins/ltac/g_tactic.mlg"
                  false 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("->")))))
                                 (fun _ loc -> 
# 421 "plugins/ltac/g_tactic.mlg"
                  true 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty simple_binder) in
        let () =
        Pcoq.grammar_extend simple_binder
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm name)))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ c _ nal _ loc -> 
# 428 "plugins/ltac/g_tactic.mlg"
                                                      (nal,Default Glob_term.Explicit,c) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm name)))
                                 (fun na loc -> 
# 426 "plugins/ltac/g_tactic.mlg"
                     ([na],Default Glob_term.Explicit, CAst.make ~loc @@
                    CHole (Some (Evar_kinds.BinderType na.CAst.v), IntroAnonymous, None)) 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty fixdecl) in
        let () =
        Pcoq.grammar_extend fixdecl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm ident)))
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm simple_binder))))
                                                                  ((Pcoq.Symbol.nterm struct_annot)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ ty _ ann bl id _ loc -> 
# 433 "plugins/ltac/g_tactic.mlg"
                                  (loc, id, bl, ann, ty) 
                                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty struct_annot) in
        let () =
        Pcoq.grammar_extend struct_annot
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 437 "plugins/ltac/g_tactic.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("{")))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("struct"))))))
                                                                 ((Pcoq.Symbol.nterm name)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                 (fun _ id _ _ loc -> 
# 436 "plugins/ltac/g_tactic.mlg"
                                               Some id 
                                                      )])]))
        in let () = assert (Pcoq.Entry.is_empty cofixdecl) in
        let () =
        Pcoq.grammar_extend cofixdecl
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm ident)))
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm simple_binder))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ ty _ bl id _ loc -> 
# 441 "plugins/ltac/g_tactic.mlg"
          (loc, id, bl, None, ty) 
                                                             )])]))
        in let () = assert (Pcoq.Entry.is_empty bindings_with_parameters)
        in
        let () =
        Pcoq.grammar_extend bindings_with_parameters
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm check_for_coloneq)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                  ((Pcoq.Symbol.nterm ident)))
                                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm simple_binder))))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                  (fun _ c _ bl id _ _ loc -> 
# 445 "plugins/ltac/g_tactic.mlg"
                                    (id, mkCLambdaN_simple bl c) 
                                                              )])]))
        in let () = assert (Pcoq.Entry.is_empty eliminator) in
        let () =
        Pcoq.grammar_extend eliminator
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("using")))))
                                                  ((Pcoq.Symbol.nterm constr_with_bindings)))
                                  (fun el _ loc -> 
# 448 "plugins/ltac/g_tactic.mlg"
                                                el 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty as_ipat) in
        let () =
        Pcoq.grammar_extend as_ipat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 452 "plugins/ltac/g_tactic.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm simple_intropattern)))
                                 (fun ipat _ loc -> 
# 451 "plugins/ltac/g_tactic.mlg"
                                              Some ipat 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty or_and_intropattern_loc)
        in
        let () =
        Pcoq.grammar_extend or_and_intropattern_loc
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm identref)))
                                  (fun locid loc -> 
# 456 "plugins/ltac/g_tactic.mlg"
                              ArgVar locid 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm or_and_intropattern)))
                                 (fun ipat loc -> 
# 455 "plugins/ltac/g_tactic.mlg"
                                        ArgArg (CAst.make ~loc ipat) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty as_or_and_ipat) in
        let () =
        Pcoq.grammar_extend as_or_and_ipat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 465 "plugins/ltac/g_tactic.mlg"
             None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm equality_intropattern)))
                                 (fun ipat _ loc -> 
# 461 "plugins/ltac/g_tactic.mlg"
          match ipat with
          | IntroRewrite _ -> user_err ~loc Pp.(str "Disjunctive/conjunctive pattern expected.")
          | IntroInjection _ -> user_err ~loc Pp.(strbrk "Found an injection pattern while a disjunctive/conjunctive pattern was expected; use " ++ str "\"injection as pattern\"" ++ strbrk " instead.")
          | _ -> assert false 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm or_and_intropattern_loc)))
                                 (fun ipat _ loc -> 
# 459 "plugins/ltac/g_tactic.mlg"
                                                  Some ipat 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty eqn_ipat) in
        let () =
        Pcoq.grammar_extend eqn_ipat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 469 "plugins/ltac/g_tactic.mlg"
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
# 468 "plugins/ltac/g_tactic.mlg"
                                                         Some (CAst.make ~loc pat) 
                                                     )])]))
        in let () = assert (Pcoq.Entry.is_empty as_name) in
        let () =
        Pcoq.grammar_extend as_name
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 472 "plugins/ltac/g_tactic.mlg"
                                                          Names.Name.Anonymous 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("as")))))
                                                 ((Pcoq.Symbol.nterm ident)))
                                 (fun id _ loc -> 
# 472 "plugins/ltac/g_tactic.mlg"
                              Names.Name.Name id 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty by_tactic) in
        let () =
        Pcoq.grammar_extend by_tactic
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make (Pcoq.Rule.stop)
                                  (fun loc -> 
# 476 "plugins/ltac/g_tactic.mlg"
           None 
                                              );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("by")))))
                                                 ((Pcoq.Symbol.nterml ltac_expr ("3"))))
                                 (fun tac _ loc -> 
# 475 "plugins/ltac/g_tactic.mlg"
                                             Some tac 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty rewriter) in
        let () =
        Pcoq.grammar_extend rewriter
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr_with_bindings_arg)))
                                  (fun c loc -> 
# 484 "plugins/ltac/g_tactic.mlg"
                                          (Equality.Precisely 1, c) 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings_arg)))
                                 (fun c n loc -> 
# 483 "plugins/ltac/g_tactic.mlg"
                                                       (Equality.Precisely n,c) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PLEFTQMARK))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 482 "plugins/ltac/g_tactic.mlg"
                                                     () 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 482 "plugins/ltac/g_tactic.mlg"
                               () 
                                                                 )])))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings_arg)))
                                 (fun c _ n loc -> 
# 482 "plugins/ltac/g_tactic.mlg"
                                                                                               (Equality.UpTo n,c) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings_arg)))
                                 (fun c _ n loc -> 
# 481 "plugins/ltac/g_tactic.mlg"
                                                            (Equality.Precisely n,c) 
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
                                                                 
# 480 "plugins/ltac/g_tactic.mlg"
                                        () 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("?")))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 480 "plugins/ltac/g_tactic.mlg"
                  () 
                                                                 )])))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings_arg)))
                                 (fun c _ loc -> 
# 480 "plugins/ltac/g_tactic.mlg"
                                                                                  (Equality.RepeatStar,c) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                 ((Pcoq.Symbol.nterm constr_with_bindings_arg)))
                                 (fun c _ loc -> 
# 479 "plugins/ltac/g_tactic.mlg"
                                               (Equality.RepeatPlus,c) 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty oriented_rewriter) in
        let () =
        Pcoq.grammar_extend oriented_rewriter
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm orient_rw)))
                                                  ((Pcoq.Symbol.nterm rewriter)))
                                  (fun p b loc -> 
# 488 "plugins/ltac/g_tactic.mlg"
                                         let (m,c) = p in (b,m,c) 
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
                                                  ((Pcoq.Symbol.nterm opt_clause)))
                                  (fun cl eq pat c loc -> 
# 492 "plugins/ltac/g_tactic.mlg"
                             (c,(eq,pat),cl) 
                                                          )])]))
        in let () = assert (Pcoq.Entry.is_empty induction_clause_list)
        in
        let () =
        Pcoq.grammar_extend induction_clause_list
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm induction_clause)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm eliminator))))
                                                  ((Pcoq.Symbol.nterm opt_clause)))
                                  (fun cl_tolerance el ic loc -> 
# 498 "plugins/ltac/g_tactic.mlg"
          match ic,el,cl_tolerance with
        | [c,pat,None],Some _,Some _ -> ([c,pat,cl_tolerance],el)
        | _,_,Some _ -> err ()
        | _,_,None -> (ic,el) 
                                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty simple_tactic) in
        let () =
        Pcoq.grammar_extend simple_tactic
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("change_no_check"))))))
                                                                  ((Pcoq.Symbol.nterm conversion)))
                                                  ((Pcoq.Symbol.nterm clause_dft_concl)))
                                  (fun cl c _ loc -> 
# 692 "plugins/ltac/g_tactic.mlg"
            let (oc, c) = c in
          let p,cl = merge_occurrences loc cl oc in
          CAst.make ~loc @@ TacAtom (TacChange (false,p,c,cl)) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("change"))))))
                                                                 ((Pcoq.Symbol.nterm conversion)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl c _ loc -> 
# 688 "plugins/ltac/g_tactic.mlg"
            let (oc, c) = c in
          let p,cl = merge_occurrences loc cl oc in
          CAst.make ~loc @@ TacAtom (TacChange (true,p,c,cl)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("pattern"))))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm pattern_occ)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl pl _ loc -> 
# 684 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Pattern pl, cl)) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("fold"))))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm constr)))))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl l _ loc -> 
# 682 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Fold l, cl)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("unfold"))))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm unfold_occ)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl ul _ loc -> 
# 680 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Unfold ul, cl)) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("native_compute"))))))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ref_or_pattern_occ))))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl po _ loc -> 
# 678 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (CbvNative po, cl)) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("vm_compute"))))))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ref_or_pattern_occ))))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl po _ loc -> 
# 676 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (CbvVm po, cl)) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("compute"))))))
                                                                 ((Pcoq.Symbol.nterm delta_flag)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl delta _ loc -> 
# 674 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Cbv (all_with delta), cl)) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("lazy"))))))
                                                                 ((Pcoq.Symbol.nterm strategy_flag)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl s _ loc -> 
# 672 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Lazy s, cl)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("cbn"))))))
                                                                 ((Pcoq.Symbol.nterm strategy_flag)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl s _ loc -> 
# 670 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Cbn s, cl)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("cbv"))))))
                                                                 ((Pcoq.Symbol.nterm strategy_flag)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl s _ loc -> 
# 668 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Cbv s, cl)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("simpl"))))))
                                                                 ((Pcoq.Symbol.nterm delta_flag)))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm ref_or_pattern_occ))))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl po d _ loc -> 
# 666 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Simpl (all_with d, po), cl)) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("hnf"))))))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl _ loc -> 
# 664 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Hnf, cl)) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("red"))))))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun cl _ loc -> 
# 662 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacReduce (Red false, cl)) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inversion"))))))
                                                                 ((Pcoq.Symbol.nterm quantified_hypothesis)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("using")))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                 ((Pcoq.Symbol.nterm in_hyp_list)))
                                 (fun cl c _ hyp _ loc -> 
# 658 "plugins/ltac/g_tactic.mlg"
              CAst.make ~loc @@ TacAtom (TacInversion (InversionUsing (c,cl), hyp)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inversion_clear"))))))
                                                                 ((Pcoq.Symbol.nterm quantified_hypothesis)))
                                                                 ((Pcoq.Symbol.nterm as_or_and_ipat)))
                                                 ((Pcoq.Symbol.nterm in_hyp_list)))
                                 (fun cl ids hyp _ loc -> 
# 655 "plugins/ltac/g_tactic.mlg"
              CAst.make ~loc @@ TacAtom (TacInversion (NonDepInversion (FullInversionClear, cl, ids), hyp)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inversion"))))))
                                                                 ((Pcoq.Symbol.nterm quantified_hypothesis)))
                                                                 ((Pcoq.Symbol.nterm as_or_and_ipat)))
                                                 ((Pcoq.Symbol.nterm in_hyp_list)))
                                 (fun cl ids hyp _ loc -> 
# 651 "plugins/ltac/g_tactic.mlg"
              CAst.make ~loc @@ TacAtom (TacInversion (NonDepInversion (FullInversion, cl, ids), hyp)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("simple"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inversion"))))))
                                                                 ((Pcoq.Symbol.nterm quantified_hypothesis)))
                                                                 ((Pcoq.Symbol.nterm as_or_and_ipat)))
                                                 ((Pcoq.Symbol.nterm in_hyp_list)))
                                 (fun cl ids hyp _ _ loc -> 
# 647 "plugins/ltac/g_tactic.mlg"
              CAst.make ~loc @@ TacAtom (TacInversion (NonDepInversion (SimpleInversion, cl, ids), hyp)) 
                                                            );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("dependent"))))))
                                                                 ((Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inversion_clear"))))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 640 "plugins/ltac/g_tactic.mlg"
                                         FullInversionClear 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inversion"))))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 639 "plugins/ltac/g_tactic.mlg"
                                   FullInversion 
                                                                 );
                                                                 Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("simple"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("inversion"))))))
                                                                 (fun _ _
                                                                 loc -> 
                                                                 
# 638 "plugins/ltac/g_tactic.mlg"
                                                   SimpleInversion 
                                                                 )])))
                                                                 ((Pcoq.Symbol.nterm quantified_hypothesis)))
                                                                 ((Pcoq.Symbol.nterm as_or_and_ipat)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                                  ((Pcoq.Symbol.nterm constr)))
                                                                  (fun c _
                                                                  loc -> 
                                                                  
# 642 "plugins/ltac/g_tactic.mlg"
                                                                  c 
                                                                  )]))))
                                 (fun co ids hyp k _ loc -> 
# 643 "plugins/ltac/g_tactic.mlg"
              CAst.make ~loc @@ TacAtom (TacInversion (DepInversion (k,co,ids),hyp)) 
                                                            );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("erewrite"))))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm oriented_rewriter)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun t cl l _ loc -> 
# 636 "plugins/ltac/g_tactic.mlg"
                                                  CAst.make ~loc @@ TacAtom (TacRewrite (true,l,cl,t)) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("rewrite"))))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm oriented_rewriter)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun t cl l _ loc -> 
# 634 "plugins/ltac/g_tactic.mlg"
                                                  CAst.make ~loc @@ TacAtom (TacRewrite (false,l,cl,t)) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("edestruct"))))))
                                                 ((Pcoq.Symbol.nterm induction_clause_list)))
                                 (fun icl _ loc -> 
# 630 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacInductionDestruct(false,true,icl)) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("destruct"))))))
                                                 ((Pcoq.Symbol.nterm induction_clause_list)))
                                 (fun icl _ loc -> 
# 628 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacInductionDestruct(false,false,icl)) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("einduction"))))))
                                                 ((Pcoq.Symbol.nterm induction_clause_list)))
                                 (fun ic _ loc -> 
# 626 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacInductionDestruct(true,true,ic)) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("induction"))))))
                                                 ((Pcoq.Symbol.nterm induction_clause_list)))
                                 (fun ic _ loc -> 
# 624 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacInductionDestruct (true,false,ic)) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("generalize"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm lookup_at_as_comma)))
                                                                 ((Pcoq.Symbol.nterm occs)))
                                                                 ((Pcoq.Symbol.nterm as_name)))
                                                 ((Pcoq.Symbol.list0 (Pcoq.Symbol.rules 
                                                 [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (",")))))
                                                                  ((Pcoq.Symbol.nterm pattern_occ)))
                                                                  ((Pcoq.Symbol.nterm as_name)))
                                                                  (fun na c _
                                                                  loc -> 
                                                                  
# 619 "plugins/ltac/g_tactic.mlg"
                                                             (c,na) 
                                                                  )]))))
                                 (fun l na nl _ c _ loc -> 
# 620 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacGeneralize (((nl,c),na)::l)) 
                                                           );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("generalize"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm constr)))))
                                 (fun l c _ loc -> 
# 615 "plugins/ltac/g_tactic.mlg"
            let gen_everywhere c = ((AllOccurrences,c),Names.Name.Anonymous) in
          CAst.make ~loc @@ TacAtom (TacGeneralize (List.map gen_everywhere (c::l))) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("generalize"))))))
                                                 ((Pcoq.Symbol.nterm constr)))
                                 (fun c _ loc -> 
# 613 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacGeneralize [((AllOccurrences,c),Names.Name.Anonymous)]) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eenough"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm as_ipat)))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun tac ipat c _ loc -> 
# 610 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacAssert (true,false,Some tac,ipat,c)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("enough"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm as_ipat)))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun tac ipat c _ loc -> 
# 608 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacAssert (false,false,Some tac,ipat,c)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("epose"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("proof"))))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.nterm as_ipat)))
                                 (fun ipat c _ _ loc -> 
# 606 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacAssert (true,true,None,ipat,c)) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("pose"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("proof"))))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.nterm as_ipat)))
                                 (fun ipat c _ _ loc -> 
# 604 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacAssert (false,true,None,ipat,c)) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("epose"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("proof"))))))
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_coloneq)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ lid _ _ _ _ loc -> 
# 601 "plugins/ltac/g_tactic.mlg"
            let { CAst.loc = loc; v = id } = lid in
          CAst.make ?loc @@ TacAtom ( TacAssert (true,true,None,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) 
                                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("pose"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("proof"))))))
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_coloneq)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ lid _ _ _ _ loc -> 
# 597 "plugins/ltac/g_tactic.mlg"
            let { CAst.loc = loc; v = id } = lid in
          CAst.make ?loc @@ TacAtom (TacAssert (false,true,None,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) 
                                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eassert"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm as_ipat)))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun tac ipat c _ loc -> 
# 592 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacAssert (true,true,Some tac,ipat,c)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("assert"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm as_ipat)))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun tac ipat c _ loc -> 
# 590 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacAssert (false,true,Some tac,ipat,c)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eenough"))))))
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_colon)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun tac _ c _ lid _ _ _ loc -> 
# 586 "plugins/ltac/g_tactic.mlg"
            let { CAst.loc = loc; v = id } = lid in
          CAst.make ?loc @@ TacAtom ( TacAssert (true,false,Some tac,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) 
                                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("enough"))))))
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_colon)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun tac _ c _ lid _ _ _ loc -> 
# 582 "plugins/ltac/g_tactic.mlg"
            let { CAst.loc = loc; v = id } = lid in
          CAst.make ?loc @@ TacAtom ( TacAssert (false,false,Some tac,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) 
                                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eassert"))))))
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_colon)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun tac _ c _ lid _ _ _ loc -> 
# 576 "plugins/ltac/g_tactic.mlg"
            let { CAst.loc = loc; v = id } = lid in
          CAst.make ?loc @@ TacAtom ( TacAssert (true,true,Some tac,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) 
                                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("assert"))))))
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_colon)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                                 ((Pcoq.Symbol.nterm by_tactic)))
                                 (fun tac _ c _ lid _ _ _ loc -> 
# 572 "plugins/ltac/g_tactic.mlg"
            let { CAst.loc = loc; v = id } = lid in
          CAst.make ?loc @@ TacAtom ( TacAssert (false,true,Some tac,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) 
                                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eassert"))))))
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_coloneq)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ lid _ _ _ loc -> 
# 566 "plugins/ltac/g_tactic.mlg"
            let { CAst.loc = loc; v = id } = lid in
          CAst.make ?loc @@ TacAtom ( TacAssert (true,true,None,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("assert"))))))
                                                                 ((Pcoq.Symbol.nterm test_lpar_id_coloneq)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("(")))))
                                                                 ((Pcoq.Symbol.nterm identref)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                                 ((Pcoq.Symbol.nterm lconstr)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (")")))))
                                 (fun _ c _ lid _ _ _ loc -> 
# 562 "plugins/ltac/g_tactic.mlg"
            let { CAst.loc = loc; v = id } = lid in
          CAst.make ?loc @@ TacAtom ( TacAssert (false,true,None,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eremember"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm as_name)))
                                                                 ((Pcoq.Symbol.nterm eqn_ipat)))
                                                 ((Pcoq.Symbol.nterm clause_dft_all)))
                                 (fun p e na c _ loc -> 
# 557 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacLetTac (true,na,c,p,false,e)) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("remember"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm as_name)))
                                                                 ((Pcoq.Symbol.nterm eqn_ipat)))
                                                 ((Pcoq.Symbol.nterm clause_dft_all)))
                                 (fun p e na c _ loc -> 
# 554 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacLetTac (false,na,c,p,false,e)) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eset"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm as_name)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun p na c _ loc -> 
# 551 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacLetTac (true,na,c,p,true,None)) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eset"))))))
                                                                 ((Pcoq.Symbol.nterm bindings_with_parameters)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun p bl _ loc -> 
# 549 "plugins/ltac/g_tactic.mlg"
            let (id,c) = bl in CAst.make ~loc @@ TacAtom (TacLetTac (true,Names.Name id,c,p,true,None)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("set"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                                 ((Pcoq.Symbol.nterm as_name)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun p na c _ loc -> 
# 547 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacLetTac (false,na,c,p,true,None)) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("set"))))))
                                                                 ((Pcoq.Symbol.nterm bindings_with_parameters)))
                                                 ((Pcoq.Symbol.nterm clause_dft_concl)))
                                 (fun p bl _ loc -> 
# 545 "plugins/ltac/g_tactic.mlg"
            let (id,c) = bl in CAst.make ~loc @@ TacAtom (TacLetTac (false,Names.Name.Name id,c,p,true,None)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("epose"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                 ((Pcoq.Symbol.nterm as_name)))
                                 (fun na b _ loc -> 
# 543 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacLetTac (true,na,b,Locusops.nowhere,true,None)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("epose"))))))
                                                 ((Pcoq.Symbol.nterm bindings_with_parameters)))
                                 (fun bl _ loc -> 
# 541 "plugins/ltac/g_tactic.mlg"
            let (id,b) = bl in CAst.make ~loc @@ TacAtom (TacLetTac (true,Names.Name id,b,Locusops.nowhere,true,None)) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("pose"))))))
                                                                 ((Pcoq.Symbol.nterm constr)))
                                                 ((Pcoq.Symbol.nterm as_name)))
                                 (fun na b _ loc -> 
# 539 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacLetTac (false,na,b,Locusops.nowhere,true,None)) 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("pose"))))))
                                                 ((Pcoq.Symbol.nterm bindings_with_parameters)))
                                 (fun bl _ loc -> 
# 537 "plugins/ltac/g_tactic.mlg"
            let (id,b) = bl in CAst.make ~loc @@ TacAtom (TacLetTac (false,Names.Name.Name id,b,Locusops.nowhere,true,None)) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("cofix")))))
                                                                 ((Pcoq.Symbol.nterm ident)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm cofixdecl)))))
                                 (fun fd _ id _ loc -> 
# 534 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacMutualCofix (id,List.map mk_cofix_tac fd)) 
                                                       );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("fix")))))
                                                                 ((Pcoq.Symbol.nterm ident)))
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("with")))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm fixdecl)))))
                                 (fun fd _ n id _ loc -> 
# 532 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacMutualFix (id,n,List.map mk_fix_tac fd)) 
                                                         );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("ecase"))))))
                                                 ((Pcoq.Symbol.nterm induction_clause_list)))
                                 (fun icl _ loc -> 
# 530 "plugins/ltac/g_tactic.mlg"
                                                        CAst.make ~loc @@ TacAtom (mkTacCase true icl) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("case"))))))
                                                 ((Pcoq.Symbol.nterm induction_clause_list)))
                                 (fun icl _ loc -> 
# 529 "plugins/ltac/g_tactic.mlg"
                                                       CAst.make ~loc @@ TacAtom (mkTacCase false icl) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eelim"))))))
                                                                 ((Pcoq.Symbol.nterm constr_with_bindings_arg)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm eliminator))))
                                 (fun el cl _ loc -> 
# 528 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacElim (true,cl,el)) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("elim"))))))
                                                                 ((Pcoq.Symbol.nterm constr_with_bindings_arg)))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm eliminator))))
                                 (fun el cl _ loc -> 
# 526 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacElim (false,cl,el)) 
                                                     );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("simple"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eapply"))))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm constr_with_bindings_arg)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.nterm in_hyp_as)))
                                 (fun inhyp cl _ _ loc -> 
# 524 "plugins/ltac/g_tactic.mlg"
                                 CAst.make ~loc @@ TacAtom (TacApply (false,true,cl,inhyp)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("simple"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("apply"))))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm constr_with_bindings_arg)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.nterm in_hyp_as)))
                                 (fun inhyp cl _ _ loc -> 
# 521 "plugins/ltac/g_tactic.mlg"
                                 CAst.make ~loc @@ TacAtom (TacApply (false,false,cl,inhyp)) 
                                                          );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eapply"))))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm constr_with_bindings_arg)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.nterm in_hyp_as)))
                                 (fun inhyp cl _ loc -> 
# 518 "plugins/ltac/g_tactic.mlg"
                                 CAst.make ~loc @@ TacAtom (TacApply (true,true,cl,inhyp)) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("apply"))))))
                                                                 ((Pcoq.Symbol.list1sep ((Pcoq.Symbol.nterm constr_with_bindings_arg)) ((Pcoq.Symbol.tokens [Pcoq.TPattern (Tok.PKEYWORD (","))])) false)))
                                                 ((Pcoq.Symbol.nterm in_hyp_as)))
                                 (fun inhyp cl _ loc -> 
# 516 "plugins/ltac/g_tactic.mlg"
                                 CAst.make ~loc @@ TacAtom (TacApply (true,false,cl,inhyp)) 
                                                        );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("eintros"))))))
                                 (fun _ loc -> 
# 513 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacIntroPattern (true,[CAst.make ~loc @@IntroForthcoming false])) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("eintros"))))))
                                                 ((Pcoq.Symbol.nterm ne_intropatterns)))
                                 (fun pl _ loc -> 
# 511 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacIntroPattern (true,pl)) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("intros"))))))
                                 (fun _ loc -> 
# 509 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacIntroPattern (false,[CAst.make ~loc @@IntroForthcoming false])) 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("intros"))))))
                                                 ((Pcoq.Symbol.nterm ne_intropatterns)))
                                 (fun pl _ loc -> 
# 507 "plugins/ltac/g_tactic.mlg"
            CAst.make ~loc @@ TacAtom (TacIntroPattern (false,pl)) 
                                                  )])]))
        in ()

