
# 11 "parsing/g_prim.mlg"
 

open Names
open Libnames

open Pcoq.Prim

let local_make_qualid loc l id = make_qualid ~loc (DirPath.make l) id

let my_int_of_string ?loc s =
  try
    int_of_string s
  with Failure _ ->
    CErrors.user_err ?loc (Pp.str "This number is too large.")

let my_to_nat_string ?loc s =
  match NumTok.Unsigned.to_nat s with
  | Some n -> n
  | None ->
    CErrors.user_err ?loc Pp.(str "This number is not an integer.")

let test_pipe_closedcurly =
  let open Pcoq.Lookahead in
  to_entry "test_pipe_closedcurly" begin
    lk_kw "|" >> lk_kw "}" >> check_no_space
  end

let test_minus_nat =
  let open Pcoq.Lookahead in
  to_entry "test_minus_nat" begin
    lk_kw "-" >> lk_nat >> check_no_space
  end



let _ = let field = Pcoq.Entry.make "field"
        in
        let () = assert (Pcoq.Entry.is_empty preident) in
        let () =
        Pcoq.grammar_extend preident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                  (fun s loc -> 
# 53 "parsing/g_prim.mlg"
                       s 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty ident) in
        let () =
        Pcoq.grammar_extend ident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                  (fun s loc -> 
# 56 "parsing/g_prim.mlg"
                       Id.of_string s 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty pattern_ident) in
        let () =
        Pcoq.grammar_extend pattern_ident
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PLEFTQMARK))))
                                                  ((Pcoq.Symbol.nterm ident)))
                                  (fun id _ loc -> 
# 59 "parsing/g_prim.mlg"
                                   CAst.make ~loc id 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty identref) in
        let () =
        Pcoq.grammar_extend identref
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ident)))
                                  (fun id loc -> 
# 62 "parsing/g_prim.mlg"
                        CAst.make ~loc id 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty hyp) in
        let () =
        Pcoq.grammar_extend hyp
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm identref)))
                                  (fun id loc -> 
# 65 "parsing/g_prim.mlg"
                           id 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty field) in
        let () =
        Pcoq.grammar_extend field
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PFIELD (None)))))
                                  (fun s loc -> 
# 68 "parsing/g_prim.mlg"
                       Id.of_string s 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty fields) in
        let () =
        Pcoq.grammar_extend fields
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm field)))
                                  (fun id loc -> 
# 72 "parsing/g_prim.mlg"
                        ([],id) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm field)))
                                                 ((Pcoq.Symbol.nterm fields)))
                                 (fun f id loc -> 
# 71 "parsing/g_prim.mlg"
                                    let (l,id') = f in (l@[id],id') 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty fullyqualid) in
        let () =
        Pcoq.grammar_extend fullyqualid
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ident)))
                                  (fun id loc -> 
# 77 "parsing/g_prim.mlg"
                        CAst.make ~loc [id] 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ident)))
                                                 ((Pcoq.Symbol.nterm fields)))
                                 (fun f id loc -> 
# 76 "parsing/g_prim.mlg"
                                  let (l,id') = f in CAst.make ~loc @@ id::List.rev (id'::l) 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty name) in
        let () =
        Pcoq.grammar_extend name
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ident)))
                                  (fun id loc -> 
# 82 "parsing/g_prim.mlg"
                        CAst.make ~loc @@ Name id 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("_"))))))
                                 (fun _ loc -> 
# 81 "parsing/g_prim.mlg"
                        CAst.make ~loc Anonymous 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty reference) in
        let () =
        Pcoq.grammar_extend reference
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ident)))
                                  (fun id loc -> 
# 88 "parsing/g_prim.mlg"
                        qualid_of_ident ~loc id 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm ident)))
                                                 ((Pcoq.Symbol.nterm fields)))
                                 (fun f id loc -> 
# 85 "parsing/g_prim.mlg"
                                   
        let (l,id') = f in
        local_make_qualid loc (l@[id]) id' 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty qualid) in
        let () =
        Pcoq.grammar_extend qualid
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm reference)))
                                  (fun qid loc -> 
# 92 "parsing/g_prim.mlg"
                             qid 
                                                  )])]))
        in let () = assert (Pcoq.Entry.is_empty by_notation) in
        let () =
        Pcoq.grammar_extend by_notation
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ne_string)))
                                                  ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD ("%")))))
                                                                   ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                   (fun key _
                                                                   loc -> 
                                                                   
# 95 "parsing/g_prim.mlg"
                                                       key 
                                                                   )]))))
                                  (fun sc s loc -> 
# 95 "parsing/g_prim.mlg"
                                                                    (s, sc) 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty smart_global) in
        let () =
        Pcoq.grammar_extend smart_global
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm by_notation)))
                                  (fun ntn loc -> 
# 99 "parsing/g_prim.mlg"
                               CAst.make ~loc @@ Constrexpr.ByNotation ntn 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm reference)))
                                 (fun c loc -> 
# 98 "parsing/g_prim.mlg"
                           CAst.make ~loc @@ Constrexpr.AN c 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty ne_string) in
        let () =
        Pcoq.grammar_extend ne_string
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                  (fun s loc -> 
# 103 "parsing/g_prim.mlg"
          if s="" then CErrors.user_err ~loc (Pp.str"Empty string."); s 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty ne_lstring) in
        let () =
        Pcoq.grammar_extend ne_lstring
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm ne_string)))
                                  (fun s loc -> 
# 107 "parsing/g_prim.mlg"
                           CAst.make ~loc s 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty dirpath) in
        let () =
        Pcoq.grammar_extend dirpath
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm ident)))
                                                  ((Pcoq.Symbol.list0 (Pcoq.Symbol.nterm field))))
                                  (fun l id loc -> 
# 111 "parsing/g_prim.mlg"
          DirPath.make (List.rev (id::l)) 
                                                   )])]))
        in let () = assert (Pcoq.Entry.is_empty string) in
        let () =
        Pcoq.grammar_extend string
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PSTRING (None)))))
                                  (fun s loc -> 
# 114 "parsing/g_prim.mlg"
                        s 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty lstring) in
        let () =
        Pcoq.grammar_extend lstring
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm string)))
                                  (fun s loc -> 
# 117 "parsing/g_prim.mlg"
                        CAst.make ~loc s 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty integer) in
        let () =
        Pcoq.grammar_extend integer
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm bigint)))
                                  (fun i loc -> 
# 120 "parsing/g_prim.mlg"
                        my_int_of_string ~loc i 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty natural) in
        let () =
        Pcoq.grammar_extend natural
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm bignat)))
                                  (fun i loc -> 
# 123 "parsing/g_prim.mlg"
                        my_int_of_string ~loc i 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty bigint) in
        let () =
        Pcoq.grammar_extend bigint
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm test_minus_nat)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                  ((Pcoq.Symbol.nterm bignat)))
                                  (fun i _ _ loc -> 
# 127 "parsing/g_prim.mlg"
                                             "-" ^ i 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm bignat)))
                                 (fun i loc -> 
# 126 "parsing/g_prim.mlg"
                        i 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty bignat) in
        let () =
        Pcoq.grammar_extend bignat
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PNUMBER None))))
                                  (fun i loc -> 
# 130 "parsing/g_prim.mlg"
                        my_to_nat_string ~loc i 
                                                )])]))
        in let () = assert (Pcoq.Entry.is_empty bar_cbrace) in
        let () =
        Pcoq.grammar_extend bar_cbrace
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.nterm test_pipe_closedcurly)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("|")))))
                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("}")))))
                                  (fun _ _ _ loc -> 
# 133 "parsing/g_prim.mlg"
                                             () 
                                                    )])]))
        in let () = assert (Pcoq.Entry.is_empty strategy_level) in
        let () =
        Pcoq.grammar_extend strategy_level
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                  ("transparent"))))))
                                  (fun _ loc -> 
# 139 "parsing/g_prim.mlg"
                                 Conv_oracle.transparent 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm integer)))
                                 (fun n loc -> 
# 138 "parsing/g_prim.mlg"
                       Conv_oracle.Level n 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("opaque"))))))
                                 (fun _ loc -> 
# 137 "parsing/g_prim.mlg"
                            Conv_oracle.Opaque 
                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("expand"))))))
                                 (fun _ loc -> 
# 136 "parsing/g_prim.mlg"
                            Conv_oracle.Expand 
                                               )])]))
        in ()

