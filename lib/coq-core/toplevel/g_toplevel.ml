
# 11 "toplevel/g_toplevel.mlg"
 
open Pcoq
open Pcoq.Prim
open Vernacexpr

(* Vernaculars specific to the toplevel *)
type vernac_toplevel =
  | VernacBackTo of int
  | VernacDrop
  | VernacQuit
  | VernacControl of vernac_control
  | VernacShowGoal of { gid : int; sid: int }
  | VernacShowProofDiffs of Proof_diffs.diffOpt

module Toplevel_ : sig
  val vernac_toplevel : vernac_toplevel option Entry.t
end = struct
  let gec_vernac s = Entry.create ("toplevel:" ^ s)
  let vernac_toplevel = gec_vernac "vernac_toplevel"
end

open Toplevel_

let err () = raise Stream.Failure

let test_show_goal =
  let open Pcoq.Lookahead in
  to_entry "test_show_goal" begin
   lk_kw "Show" >> lk_kw "Goal" >> lk_nat
  end



let _ = let () =
        Pcoq.grammar_extend vernac_toplevel
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm Pvernac.Vernac_.main_entry)))
                                  (fun cmd loc -> 
# 58 "toplevel/g_toplevel.mlg"
                match cmd with
              | None -> None
              | Some v -> Some (VernacControl v) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Show"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Proof"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Diffs"))))))
                                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.rules 
                                                                 [Pcoq.Rules.make 
                                                                 (Pcoq.Rule.next_norec 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("removed"))))))
                                                                 (fun _
                                                                 loc -> 
                                                                 
# 54 "toplevel/g_toplevel.mlg"
                                                                                         () 
                                                                 )]))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ removed _ _ _ loc -> 
# 55 "toplevel/g_toplevel.mlg"
          Some (VernacShowProofDiffs
          (if removed = None then Proof_diffs.DiffOn else Proof_diffs.DiffRemoved)) 
                                                             );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.nterm test_show_goal)))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Show"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Goal"))))))
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("at"))))))
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ sid _ gid _ _ _ loc -> 
# 53 "toplevel/g_toplevel.mlg"
            Some (VernacShowGoal {gid; sid}) 
                                                               );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("BackTo"))))))
                                                                 ((Pcoq.Symbol.nterm natural)))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ n _ loc -> 
# 50 "toplevel/g_toplevel.mlg"
          Some (VernacBackTo n) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Quit"))))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ _ loc -> 
# 48 "toplevel/g_toplevel.mlg"
                               Some VernacQuit 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Drop"))))))
                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (".")))))
                                 (fun _ _ loc -> 
# 47 "toplevel/g_toplevel.mlg"
                               Some VernacDrop 
                                                 )])]))
        in ()


# 66 "toplevel/g_toplevel.mlg"
 

let vernac_toplevel pm =
  Pvernac.Unsafe.set_tactic_entry pm;
  vernac_toplevel



