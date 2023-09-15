
# 11 "vernac/g_proofs.mlg"
 

open Constrexpr
open Vernacexpr
open Hints

module C = Constr

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pvernac.Vernac_

let thm_token = G_vernac.thm_token

let hint = Entry.create "hint"

let warn_deprecated_focus =
  CWarnings.create ~name:"deprecated-focus" ~category:"deprecated"
         (fun () ->
           Pp.strbrk
             "The Focus command is deprecated; use bullets or focusing brackets instead"
         )

let warn_deprecated_focus_n n =
  CWarnings.create ~name:"deprecated-focus" ~category:"deprecated"
         (fun () ->
           Pp.(str "The Focus command is deprecated;" ++ spc ()
               ++ str "use '" ++ int n ++ str ": {' instead")
         )

let warn_deprecated_unfocus =
  CWarnings.create ~name:"deprecated-unfocus" ~category:"deprecated"
         (fun () -> Pp.strbrk "The Unfocus command is deprecated")



let _ = let opt_hintbases = Pcoq.Entry.make "opt_hintbases"
        and reference_or_constr = Pcoq.Entry.make "reference_or_constr"
        and constr_body = Pcoq.Entry.make "constr_body"
        and mode = Pcoq.Entry.make "mode"
        in
        let () = assert (Pcoq.Entry.is_empty opt_hintbases) in
        let () =
        Pcoq.grammar_extend opt_hintbases
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                                                   (fun id
                                                                   loc -> 
                                                                   
# 54 "vernac/g_proofs.mlg"
                                      id 
                                                                   )])))))
                                  (fun l _ loc -> 
# 54 "vernac/g_proofs.mlg"
                                                  l 
                                                  );
                                 Pcoq.Production.make (Pcoq.Rule.stop)
                                 (fun loc -> 
# 53 "vernac/g_proofs.mlg"
           [] 
                                             )])]))
        in let () =
        Pcoq.grammar_extend command
        (Pcoq.Reuse (None, [Pcoq.Production.make
                            (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                            (Pcoq.Rule.stop)
                                                            ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                            ("Hint"))))))
                                                            ((Pcoq.Symbol.nterm hint)))
                                            ((Pcoq.Symbol.nterm opt_hintbases)))
                            (fun dbnames h _ loc -> 
# 105 "vernac/g_proofs.mlg"
            VernacHints (dbnames, h) 
                                                    );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Remove"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Hints"))))))
                                                           ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                           ((Pcoq.Symbol.nterm opt_hintbases)))
                           (fun dbnames ids _ _ loc -> 
# 103 "vernac/g_proofs.mlg"
            VernacRemoveHints (dbnames, ids) 
                                                       );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Create"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("HintDb"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (None)))))
                                           ((Pcoq.Symbol.rules [Pcoq.Rules.make 
                                                               (Pcoq.Rule.stop)
                                                               (fun loc -> 
                                                               
# 100 "vernac/g_proofs.mlg"
                                                                      false 
                                                               );
                                                               Pcoq.Rules.make 
                                                               (Pcoq.Rule.next_norec 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                               ("discriminated"))))))
                                                               (fun _ loc ->
                                                               
# 100 "vernac/g_proofs.mlg"
                                                        true 
                                                               )])))
                           (fun b id _ _ loc -> 
# 101 "vernac/g_proofs.mlg"
              VernacCreateHintDb (id, b) 
                                                );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Guarded"))))))
                           (fun _ loc -> 
# 97 "vernac/g_proofs.mlg"
                             VernacCheckGuard 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Show"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Match"))))))
                                           ((Pcoq.Symbol.nterm reference)))
                           (fun id _ _ loc -> 
# 96 "vernac/g_proofs.mlg"
                                                         VernacShow (ShowMatch id) 
                                              );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Show"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Intros"))))))
                           (fun _ _ loc -> 
# 95 "vernac/g_proofs.mlg"
                                          VernacShow (ShowIntros true) 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Show"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Intro"))))))
                           (fun _ _ loc -> 
# 94 "vernac/g_proofs.mlg"
                                         VernacShow (ShowIntros false) 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Show"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Proof"))))))
                           (fun _ _ loc -> 
# 93 "vernac/g_proofs.mlg"
                                         VernacShow ShowProof 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Show"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Conjectures"))))))
                           (fun _ _ loc -> 
# 92 "vernac/g_proofs.mlg"
                                               VernacShow ShowProofNames 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Show"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Universes"))))))
                           (fun _ _ loc -> 
# 91 "vernac/g_proofs.mlg"
                                             VernacShow ShowUniverses 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Show"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Existentials"))))))
                           (fun _ _ loc -> 
# 90 "vernac/g_proofs.mlg"
                                                VernacShow ShowExistentials 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Show"))))))
                                           ((Pcoq.Symbol.nterm ident)))
                           (fun id _ loc -> 
# 89 "vernac/g_proofs.mlg"
                                      VernacShow (ShowGoal (GoalId id)) 
                                            );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Show"))))))
                                           ((Pcoq.Symbol.nterm natural)))
                           (fun n _ loc -> 
# 88 "vernac/g_proofs.mlg"
                                       VernacShow (ShowGoal (NthGoal n)) 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Show"))))))
                           (fun _ loc -> 
# 87 "vernac/g_proofs.mlg"
                          VernacShow (ShowGoal OpenSubgoals) 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Unfocused"))))))
                           (fun _ loc -> 
# 86 "vernac/g_proofs.mlg"
                               VernacUnfocused 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Unfocus"))))))
                           (fun _ loc -> 
# 84 "vernac/g_proofs.mlg"
           warn_deprecated_unfocus ~loc ();
         VernacUnfocus 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Focus"))))))
                                           ((Pcoq.Symbol.nterm natural)))
                           (fun n _ loc -> 
# 81 "vernac/g_proofs.mlg"
           warn_deprecated_focus_n n ~loc ();
         VernacFocus (Some n) 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Focus"))))))
                           (fun _ loc -> 
# 78 "vernac/g_proofs.mlg"
           warn_deprecated_focus ~loc ();
         VernacFocus None 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Undo"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("To"))))))
                                           ((Pcoq.Symbol.nterm natural)))
                           (fun n _ _ loc -> 
# 76 "vernac/g_proofs.mlg"
                                                   VernacUndoTo n 
                                             );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Undo"))))))
                                           ((Pcoq.Symbol.nterm natural)))
                           (fun n _ loc -> 
# 75 "vernac/g_proofs.mlg"
                                       VernacUndo n 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Undo"))))))
                           (fun _ loc -> 
# 74 "vernac/g_proofs.mlg"
                          VernacUndo 1 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Restart"))))))
                           (fun _ loc -> 
# 73 "vernac/g_proofs.mlg"
                             VernacRestart 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Defined"))))))
                                           ((Pcoq.Symbol.nterm identref)))
                           (fun id _ loc -> 
# 72 "vernac/g_proofs.mlg"
            VernacEndProof (Proved (Transparent,Some id)) 
                                            );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Defined"))))))
                           (fun _ loc -> 
# 70 "vernac/g_proofs.mlg"
                             VernacEndProof (Proved (Transparent,None)) 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Save"))))))
                                           ((Pcoq.Symbol.nterm identref)))
                           (fun id _ loc -> 
# 69 "vernac/g_proofs.mlg"
            VernacEndProof (Proved (Opaque, Some id)) 
                                            );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Qed"))))))
                           (fun _ loc -> 
# 67 "vernac/g_proofs.mlg"
                         VernacEndProof (Proved (Opaque,None)) 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Admitted"))))))
                           (fun _ loc -> 
# 66 "vernac/g_proofs.mlg"
                              VernacEndProof Admitted 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Abort"))))))
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("All"))))))
                           (fun _ _ loc -> 
# 65 "vernac/g_proofs.mlg"
                                        VernacAbortAll 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Abort"))))))
                           (fun _ loc -> 
# 64 "vernac/g_proofs.mlg"
                           VernacAbort 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Proof"))))))
                                           ((Pcoq.Symbol.nterm lconstr)))
                           (fun c _ loc -> 
# 63 "vernac/g_proofs.mlg"
                                        VernacExactProof c 
                                           );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Proof"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Mode"))))))
                                           ((Pcoq.Symbol.nterm string)))
                           (fun mn _ _ loc -> 
# 62 "vernac/g_proofs.mlg"
                                                        VernacProofMode mn 
                                              );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Proof"))))))
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("using"))))))
                                           ((Pcoq.Symbol.nterm G_vernac.section_subset_expr)))
                           (fun l _ _ loc -> 
# 61 "vernac/g_proofs.mlg"
            VernacProof (None,Some l) 
                                             );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.stop)
                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                           ("Proof"))))))
                           (fun _ loc -> 
# 59 "vernac/g_proofs.mlg"
                           VernacProof (None,None) 
                                         );
                           Pcoq.Production.make
                           (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                           ("Goal"))))))
                                           ((Pcoq.Symbol.nterm lconstr)))
                           (fun c _ loc -> 
# 58 "vernac/g_proofs.mlg"
          VernacDefinition (Decls.(NoDischarge, Definition), ((CAst.make ~loc Names.Anonymous), None), ProveBody ([], c)) 
                                           )]))
        in let () = assert (Pcoq.Entry.is_empty reference_or_constr)
        in
        let () =
        Pcoq.grammar_extend reference_or_constr
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.nterm constr)))
                                  (fun c loc -> 
# 109 "vernac/g_proofs.mlg"
                       HintsConstr c 
                                                );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                 ((Pcoq.Symbol.nterm global)))
                                 (fun r loc -> 
# 108 "vernac/g_proofs.mlg"
                       HintsReference r 
                                               )])]))
        in let () = assert (Pcoq.Entry.is_empty hint) in
        let () =
        Pcoq.grammar_extend hint
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                  ("Constructors"))))))
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                  (fun lc _ loc -> 
# 127 "vernac/g_proofs.mlg"
                                                     HintsConstructors lc 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Unfold"))))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                 (fun lqid _ loc -> 
# 126 "vernac/g_proofs.mlg"
                                                 HintsUnfold lqid 
                                                    );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Mode"))))))
                                                                 ((Pcoq.Symbol.nterm global)))
                                                 ((Pcoq.Symbol.nterm mode)))
                                 (fun m l _ loc -> 
# 125 "vernac/g_proofs.mlg"
                                                HintsMode (l, m) 
                                                   );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Opaque"))))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                 (fun lc _ loc -> 
# 124 "vernac/g_proofs.mlg"
                                               HintsTransparency (HintsReferences lc, false) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Transparent"))))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                 (fun lc _ loc -> 
# 123 "vernac/g_proofs.mlg"
                                                    HintsTransparency (HintsReferences lc, true) 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Constants"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Opaque"))))))
                                 (fun _ _ loc -> 
# 122 "vernac/g_proofs.mlg"
                                               HintsTransparency (HintsConstants, false) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Constants"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Transparent"))))))
                                 (fun _ _ loc -> 
# 121 "vernac/g_proofs.mlg"
                                                    HintsTransparency (HintsConstants, true) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Variables"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Opaque"))))))
                                 (fun _ _ loc -> 
# 120 "vernac/g_proofs.mlg"
                                               HintsTransparency (HintsVariables, false) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Variables"))))))
                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                 ("Transparent"))))))
                                 (fun _ _ loc -> 
# 119 "vernac/g_proofs.mlg"
                                                    HintsTransparency (HintsVariables, true) 
                                                 );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Immediate"))))))
                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm reference_or_constr)))))
                                 (fun lc _ loc -> 
# 118 "vernac/g_proofs.mlg"
                                                               HintsImmediate lc 
                                                  );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Resolve"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("<-")))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm natural))))
                                 (fun n lc _ _ loc -> 
# 117 "vernac/g_proofs.mlg"
            HintsResolveIFF (false, lc, n) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Resolve"))))))
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD ("->")))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm global)))))
                                                 ((Pcoq.Symbol.opt (Pcoq.Symbol.nterm natural))))
                                 (fun n lc _ _ loc -> 
# 115 "vernac/g_proofs.mlg"
            HintsResolveIFF (true, lc, n) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PIDENT (Some
                                                                 ("Resolve"))))))
                                                                 ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm reference_or_constr)))))
                                                 ((Pcoq.Symbol.nterm hint_info)))
                                 (fun info lc _ loc -> 
# 113 "vernac/g_proofs.mlg"
            HintsResolve (List.map (fun x -> (info, true, x)) lc) 
                                                       )])]))
        in let () = assert (Pcoq.Entry.is_empty constr_body) in
        let () =
        Pcoq.grammar_extend constr_body
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.next 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":")))))
                                                                  ((Pcoq.Symbol.nterm lconstr)))
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                  ((Pcoq.Symbol.nterm lconstr)))
                                  (fun c _ t _ loc -> 
# 131 "vernac/g_proofs.mlg"
                                                 CAst.make ~loc @@ CCast(c,C.DEFAULTcast, t) 
                                                      );
                                 Pcoq.Production.make
                                 (Pcoq.Rule.next (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (Tok.PKEYWORD (":=")))))
                                                 ((Pcoq.Symbol.nterm lconstr)))
                                 (fun c _ loc -> 
# 130 "vernac/g_proofs.mlg"
                               c 
                                                 )])]))
        in let () = assert (Pcoq.Entry.is_empty mode) in
        let () =
        Pcoq.grammar_extend mode
        (Pcoq.Fresh
        (Gramlib.Gramext.First, [(None, None,
                                 [Pcoq.Production.make
                                  (Pcoq.Rule.next (Pcoq.Rule.stop)
                                                  ((Pcoq.Symbol.list1 ((Pcoq.Symbol.rules 
                                                  [Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                   (Pcoq.Rule.stop)
                                                                   ((Pcoq.Symbol.token (Tok.PKEYWORD ("-")))))
                                                                   (fun _
                                                                   loc -> 
                                                                   
# 136 "vernac/g_proofs.mlg"
                             ModeOutput 
                                                                   );
                                                  Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("!")))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 135 "vernac/g_proofs.mlg"
                             ModeNoHeadEvar 
                                                                  );
                                                  Pcoq.Rules.make (Pcoq.Rule.next_norec 
                                                                  (Pcoq.Rule.stop)
                                                                  ((Pcoq.Symbol.token (Tok.PKEYWORD ("+")))))
                                                                  (fun _
                                                                  loc -> 
                                                                  
# 134 "vernac/g_proofs.mlg"
                             ModeInput 
                                                                  )])))))
                                  (fun l loc -> 
# 136 "vernac/g_proofs.mlg"
                                                 l 
                                                )])]))
        in ()

