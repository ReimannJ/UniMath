
# 11 "plugins/ltac/extraargs.mlg"
 

open Pp
open Stdarg
open Tacarg
open Pcoq.Prim
open Pcoq.Constr
open Names
open Tacexpr
open Taccoerce
open Tacinterp
open Locus

(** Adding scopes for generic arguments not defined through ARGUMENT EXTEND *)

let create_generic_quotation name e wit =
  let inject (loc, v) = Tacexpr.TacGeneric (Some name, Genarg.in_gen (Genarg.rawwit wit) v) in
  Tacentries.create_ltac_quotation name inject (e, None)

let () = create_generic_quotation "integer" Pcoq.Prim.integer Stdarg.wit_int
let () = create_generic_quotation "string" Pcoq.Prim.string Stdarg.wit_string

let () = create_generic_quotation "smart_global" Pcoq.Prim.smart_global Stdarg.wit_smart_global

let () = create_generic_quotation "ident" Pcoq.Prim.ident Stdarg.wit_ident
let () = create_generic_quotation "reference" Pcoq.Prim.reference Stdarg.wit_ref
let () = create_generic_quotation "uconstr" Pcoq.Constr.lconstr Stdarg.wit_uconstr
let () = create_generic_quotation "constr" Pcoq.Constr.lconstr Stdarg.wit_constr
let () = create_generic_quotation "ipattern" Pltac.simple_intropattern wit_simple_intropattern
let () = create_generic_quotation "open_constr" Pcoq.Constr.lconstr Stdarg.wit_open_constr
let () =
  let inject (loc, v) = Tacexpr.Tacexp v in
  Tacentries.create_ltac_quotation "ltac" inject (Pltac.ltac_expr, Some 5)

(** Backward-compatible tactic notation entry names *)

let () =
  let register name entry = Tacentries.register_tactic_notation_entry name entry in
  register "hyp" wit_hyp;
  register "simple_intropattern" wit_simple_intropattern;
  register "integer" wit_integer;
  register "reference" wit_ref;
  ()

(* Rewriting orientation *)

let pr_orient _prc _prlc _prt = function
  | true -> Pp.mt ()
  | false -> Pp.str " <-"



let (wit_orient, orient) = Tacentries.argument_extend ~name:"orient" 
                           {
                           Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                    [(Pcoq.Production.make
                                                      (Pcoq.Rule.stop)
                                                      (fun loc -> 
# 66 "plugins/ltac/extraargs.mlg"
           true 
                                                                  ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.token (CLexer.terminal "<-"))))
                                                     (fun _ loc -> 
# 65 "plugins/ltac/extraargs.mlg"
                false 
                                                                   ));
                                                    (Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.token (CLexer.terminal "->"))))
                                                     (fun _ loc -> 
# 64 "plugins/ltac/extraargs.mlg"
                true 
                                                                   ))]);
                           Tacentries.arg_tag = Some
                                                (Geninterp.val_tag (Genarg.topwit wit_bool));
                           Tacentries.arg_intern = Tacentries.ArgInternWit (wit_bool);
                           Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_bool);
                           Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_bool);
                           Tacentries.arg_printer = ((fun env sigma -> 
                                                    
# 63 "plugins/ltac/extraargs.mlg"
                                                  pr_orient 
                                                    ), (fun env sigma -> 
                                                    
# 63 "plugins/ltac/extraargs.mlg"
                                                  pr_orient 
                                                    ), (fun env sigma -> 
                                                    
# 63 "plugins/ltac/extraargs.mlg"
                                                  pr_orient 
                                                    ));
                           }
let _ = (wit_orient, orient)


# 69 "plugins/ltac/extraargs.mlg"
 

let pr_int _ _ _ i = Pp.int i

let _natural = Pcoq.Prim.natural



let (wit_natural, natural) = Tacentries.argument_extend ~name:"natural" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_alias (_natural);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.val_tag (Genarg.topwit wit_int));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (wit_int);
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_int);
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_int);
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 77 "plugins/ltac/extraargs.mlg"
                                                  pr_int 
                                                      ), (fun env sigma -> 
                                                      
# 77 "plugins/ltac/extraargs.mlg"
                                                  pr_int 
                                                      ), (fun env sigma -> 
                                                      
# 77 "plugins/ltac/extraargs.mlg"
                                                  pr_int 
                                                      ));
                             }
let _ = (wit_natural, natural)


# 81 "plugins/ltac/extraargs.mlg"
 

let pr_orient = pr_orient () () ()

let pr_int_list = Pp.pr_sequence Pp.int
let pr_int_list_full _prc _prlc _prt l = pr_int_list l

let pr_occurrences _prc _prlc _prt l =
  match l with
    | ArgArg x -> pr_int_list x
    | ArgVar { CAst.loc = loc; v=id } -> Id.print id

let occurrences_of = function
  | [] -> NoOccurrences
  | n::_ as nl when n < 0 -> AllOccurrencesBut (List.map abs nl)
  | nl ->
      if List.exists (fun n -> n < 0) nl then
        CErrors.user_err Pp.(str "Illegal negative occurrence number.");
      OnlyOccurrences nl

let coerce_to_int v = match Value.to_int v with
  | None -> raise (CannotCoerceTo "an integer")
  | Some n -> n

let int_list_of_VList v = match Value.to_list v with
| Some l -> List.map (fun n -> coerce_to_int n) l
| _ -> raise (CannotCoerceTo "an integer")

let interp_occs ist env sigma l =
  match l with
    | ArgArg x -> x
    | ArgVar ({ CAst.v = id } as locid) ->
        (try int_list_of_VList (Id.Map.find id ist.lfun)
          with Not_found | CannotCoerceTo _ -> [interp_int ist locid])

let glob_occs ist l = l

let subst_occs evm l = l



let (wit_occurrences, occurrences) = Tacentries.argument_extend ~name:"occurrences" 
                                     {
                                     Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                              [(Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.nterm hyp)))
                                                                (fun id
                                                                loc -> 
                                                                
# 134 "plugins/ltac/extraargs.mlg"
                   ArgVar id 
                                                                ));
                                                              (Pcoq.Production.make
                                                               (Pcoq.Rule.next 
                                                               (Pcoq.Rule.stop)
                                                               ((Pcoq.Symbol.list1 ((Pcoq.Symbol.nterm integer)))))
                                                               (fun l loc ->
                                                               
# 133 "plugins/ltac/extraargs.mlg"
                              ArgArg l 
                                                               ))]);
                                     Tacentries.arg_tag = Some
                                                          (Geninterp.Val.List 
                                                          (Geninterp.val_tag (Genarg.topwit wit_int)));
                                     Tacentries.arg_intern = Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                             
# 127 "plugins/ltac/extraargs.mlg"
                  glob_occs 
                                                             ));
                                     Tacentries.arg_subst = Tacentries.ArgSubstFun (
                                                            
# 128 "plugins/ltac/extraargs.mlg"
                   subst_occs 
                                                            );
                                     Tacentries.arg_interp = Tacentries.ArgInterpSimple (
                                                             
# 126 "plugins/ltac/extraargs.mlg"
                   interp_occs 
                                                             );
                                     Tacentries.arg_printer = ((fun env sigma -> 
                                                              
# 130 "plugins/ltac/extraargs.mlg"
                   pr_occurrences 
                                                              ), (fun env sigma -> 
                                                              
# 131 "plugins/ltac/extraargs.mlg"
                    pr_occurrences 
                                                              ), (fun env sigma -> 
                                                              
# 124 "plugins/ltac/extraargs.mlg"
               pr_int_list_full 
                                                              ));
                                     }
let _ = (wit_occurrences, occurrences)


# 137 "plugins/ltac/extraargs.mlg"
 

let pr_occurrences = pr_occurrences () () ()

let pr_gen env sigma prc _prlc _prtac x = prc env sigma x

let pr_globc env sigma _prc _prlc _prtac (_,glob) =
  Printer.pr_glob_constr_env env sigma glob

let interp_glob ist env sigma (t,_) = (ist,t)

let glob_glob = Tacintern.intern_constr

let pr_lconstr env sigma _ prc _ c = prc env sigma c

let subst_glob = Tacsubst.subst_glob_constr_and_expr



let (wit_glob, glob) = Tacentries.argument_extend ~name:"glob" {
                                                               Tacentries.arg_parsing = 
                                                               Vernacextend.Arg_alias (constr);
                                                               Tacentries.arg_tag = 
                                                               None;
                                                               Tacentries.arg_intern = 
                                                               Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                               
# 160 "plugins/ltac/extraargs.mlg"
                     glob_glob 
                                                               ));
                                                               Tacentries.arg_subst = 
                                                               Tacentries.ArgSubstFun (
                                                               
# 161 "plugins/ltac/extraargs.mlg"
                      subst_glob 
                                                               );
                                                               Tacentries.arg_interp = 
                                                               Tacentries.ArgInterpSimple (
                                                               
# 159 "plugins/ltac/extraargs.mlg"
                      interp_glob 
                                                               );
                                                               Tacentries.arg_printer = 
                                                               ((fun env sigma -> 
                                                               
# 163 "plugins/ltac/extraargs.mlg"
                      pr_gen env sigma 
                                                               ), (fun env sigma -> 
                                                               
# 164 "plugins/ltac/extraargs.mlg"
                       pr_gen env sigma 
                                                               ), (fun env sigma -> 
                                                               
# 157 "plugins/ltac/extraargs.mlg"
                 pr_globc env sigma 
                                                               ));
                                                               }
let _ = (wit_glob, glob)


# 168 "plugins/ltac/extraargs.mlg"
 

let l_constr = Pcoq.Constr.lconstr



let (wit_lconstr, lconstr) = Tacentries.argument_extend ~name:"lconstr" 
                             {
                             Tacentries.arg_parsing = Vernacextend.Arg_alias (l_constr);
                             Tacentries.arg_tag = Some
                                                  (Geninterp.val_tag (Genarg.topwit wit_constr));
                             Tacentries.arg_intern = Tacentries.ArgInternWit (wit_constr);
                             Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_constr);
                             Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_constr);
                             Tacentries.arg_printer = ((fun env sigma -> 
                                                      
# 176 "plugins/ltac/extraargs.mlg"
                 pr_lconstr env sigma 
                                                      ), (fun env sigma -> 
                                                      
# 176 "plugins/ltac/extraargs.mlg"
                 pr_lconstr env sigma 
                                                      ), (fun env sigma -> 
                                                      
# 176 "plugins/ltac/extraargs.mlg"
                 pr_lconstr env sigma 
                                                      ));
                             }
let _ = (wit_lconstr, lconstr)

let (wit_lglob, lglob) = Tacentries.argument_extend ~name:"lglob" {
                                                                  Tacentries.arg_parsing = 
                                                                  Vernacextend.Arg_alias (lconstr);
                                                                  Tacentries.arg_tag = 
                                                                  Some
                                                                  (Geninterp.val_tag (Genarg.topwit wit_glob));
                                                                  Tacentries.arg_intern = 
                                                                  Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                                  
# 185 "plugins/ltac/extraargs.mlg"
                     glob_glob 
                                                                  ));
                                                                  Tacentries.arg_subst = 
                                                                  Tacentries.ArgSubstFun (
                                                                  
# 186 "plugins/ltac/extraargs.mlg"
                      subst_glob 
                                                                  );
                                                                  Tacentries.arg_interp = 
                                                                  Tacentries.ArgInterpSimple (
                                                                  
# 184 "plugins/ltac/extraargs.mlg"
                      interp_glob 
                                                                  );
                                                                  Tacentries.arg_printer = 
                                                                  ((fun env sigma -> 
                                                                  
# 188 "plugins/ltac/extraargs.mlg"
                      pr_gen env sigma 
                                                                  ), (fun env sigma -> 
                                                                  
# 189 "plugins/ltac/extraargs.mlg"
                       pr_gen env sigma 
                                                                  ), (fun env sigma -> 
                                                                  
# 182 "plugins/ltac/extraargs.mlg"
                 pr_globc env sigma 
                                                                  ));
                                                                  }
let _ = (wit_lglob, lglob)


# 193 "plugins/ltac/extraargs.mlg"
 

type 'id gen_place= ('id * hyp_location_flag,unit) location

type loc_place = lident gen_place
type place = Id.t gen_place

let pr_gen_place pr_id = function
    ConclLocation () -> Pp.mt ()
  | HypLocation (id,InHyp) -> str "in " ++ pr_id id
  | HypLocation (id,InHypTypeOnly) ->
      str "in (type of " ++ pr_id id ++ str ")"
  | HypLocation (id,InHypValueOnly) ->
      str "in (value of " ++ pr_id id ++ str ")"

let pr_loc_place _ _ _ = pr_gen_place (fun { CAst.v = id } -> Id.print id)
let pr_place _ _ _ = pr_gen_place Id.print
let pr_hloc = pr_loc_place () () ()

let intern_place ist = function
    ConclLocation () -> ConclLocation ()
  | HypLocation (id,hl) -> HypLocation (Tacintern.intern_hyp ist id,hl)

let interp_place ist env sigma = function
    ConclLocation () -> ConclLocation ()
  | HypLocation (id,hl) -> HypLocation (Tacinterp.interp_hyp ist env sigma id,hl)

let subst_place subst pl = pl



let (wit_hloc, hloc) = Tacentries.argument_extend ~name:"hloc" {
                                                               Tacentries.arg_parsing = 
                                                               Vernacextend.Arg_rules (
                                                               [(Pcoq.Production.make
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.next 
                                                                 (Pcoq.Rule.stop)
                                                                 ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                                 ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                                 ((Pcoq.Symbol.token (CLexer.terminal "value"))))
                                                                 ((Pcoq.Symbol.token (CLexer.terminal "of"))))
                                                                 ((Pcoq.Symbol.nterm ident)))
                                                                 ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                                 (fun _ id _
                                                                 _ _ _ loc ->
                                                                 
# 240 "plugins/ltac/extraargs.mlg"
      HypLocation ((CAst.make id),InHypValueOnly) 
                                                                 ));
                                                               (Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                                ((Pcoq.Symbol.token (CLexer.terminal "("))))
                                                                ((Pcoq.Symbol.token (CLexer.terminal "type"))))
                                                                ((Pcoq.Symbol.token (CLexer.terminal "of"))))
                                                                ((Pcoq.Symbol.nterm ident)))
                                                                ((Pcoq.Symbol.token (CLexer.terminal ")"))))
                                                                (fun _ id _ _
                                                                _ _ loc -> 
                                                                
# 238 "plugins/ltac/extraargs.mlg"
      HypLocation ((CAst.make id),InHypTypeOnly) 
                                                                ));
                                                               (Pcoq.Production.make
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.next 
                                                                (Pcoq.Rule.stop)
                                                                ((Pcoq.Symbol.token (CLexer.terminal "in"))))
                                                                ((Pcoq.Symbol.nterm ident)))
                                                                (fun id _
                                                                loc -> 
                                                                
# 236 "plugins/ltac/extraargs.mlg"
      HypLocation ((CAst.make id),InHyp) 
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
                                                                
# 234 "plugins/ltac/extraargs.mlg"
      ConclLocation () 
                                                                ));
                                                               (Pcoq.Production.make
                                                                (Pcoq.Rule.stop)
                                                                (fun loc -> 
# 232 "plugins/ltac/extraargs.mlg"
      ConclLocation () 
                                                                    ))]);
                                                               Tacentries.arg_tag = 
                                                               None;
                                                               Tacentries.arg_intern = 
                                                               Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                               
# 227 "plugins/ltac/extraargs.mlg"
                    intern_place 
                                                               ));
                                                               Tacentries.arg_subst = 
                                                               Tacentries.ArgSubstFun (
                                                               
# 228 "plugins/ltac/extraargs.mlg"
                     subst_place 
                                                               );
                                                               Tacentries.arg_interp = 
                                                               Tacentries.ArgInterpSimple (
                                                               
# 226 "plugins/ltac/extraargs.mlg"
                     interp_place 
                                                               );
                                                               Tacentries.arg_printer = 
                                                               ((fun env sigma -> 
                                                               
# 229 "plugins/ltac/extraargs.mlg"
                     pr_loc_place 
                                                               ), (fun env sigma -> 
                                                               
# 230 "plugins/ltac/extraargs.mlg"
                      pr_loc_place 
                                                               ), (fun env sigma -> 
                                                               
# 225 "plugins/ltac/extraargs.mlg"
                 pr_place 
                                                               ));
                                                               }
let _ = (wit_hloc, hloc)


# 244 "plugins/ltac/extraargs.mlg"
 

let pr_rename _ _ _ (n, m) = Id.print n ++ str " into " ++ Id.print m



let (wit_rename, rename) = Tacentries.argument_extend ~name:"rename" 
                           {
                           Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                    [(Pcoq.Production.make
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.next 
                                                      (Pcoq.Rule.stop)
                                                      ((Pcoq.Symbol.nterm ident)))
                                                      ((Pcoq.Symbol.token (CLexer.terminal "into"))))
                                                      ((Pcoq.Symbol.nterm ident)))
                                                      (fun m _ n loc -> 
# 253 "plugins/ltac/extraargs.mlg"
                                    (n, m) 
                                                                    ))]);
                           Tacentries.arg_tag = Some
                                                (Geninterp.Val.Pair (
                                                (Geninterp.val_tag (Genarg.topwit wit_ident)), 
                                                (Geninterp.val_tag (Genarg.topwit wit_ident))));
                           Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.PairArg (
                                                   (wit_ident), (wit_ident)));
                           Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.PairArg (
                                                  (wit_ident), (wit_ident)));
                           Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.PairArg (
                                                   (wit_ident), (wit_ident)));
                           Tacentries.arg_printer = ((fun env sigma -> 
                                                    
# 252 "plugins/ltac/extraargs.mlg"
               pr_rename 
                                                    ), (fun env sigma -> 
                                                    
# 252 "plugins/ltac/extraargs.mlg"
               pr_rename 
                                                    ), (fun env sigma -> 
                                                    
# 252 "plugins/ltac/extraargs.mlg"
               pr_rename 
                                                    ));
                           }
let _ = (wit_rename, rename)


# 258 "plugins/ltac/extraargs.mlg"
 

let pr_by_arg_tac env sigma _prc _prlc prtac opt_c =
  match opt_c with
    | None -> mt ()
    | Some t -> hov 2 (str "by" ++ spc () ++ prtac env sigma (Constrexpr.LevelLe 3) t)



let (wit_by_arg_tac, by_arg_tac) = Tacentries.argument_extend ~name:"by_arg_tac" 
                                   {
                                   Tacentries.arg_parsing = Vernacextend.Arg_rules (
                                                            [(Pcoq.Production.make
                                                              (Pcoq.Rule.stop)
                                                              (fun loc -> 
# 271 "plugins/ltac/extraargs.mlg"
           None 
                                                                    ));
                                                            (Pcoq.Production.make
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.next 
                                                             (Pcoq.Rule.stop)
                                                             ((Pcoq.Symbol.token (CLexer.terminal "by"))))
                                                             ((Pcoq.Symbol.nterml Pltac.ltac_expr ("3"))))
                                                             (fun c _ loc ->
                                                             
# 270 "plugins/ltac/extraargs.mlg"
                           Some c 
                                                             ))]);
                                   Tacentries.arg_tag = Some
                                                        (Geninterp.Val.Opt 
                                                        (Geninterp.val_tag (Genarg.topwit wit_tactic)));
                                   Tacentries.arg_intern = Tacentries.ArgInternWit (Genarg.OptArg 
                                                           (wit_tactic));
                                   Tacentries.arg_subst = Tacentries.ArgSubstWit (Genarg.OptArg 
                                                          (wit_tactic));
                                   Tacentries.arg_interp = Tacentries.ArgInterpWit (Genarg.OptArg 
                                                           (wit_tactic));
                                   Tacentries.arg_printer = ((fun env sigma -> 
                                                            
# 269 "plugins/ltac/extraargs.mlg"
               pr_by_arg_tac env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 269 "plugins/ltac/extraargs.mlg"
               pr_by_arg_tac env sigma 
                                                            ), (fun env sigma -> 
                                                            
# 269 "plugins/ltac/extraargs.mlg"
               pr_by_arg_tac env sigma 
                                                            ));
                                   }
let _ = (wit_by_arg_tac, by_arg_tac)


# 274 "plugins/ltac/extraargs.mlg"
 

let pr_by_arg_tac env sigma prtac opt_c = pr_by_arg_tac env sigma () () prtac opt_c

let pr_in_clause _ _ _ cl = Pptactic.pr_in_clause Pputils.pr_lident cl
let pr_in_top_clause _ _ _ cl = Pptactic.pr_in_clause Id.print cl
let in_clause' = Pltac.in_clause



let (wit_in_clause, in_clause) = Tacentries.argument_extend ~name:"in_clause" 
                                 {
                                 Tacentries.arg_parsing = Vernacextend.Arg_alias (in_clause');
                                 Tacentries.arg_tag = Some
                                                      (Geninterp.val_tag (Genarg.topwit wit_clause_dft_concl));
                                 Tacentries.arg_intern = Tacentries.ArgInternWit (wit_clause_dft_concl);
                                 Tacentries.arg_subst = Tacentries.ArgSubstWit (wit_clause_dft_concl);
                                 Tacentries.arg_interp = Tacentries.ArgInterpWit (wit_clause_dft_concl);
                                 Tacentries.arg_printer = ((fun env sigma -> 
                                                          
# 287 "plugins/ltac/extraargs.mlg"
                   pr_in_clause 
                                                          ), (fun env sigma -> 
                                                          
# 288 "plugins/ltac/extraargs.mlg"
                    pr_in_clause 
                                                          ), (fun env sigma -> 
                                                          
# 286 "plugins/ltac/extraargs.mlg"
               pr_in_top_clause 
                                                          ));
                                 }
let _ = (wit_in_clause, in_clause)


# 292 "plugins/ltac/extraargs.mlg"
 

let local_test_lpar_id_colon =
  let open Pcoq.Lookahead in
  to_entry "lpar_id_colon" begin
    lk_kw "(" >> lk_ident >> lk_kw ":"
  end

let pr_lpar_id_colon _ _ _ _ = mt ()



let (wit_test_lpar_id_colon, test_lpar_id_colon) = Tacentries.argument_extend ~name:"test_lpar_id_colon" 
                                                   {
                                                   Tacentries.arg_parsing = 
                                                   Vernacextend.Arg_rules (
                                                   [(Pcoq.Production.make
                                                     (Pcoq.Rule.next 
                                                     (Pcoq.Rule.stop)
                                                     ((Pcoq.Symbol.nterm local_test_lpar_id_colon)))
                                                     (fun x loc -> 
# 305 "plugins/ltac/extraargs.mlg"
                                       () 
                                                                   ))]);
                                                   Tacentries.arg_tag = 
                                                   Some
                                                   (Geninterp.val_tag (Genarg.topwit wit_unit));
                                                   Tacentries.arg_intern = 
                                                   Tacentries.ArgInternWit (wit_unit);
                                                   Tacentries.arg_subst = 
                                                   Tacentries.ArgSubstWit (wit_unit);
                                                   Tacentries.arg_interp = 
                                                   Tacentries.ArgInterpWit (wit_unit);
                                                   Tacentries.arg_printer = 
                                                   ((fun env sigma -> 
                                                   
# 304 "plugins/ltac/extraargs.mlg"
                                                              pr_lpar_id_colon 
                                                   ), (fun env sigma -> 
                                                   
# 304 "plugins/ltac/extraargs.mlg"
                                                              pr_lpar_id_colon 
                                                   ), (fun env sigma -> 
                                                   
# 304 "plugins/ltac/extraargs.mlg"
                                                              pr_lpar_id_colon 
                                                   ));
                                                   }
let _ = (wit_test_lpar_id_colon, test_lpar_id_colon)


# 308 "plugins/ltac/extraargs.mlg"
 

(* Work around a limitation of the macro system *)
let strategy_level0 = Pcoq.Prim.strategy_level

let pr_strategy _ _ _ v = Conv_oracle.pr_level v



let (wit_strategy_level, strategy_level) = Tacentries.argument_extend ~name:"strategy_level" 
                                           {
                                           Tacentries.arg_parsing = Vernacextend.Arg_alias (strategy_level0);
                                           Tacentries.arg_tag = None;
                                           Tacentries.arg_intern = Tacentries.ArgInternFun (fun ist v -> (ist, v));
                                           Tacentries.arg_subst = Tacentries.ArgSubstFun (fun s v -> v);
                                           Tacentries.arg_interp = Tacentries.ArgInterpRet;
                                           Tacentries.arg_printer = ((fun env sigma -> 
                                                                    
# 317 "plugins/ltac/extraargs.mlg"
                                            pr_strategy 
                                                                    ), (fun env sigma -> 
                                                                    
# 317 "plugins/ltac/extraargs.mlg"
                                            pr_strategy 
                                                                    ), (fun env sigma -> 
                                                                    
# 317 "plugins/ltac/extraargs.mlg"
                                            pr_strategy 
                                                                    ));
                                           }
let _ = (wit_strategy_level, strategy_level)


# 321 "plugins/ltac/extraargs.mlg"
 

let intern_strategy ist v = match v with
| ArgVar id -> ArgVar (Tacintern.intern_hyp ist id)
| ArgArg v -> ArgArg v

let subst_strategy _ v = v

let interp_strategy ist env sigma = function
| ArgArg n -> n
| ArgVar { CAst.v = id; CAst.loc } ->
  let v =
    try Id.Map.find id ist.lfun
    with Not_found ->
      CErrors.user_err ?loc
        (str "Unbound variable " ++ Id.print id ++ str".")
  in
  let v =
    try Tacinterp.Value.cast (Genarg.topwit wit_strategy_level) v
    with CErrors.UserError _ -> Taccoerce.error_ltac_variable ?loc id None v "a strategy_level"
  in
  v

let pr_loc_strategy _ _ _ v = Pputils.pr_or_var Conv_oracle.pr_level v



let (wit_strategy_level_or_var, strategy_level_or_var) = Tacentries.argument_extend ~name:"strategy_level_or_var" 
                                                         {
                                                         Tacentries.arg_parsing = 
                                                         Vernacextend.Arg_rules (
                                                         [(Pcoq.Production.make
                                                           (Pcoq.Rule.next 
                                                           (Pcoq.Rule.stop)
                                                           ((Pcoq.Symbol.nterm identref)))
                                                           (fun id loc -> 
# 357 "plugins/ltac/extraargs.mlg"
                        ArgVar id 
                                                                    ));
                                                         (Pcoq.Production.make
                                                          (Pcoq.Rule.next 
                                                          (Pcoq.Rule.stop)
                                                          ((Pcoq.Symbol.nterm strategy_level)))
                                                          (fun n loc -> 
# 356 "plugins/ltac/extraargs.mlg"
                             ArgArg n 
                                                                    ))]);
                                                         Tacentries.arg_tag = 
                                                         Some
                                                         (Geninterp.val_tag (Genarg.topwit wit_strategy_level));
                                                         Tacentries.arg_intern = 
                                                         Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (
                                                         
# 352 "plugins/ltac/extraargs.mlg"
                    intern_strategy 
                                                         ));
                                                         Tacentries.arg_subst = 
                                                         Tacentries.ArgSubstFun (
                                                         
# 353 "plugins/ltac/extraargs.mlg"
                     subst_strategy 
                                                         );
                                                         Tacentries.arg_interp = 
                                                         Tacentries.ArgInterpSimple (
                                                         
# 351 "plugins/ltac/extraargs.mlg"
                     interp_strategy 
                                                         );
                                                         Tacentries.arg_printer = 
                                                         ((fun env sigma -> 
                                                         
# 354 "plugins/ltac/extraargs.mlg"
                     pr_loc_strategy 
                                                         ), (fun env sigma -> 
                                                         
# 355 "plugins/ltac/extraargs.mlg"
                      pr_loc_strategy 
                                                         ), (fun env sigma -> 
                                                         
# 350 "plugins/ltac/extraargs.mlg"
                 pr_strategy 
                                                         ));
                                                         }
let _ = (wit_strategy_level_or_var, strategy_level_or_var)

