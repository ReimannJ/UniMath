(** * Decidable sets. *)
(** Gianluca Amato,  Marco Maggesi, Cosimo Perini Brogi 2019-2021 *)
(*
In this file we introduce the type [decSet] of h-sets of decidable sets, i.e., types [X] endowed with the
property [isdeceq X], just like an [hSet] is a type X endowed with the property [isaset X].
*)

Require Import UniMath.Foundations.PartB.

Definition decSet: Type := ∑ (X: Type), isdeceq X.

Definition make_decSet (X: Type) (i: isdeceq X): decSet := X,, i.

Definition pr1decSet: decSet -> Type := pr1.

Coercion pr1decSet: decSet >-> Sortclass.

Definition decproperty (X: decSet) := pr2 X.
