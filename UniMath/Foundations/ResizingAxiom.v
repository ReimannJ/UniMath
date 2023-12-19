Require Export UniMath.Foundations.Propositions.

(* Axioms are currently in Propositions.v!


Set Printing Universes.
(* hProp@{i j} = ∑ (X : Type@{i}, is : isaprop X) : Type@{j} with constraint i < j*)
Print hProp.
Print total2.
Print make_hProp.

#[bypass_check(universes)] (* only constraint is l < k*)
Definition resizingStatement@{i k l} := forall (X : Type@{i}) (is: isaprop X), hProp@{k l}.
Print resizingStatement.

Axiom resizingAxiom : resizingStatement.

Definition resizingEquivalenceStatement := forall (X : Type@{i}) (is: isaprop X), make_hProp X is ≃ resizingAxiom X is.
Print resizingEquivalenceStatement.

Axiom resizingEquivalence : resizingEquivalenceStatement.
Print resizingEquivalence.

Variable X : Type@{i}.
Variable is: isaprop X.

Definition example1 := resizingAxiom X is.
Print example1.

Definition example2 := resizingEquivalence X is.
Print example2.

*)
