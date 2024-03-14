Require Import pm1.

Require Export universe.

Section axiom_pred.

Context {uni : Universe}.

Axiom all : forall (_ : forall (_ : U), Prop), Prop.

Axiom spec : forall (P : forall (_ : U), Prop) (x : U), (impl (all P) (P x)).

Axiom gen : forall {p : Prop} {Q : forall (_ : U), Prop} (H : forall (x : U), (impl p (Q x))), (impl p (all Q)).

Definition ex := fun (P : forall (_ : U), Prop) => (not (all (fun (x : U) => (not (P x))))).

End axiom_pred.
