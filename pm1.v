Require Import Ltac2.Ltac2.
Require Import axiom.
Require Import nicod.

Definition not := fun (p : Prop) => (stroke p p).
Definition or := fun (p q : Prop) => (stroke (not p) (not q)).
Definition impl := fun (p q : Prop) => (or (not p) q).

#[local]
Theorem impl_intro : forall (p q : Prop), (stroke (stroke p (stroke q q)) (stroke (impl p q) (impl p q))).
Proof.
    intros.
    exact (mp (taut p) (syll (stroke (stroke p p) (stroke p p)) p p (stroke q q))).
Qed.

#[local]
Theorem impl_elim : forall (p q : Prop), (stroke (impl p q) (stroke (stroke p (stroke q q)) (stroke p (stroke q q)))).
Proof.
    intros.
    exact (mp (add (stroke p p) p) (syll p (stroke (stroke p p) (stroke p p)) (stroke (stroke p p) (stroke p p)) (stroke q q))).
Qed.

Theorem pm1_11 : forall {p q : Prop} (min : p) (maj : (impl p q)), q.
Proof.
    intros.
    pose (S1 := (mp maj (impl_elim p q))).
    exact (mp min S1).
Qed.

Theorem pm1_2 : forall (p : Prop), (impl (or p p) p).
Proof.
    intros.
    exact (mp (taut p) (impl_intro (or p p) p)).
Qed.

Theorem pm1_3 : forall (p q : Prop), (impl q (or p q)).
Proof.
    intros.
    exact (mp (add (stroke p p) q) (impl_intro q (or p q))).
Qed.

Theorem pm1_4 : forall (p q : Prop), (impl (or p q) (or q p)).
Proof.
    intros.
    exact (mp (perm (stroke q q) (stroke p p)) (impl_intro (or p q) (or q p))).
Qed.

Theorem pm1_5 : forall (p q r : Prop), (impl (or p (or q r)) (or q (or p r))).
Proof.
    intros.
    exact (mp (assoc (stroke p p) (stroke q q) (stroke r r)) (impl_intro (or p (or q r)) (or q (or p r)))).
Qed.

Theorem pm1_6 : forall (p q r : Prop), (impl (impl q r) (impl (or p q) (or p r))).
Proof.
    intros.
    pose (S1 := (mp (sum p q r) (syll (stroke q (stroke r r)) (stroke (or p q) (stroke (or p r) (or p r))) (stroke (or p q) (stroke (or p r) (or p r))) (stroke (impl (or p q) (or p r)) (impl (or p q) (or p r)))))).
    pose (S2 := (mp (impl_intro (or p q) (or p r)) S1)).
    pose (S3 := (mp (impl_elim q r) (syll (impl q r) (stroke q (stroke r r)) (stroke q (stroke r r)) (stroke (impl (or p q) (or p r)) (impl (or p q) (or p r)))))).
    pose (S4 := (mp S2 S3)).
    exact (mp S4 (impl_intro (impl q r) (impl (or p q) (or p r)))).
Qed.
