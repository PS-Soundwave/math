Require Import Ltac2.Ltac2.
Require Import axiom.
Require Import scharle.

Theorem nicod : forall (p q r s t : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).
Proof.
    intros.
    pose (S1 := (scharle4 p q r s t)).
    pose (S2 := (scharle7 (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))) (stroke p (stroke q r)))).
    pose (S3 := (mp S1 S2)).
    pose (S4 := (scharle7 (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).
    pose (S5 := (scharle (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))) (stroke p (stroke q r)))).
    pose (S6 := (mp S4 S5)).
    pose (S7 := (mp S3 S6)).
    pose (S8 := (scharle7 (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r)))).
    exact (mp S7 S8).
Qed.

Theorem id : forall (t : Prop), (stroke t (stroke t t)).
Proof.
    assert (a : forall (s t : Prop) (pi := (stroke t (stroke t t))) (Q_1 := (stroke (stroke s t) (stroke (stroke t s) (stroke t s)))), (stroke pi (stroke pi Q_1))).
    intros.
    exact (nicod t t t s t).
    assert (b : forall (s t : Prop) (pi := (stroke t (stroke t t))) (Q_1 := (stroke (stroke s t) (stroke (stroke t s) (stroke t s)))), (stroke (stroke s pi) (stroke (stroke pi s) (stroke pi s)))).
    intros.
    exact (mp (a s t) (nicod pi pi Q_1 s t)).
    assert (c : forall (s t u : Prop) (pi := (stroke t (stroke t t))), (stroke (stroke u (stroke pi s)) (stroke (stroke (stroke s pi) u) (stroke (stroke s pi) u)))).
    intros.
    exact (mp (b s t) (nicod (stroke s pi) (stroke pi s) (stroke pi s) u t)).
    assert (d : forall (p q r s t : Prop) (P := (stroke p (stroke q r))) (pi := (stroke t (stroke t t))) (Q := (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))), (stroke (stroke Q pi) P)).
    intros.
    exact (mp (nicod p q r s t) (c Q t P)).
    assert (e : forall (p q r s T : Prop) (P := (stroke p (stroke q r))) (H : (stroke T (stroke P P))), (stroke (stroke s P) (stroke (stroke T s) (stroke T s)))).
    intros.
    exact (mp H (nicod T P P s s)).
    assert (f : forall (p q r s t T : Prop) (P := (stroke p (stroke q r))) (Tw : T) (H : (stroke T (stroke P P))) (Q := (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (pi := (stroke t (stroke t t))), pi).
    intros.
    pose (S1 := (mp (d p q r s t) (e p q r (stroke Q pi) T H))).
    exact (mp Tw S1).
    assert (L : forall (s t : Prop) (pi := (stroke t (stroke t t))) (Q_1 := (stroke (stroke s t) (stroke (stroke t s) (stroke t s)))), pi).
    intros.
    pose (T := (stroke pi (stroke pi Q_1))).
    exact (f (stroke Q_1 pi) t (stroke t t) s t T (a s t) (c Q_1 t pi)).
    intros.
    exact (L t t).
Qed.

Theorem perm : forall (p s : Prop), (stroke (stroke s p) (stroke (stroke p s) (stroke p s))).
Proof.
    intros.
    exact (mp (id p) (nicod p p p s s)).
Qed.

Theorem taut : forall (p : Prop), (stroke (stroke (stroke p p) (stroke p p)) (stroke p p)).
Proof.
    intros.
    exact (mp (id (stroke p p)) (perm (stroke (stroke p p) (stroke p p)) (stroke p p))).
Qed.

Theorem add : forall (p s : Prop), (stroke s (stroke (stroke p (stroke s s)) (stroke p (stroke s s)))).
Proof.
    intros.
    pose (S1 := (mp (perm p (stroke s s)) (perm (stroke (stroke p (stroke s s)) (stroke p (stroke s s))) (stroke (stroke s s) p)))).
    pose (S2 := (mp S1 (nicod (stroke (stroke p (stroke s s)) (stroke p (stroke s s))) (stroke s s) p s s))).
    pose (S3 := (mp (id s) S2)).
    exact (mp S3 (perm s (stroke (stroke p (stroke s s)) (stroke p (stroke s s))))).
Qed.

Theorem syll_lemma : forall (p s : Prop), (stroke (stroke p p) (stroke (stroke s p) (stroke s p))).
Proof.
    assert (L : forall (p s u : Prop), (stroke (stroke u p) (stroke (stroke (stroke (stroke s p) (stroke s p)) u) (stroke (stroke (stroke s p) (stroke s p)) u)))).
    intros.
    pose (S1 := (mp (perm s p) (perm (stroke (stroke s p) (stroke s p)) (stroke p s)))).
    exact (mp S1 (nicod (stroke (stroke s p) (stroke s p)) p s u u)).
    intros.
    pose (S1 := (mp (id p) (perm (stroke p p) p))).
    pose (S2 := (mp S1 (L p s (stroke p p)))).
    exact (mp S2 (perm (stroke p p) (stroke (stroke s p) (stroke s p)))).
Qed.

Theorem gen_impl : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).
Proof.
    assert (L1 : forall (p q r s t : Prop) (P := (stroke p (stroke q r))) (pi := (stroke t (stroke t t))) (Q := (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))), (stroke (stroke P (stroke pi Q)) (stroke (stroke (stroke Q Q) P) (stroke (stroke Q Q) P)))).
    intros.
    exact (mp (syll_lemma Q pi) (nicod (stroke Q Q) (stroke pi Q) (stroke pi Q) P t)).
    assert (L2 : forall (p q r s t : Prop) (P := (stroke p (stroke q r))) (Q := (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))), (stroke P (stroke Q Q))).
    intros.
    pose (S1 := (mp (nicod p q r s t) (L1 p q r s t))).
    exact (mp S1 (perm P (stroke Q Q))).
    intros.
    exact (L2 p q r s s).
Qed.

Theorem syll : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))).
Proof.
    assert (a : forall (q s u : Prop), (stroke (stroke (stroke (stroke q s) u) (stroke (stroke q s) u)) (stroke u (stroke s q)))).
    intros.
    pose (S1 := (mp (perm s q) (gen_impl (stroke q s) (stroke s q) (stroke s q) u))).
    exact (mp S1 (perm (stroke (stroke (stroke q s) u) (stroke (stroke q s) u)) (stroke u (stroke s q)))).
    assert (b : forall (q s u : Prop), (stroke (stroke (stroke (stroke q s) u) (stroke (stroke q s) u)) (stroke (stroke s q) u))).
    intros.
    pose (S1 := (mp (perm u (stroke s q)) (gen_impl (stroke (stroke s q) u) (stroke u (stroke s q)) (stroke u (stroke s q)) (stroke (stroke (stroke q s) u) (stroke (stroke q s) u))))).
    pose (S2 := (mp (a q s u) S1)).
    exact (mp S2 (perm (stroke (stroke (stroke q s) u) (stroke (stroke q s) u)) (stroke (stroke s q) u))).
    intros.
    pose (S1 := (mp (gen_impl p q r s) (gen_impl (stroke p (stroke q r)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))))).
    exact (mp (b q s (stroke (stroke p s) (stroke p s))) S1).
Qed.

Theorem assoc : forall (p q r : Prop), (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))).
Proof.
    assert (L : forall (p q : Prop) (L := (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))), L).
    intros.
    assert (a : (stroke q (stroke L L))).
    pose (L1 := (syll p q q p)).
    pose (S1 := (mp (add p q) (syll q (stroke p (stroke q q)) (stroke p (stroke q q)) (stroke (stroke (stroke q p) (stroke (stroke p p) (stroke p p))) (stroke (stroke q p) (stroke (stroke p p) (stroke p p))))))).
    pose (L2 := (mp L1 S1)).
    pose (L3 := (syll (stroke q p) (stroke p p) (stroke p p) p)).
    pose (S2 := (mp (id p) (perm (stroke p p) p))).
    pose (L4 := (mp S2 (add q (stroke (stroke p p) p)))).
    pose (S3 := (mp L2 (syll q (stroke (stroke q p) (stroke (stroke p p) (stroke p p))) (stroke (stroke q p) (stroke (stroke p p) (stroke p p))) (stroke (stroke (stroke (stroke p p) p) (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke (stroke (stroke p p) p) (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))))))).
    pose (S4 := (mp L3 S3)).
    pose (S5 := (mp L4 (syll q (stroke (stroke p p) p) (stroke (stroke p p) p) (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))))).
    pose (S6 := (mp S4 (syll q (stroke (stroke (stroke p p) p) (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke (stroke (stroke p p) p) (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke L L)))).
    exact (mp S5 S6).
    assert (b : (stroke (stroke L L) (stroke q q))).
    assert (L1 : forall (s : Prop), (stroke (stroke q q) (stroke (stroke q s) (stroke q s)))).
    intros.
    pose (S1 := (mp (syll_lemma q s) (syll (stroke q q) (stroke s q) (stroke s q) (stroke (stroke q s) (stroke q s))))).
    exact (mp (perm q s) S1).
    pose (S1 := (L1 (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))).
    exact (mp S1 (perm (stroke L L) (stroke q q))).
    pose (S1 := (syll (stroke L L) q q (stroke L L))).
    pose (S2 := (mp b S1)).
    pose (S3 := (mp a S2)).
    exact (mp S3 (taut L)).
    intros.
    pose (S1 := (syll p (stroke q r) (stroke q r) r)).
    pose (S2 := (mp (L r q) (syll q (stroke (stroke q r) r) (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))))).
    pose (S3 := (mp S1 (syll (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))))).
    exact (mp S2 S3).
Qed.

Theorem sum : forall (p q r : Prop), (stroke (stroke q (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))).
Proof.
    assert (L : forall (p q r s : Prop), (stroke (stroke q s) (stroke (stroke (stroke p (stroke q r)) (stroke (stroke p s) (stroke p s))) (stroke (stroke p (stroke q r)) (stroke (stroke p s) (stroke p s)))))).
    intros.
    exact (mp (syll p q r s) (assoc (stroke p (stroke q r)) (stroke q s) (stroke (stroke p s) (stroke p s)))).
    intros.
    exact (L (stroke p p) q q (stroke r r)).
Qed.
