Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".

Axiom stroke : forall (p q : Prop), Prop.

Axiom ax_mp : forall {p q r : Prop} (min : p) (maj : (stroke p (stroke q r))), r.
Axiom ax_luk : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke s (stroke s s)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).

Theorem scharle2 : forall (p q r s t : Prop), (stroke (stroke t (stroke s (stroke s s))) (stroke (stroke (stroke p (stroke q r)) t) (stroke (stroke p (stroke q r)) t))).
Proof.
    intros.
    pose (S1 := (ax_luk (stroke p (stroke q r)) (stroke s (stroke s s)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) t)).
    exact (ax_mp (ax_luk p q r s) S1).
Qed.

Theorem scharle3 : forall (p q r s t u : Prop), (stroke (stroke u (stroke (stroke p (stroke q r)) t)) (stroke (stroke (stroke t (stroke s (stroke s s))) u) (stroke (stroke t (stroke s (stroke s s))) u))).
Proof.
    intros.
    pose (S1 := (ax_luk (stroke t (stroke s (stroke s s))) (stroke (stroke p (stroke q r)) t) (stroke (stroke p (stroke q r)) t) u)).
    exact (ax_mp (scharle2 p q r s t) S1).
Qed.

Theorem scharle4 : forall (p q r s t : Prop), (stroke (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))) (stroke p (stroke q r))).
Proof.
    intros.
    pose (S1 := (scharle3 s s s t (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke p (stroke q r)))).
    exact (ax_mp (ax_luk p q r s) S1).
Qed.

Theorem scharle5 : forall (p q r s t : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s t) (stroke (stroke t s) (stroke t s))) (stroke t (stroke t t)))).
Proof.
    intros.
    pose (S1 := (scharle2 p q r t (stroke (stroke (stroke s t) (stroke (stroke t s) (stroke t s))) (stroke t (stroke t t))))).
    exact (ax_mp (scharle4 t t t s t) S1).
Qed.

Theorem scharle6 : forall (t : Prop), (stroke t (stroke t t)).
Proof.
    intros.
    pose (S1 := (scharle5 (stroke t (stroke t t)) (stroke (stroke t t) (stroke (stroke t t) (stroke t t))) (stroke t (stroke t t)) t t)).
    exact (ax_mp (scharle5 t t t t t) S1).
Qed.

Theorem scharle7 : forall (s t : Prop), (stroke (stroke s t) (stroke (stroke t s) (stroke t s))).
Proof.
    intros.
    pose (S1 := (ax_luk t t t s)).
    exact (ax_mp (scharle6 t) S1).
Qed.

Theorem scharle8 : forall (t : Prop), (stroke (stroke t t) t).
Proof.
    intros.
    pose (S1 := (scharle7 t (stroke t t))).
    exact (ax_mp (scharle6 t) S1).
Qed.

Theorem scharle9 : forall (s t : Prop), (stroke (stroke (stroke t s) (stroke t s)) (stroke s t)).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke s t) (stroke (stroke t s) (stroke t s)))).
    exact (ax_mp (scharle7 s t) S1).
Qed.

Theorem scharle10 : forall (p s t : Prop), (stroke (stroke p s) (stroke (stroke (stroke (stroke t s) (stroke t s)) p) (stroke (stroke (stroke t s) (stroke t s)) p))).
Proof.
    intros.
    pose (S1 := (ax_luk (stroke (stroke t s) (stroke t s)) s t p)).
    exact (ax_mp (scharle9 s t) S1).
Qed.

Theorem scharle11 : forall (p s : Prop), (stroke (stroke (stroke s p) (stroke s p)) (stroke p p)).
Proof.
    intros.
    pose (S1 := (scharle10 (stroke p p) p s)).
    exact (ax_mp (scharle8 p) S1).
Qed.

Theorem scharle12 : forall (p s : Prop), (stroke (stroke p p) (stroke (stroke s p) (stroke s p))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke s p) (stroke s p)) (stroke p p))).
    exact (ax_mp (scharle11 p s) S1).
Qed.

Theorem scharle13 : forall (p s r : Prop), (stroke (stroke r (stroke s p)) (stroke (stroke (stroke p p) r) (stroke (stroke p p) r))).
Proof.
    intros.
    pose (S1 := (ax_luk (stroke p p) (stroke s p) (stroke s p) r)).
    exact (ax_mp (scharle12 p s) S1).
Qed.

Theorem scharle14 : forall (p q r s : Prop), (stroke (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r))).
Proof.
    intros.
    pose (S1 := (scharle13 (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke s (stroke s s)) (stroke p (stroke q r)))).
    exact (ax_mp (ax_luk p q r s) S1).
Qed.

Theorem scharle15 : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r)))).
    exact (ax_mp (scharle14 p q r s) S1).
Qed.

Theorem scharle16 : forall (p s t : Prop), (stroke (stroke p (stroke t s)) (stroke (stroke (stroke s t) p) (stroke (stroke s t) p))).
Proof.
    intros.
    pose (S1 := (scharle15 (stroke s t) (stroke t s) (stroke t s) p)).
    exact (ax_mp (scharle7 s t) S1).
Qed.

Theorem scharle17 : forall (p s t : Prop), (stroke (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)) (stroke p (stroke t s))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke p (stroke t s)) (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)))).
    exact (ax_mp (scharle16 p s t) S1).
Qed.

Theorem scharle18 : forall (p s t : Prop), (stroke (stroke (stroke t s) p) (stroke (stroke (stroke s t) p) (stroke (stroke s t) p))).
Proof.
    intros.
    pose (S1 := (scharle16 (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)) (stroke t s) p)).
    exact (ax_mp (scharle17 p s t) S1).
Qed.

Theorem scharle19 : forall (p s t : Prop), (stroke (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)) (stroke (stroke t s) p)).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke t s) p) (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)))).
    exact (ax_mp (scharle18 p s t) S1).
Qed.

Theorem scharle20 : forall (p q r s t : Prop), (stroke (stroke t (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke (stroke (stroke p (stroke q r)) t) (stroke (stroke p (stroke q r)) t))).
Proof.
    intros.
    pose (S1 := (scharle15 (stroke p (stroke q r)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) t)).
    exact (ax_mp (scharle15 p q r s) S1).
Qed.

Theorem scharle21 : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))).
Proof.
    intros.
    pose (S1 := (scharle20 p q r s (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s)))))).
    exact (ax_mp (scharle19 (stroke (stroke p s) (stroke p s)) q s) S1).
Qed.

Theorem scharle22 : forall (p s t : Prop), (stroke (stroke p s) (stroke (stroke (stroke (stroke t s) (stroke t s)) p) (stroke (stroke (stroke t s) (stroke t s)) p))).
Proof.
    intros.
    pose (S1 := (ax_luk (stroke (stroke t s) (stroke t s)) s t p)).
    exact (ax_mp (scharle9 s t) S1).
Qed.

Theorem scharle23 : forall (p t : Prop), (stroke (stroke (stroke t (stroke p p)) (stroke t (stroke p p))) p).
Proof.
    intros.
    pose (S1 := (scharle22 p (stroke p p) t)).
    exact (ax_mp (scharle6 p) S1).
Qed.

Theorem scharle24 : forall (p t : Prop), (stroke p (stroke (stroke t (stroke p p)) (stroke t (stroke p p)))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke t (stroke p p)) (stroke t (stroke p p))) p)).
    exact (ax_mp (scharle23 p t) S1).
Qed.

Theorem scharle25 : forall (p q s t : Prop), (stroke (stroke q (stroke (stroke s t) p)) (stroke (stroke (stroke (stroke t s) p) q) (stroke (stroke (stroke t s) p) q))).
Proof.
    intros.
    pose (S1 := (ax_luk (stroke (stroke t s) p) (stroke (stroke s t) p) (stroke (stroke s t) p) q)).
    exact (ax_mp (scharle18 p s t) S1).
Qed.

Theorem scharle26 : forall (p s t : Prop), (stroke (stroke (stroke p (stroke s t)) (stroke (stroke s t) p)) (stroke p (stroke t s))).
Proof.
    intros.
    pose (S1 := (scharle25 (stroke (stroke s t) p) (stroke p (stroke t s)) (stroke s t) p)).
    exact (ax_mp (scharle16 p s t) S1).
Qed.

Theorem scharle27 : forall (p s t : Prop), (stroke (stroke p (stroke t s)) (stroke (stroke p (stroke s t)) (stroke (stroke s t) p))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke p (stroke s t)) (stroke (stroke s t) p)) (stroke p (stroke t s)))).
    exact (ax_mp (scharle26 p s t) S1).
Qed.

Theorem scharle28 : forall (p q s t : Prop), (stroke (stroke (stroke p (stroke s t)) q) (stroke (stroke (stroke p (stroke t s)) q) (stroke (stroke p (stroke t s)) q))).
Proof.
    intros.
    pose (S1 := (scharle21 (stroke p (stroke t s)) (stroke p (stroke s t)) (stroke (stroke s t) p) q)).
    exact (ax_mp (scharle27 p s t) S1).
Qed.

Theorem scharle29 : forall (p q s t : Prop), (stroke (stroke (stroke t s) (stroke q p)) (stroke (stroke (stroke s t) (stroke p q)) (stroke (stroke s t) (stroke p q)))).
Proof.
    intros.
    pose (S1 := (scharle28 (stroke t s) (stroke (stroke (stroke s t) (stroke p q)) (stroke (stroke s t) (stroke p q))) p q)).
    exact (ax_mp (scharle18 (stroke p q) s t) S1).
Qed.

Theorem scharle30 : forall (p q r s t : Prop), (stroke (stroke r (stroke (stroke s t) (stroke p q))) (stroke (stroke (stroke (stroke t s) (stroke q p)) r) (stroke (stroke (stroke t s) (stroke q p)) r))).
Proof.
    intros.
    pose (S1 := (ax_luk (stroke (stroke t s) (stroke q p)) (stroke (stroke s t) (stroke p q)) (stroke (stroke s t) (stroke p q)) r)).
    exact (ax_mp (scharle29 p q s t) S1).
Qed.

Theorem scharle31 : forall (p s : Prop), (stroke (stroke (stroke (stroke p p) s) (stroke (stroke p p) s)) p).
Proof.
    intros.
    pose (S1 := (scharle30 s (stroke p p) p s (stroke p p))).
    exact (ax_mp (scharle24 p s) S1).
Qed.

Theorem scharle32 : forall (p s : Prop), (stroke p (stroke (stroke (stroke p p) s) (stroke (stroke p p) s))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke (stroke p p) s) (stroke (stroke p p) s)) p)).
    exact (ax_mp (scharle31 p s) S1).
Qed.

Theorem nicod_assoc : forall (p q r : Prop), (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))).
Proof.
    assert (L : forall (p q : Prop), (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))).
    {
        intros.
        pose (L1 := (scharle21 p q q p)).
        pose (S1 := (scharle24 q p)).
        pose (S2 := (scharle21 q (stroke p (stroke q q)) (stroke p (stroke q q)) (stroke (stroke (stroke q p) (stroke (stroke p p) (stroke p p))) (stroke (stroke q p) (stroke (stroke p p) (stroke p p)))))).
        pose (S3 := (ax_mp S1 S2)).
        pose (L2 := (ax_mp L1 S3)).
        pose (L3 := (scharle21 (stroke q p) (stroke p p) (stroke p p) p)).
        pose (S4 := (scharle24 (stroke (stroke p p) p) q)).
        pose (L4 := (ax_mp (scharle8 p) S4)).
        pose (S5 := (scharle21 q (stroke (stroke p p) p) (stroke (stroke p p) p) (stroke (stroke (stroke q p ) p) (stroke (stroke q p ) p)))).
        pose (S6 := (ax_mp L4 S5)).
        pose (S7 := (scharle21 (stroke (stroke q p) (stroke (stroke p p) (stroke p p))) (stroke (stroke (stroke p p) p) (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke (stroke (stroke p p) p) (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))))).
        pose (S8 := (ax_mp L3 S7)).
        pose (S9 := (ax_mp S6 S8)).
        pose (S10 := (scharle21 q (stroke (stroke q p) (stroke (stroke p p) (stroke p p))) (stroke (stroke q p) (stroke (stroke p p) (stroke p p))) (stroke (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))))).
        pose (S11 := (ax_mp L2 S10)).
        pose (LA := (ax_mp S9 S11)).
        pose (S12 := (scharle12 q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))).
        pose (S13 := (scharle21 (stroke q q) (stroke (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)) q) (stroke (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)) q) (stroke (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))))).
        pose (S14 := (ax_mp S12 S13)).
        pose (S15 := (ax_mp (scharle7 (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)) q) S14)).
        pose (LB := (ax_mp S15 (scharle7 (stroke q q) (stroke (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))))))).
        pose (S16 := (scharle21 (stroke (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))) q q (stroke (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))))).
        pose (S17 := (ax_mp LB S16)).
        pose (S18 := (ax_mp LA S17)).
        exact (ax_mp S18 (scharle8 (stroke (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p))) (stroke q (stroke (stroke (stroke q p) p) (stroke (stroke q p) p)))))).
    }
    intros.
    pose (S1 := (scharle21 q (stroke (stroke q r) r) (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r)))).
    pose (S2 := (ax_mp (L r q) S1)).
    pose (S3 := (scharle21 p (stroke q r) (stroke q r) r)).
    pose (S4 := (scharle21 (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r)))))).
    pose (S5 := (ax_mp S3 S4)).
    exact (ax_mp S2 S5).
Qed.

Theorem nicod_sum : forall (p q r : Prop), (stroke (stroke q (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))).
Proof.
    intros.
    pose (S1 := (nicod_assoc (stroke (stroke p p) (stroke q q)) (stroke q (stroke r r)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r))))).
    pose (S2 := (scharle21 (stroke p p) q q (stroke r r))).
    exact (ax_mp S2 S1).
Qed.

Definition not := fun (p : Prop) => (stroke p p).
Definition or := fun (p q : Prop) => (stroke (stroke p p) (stroke q q)).
Definition impl := fun (p q : Prop) => (or (not p) q).

Theorem mp : forall {p q : Prop} (min : p) (maj : (impl p q)), q.
Proof.
    intros.
    pose (S1 := (scharle24 p (stroke p p))).
    pose (S2 := (ax_mp min S1)).
    exact (ax_mp S2 maj).
Qed.
