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

Theorem pm1_1 : forall {p q : Prop} (min : p) (maj : (impl p q)), q.
Proof.
    intros.
    pose (S1 := (scharle24 p (stroke p p))).
    pose (S2 := (ax_mp min S1)).
    exact (ax_mp S2 maj).
Qed.

Theorem mp : forall {p q : Prop} (min : p) (maj : (impl p q)), q.
Proof.
    intros.
    exact (pm1_1 min maj).
Qed.

Theorem pm1_2 : forall (p : Prop), (impl (or p p) p).
Proof.
    intros.
    pose (S1 := (scharle8 (stroke (or p p) (or p p)))).
    pose (S2 := (scharle8 (stroke p p))).
    pose (S3 := (scharle21 (stroke (stroke (or p p) (or p p)) (stroke (or p p) (or p p))) (or p p) (or p p) (stroke p p))).
    pose (S4 := (ax_mp S1 S3)).
    exact (ax_mp S2 S4).
Qed.

Theorem pm_taut : forall (p : Prop), (impl (or p p) p).
Proof.
    intros.
    exact (pm1_2 p).
Qed.

Theorem pm1_3 : forall (p q : Prop), (impl q (or p q)).
Proof.
    intros.
    pose (S1 := (scharle24 q (stroke p p))).
    pose (S2 := (scharle8 (stroke q q))).
    pose (S3 := (scharle21 (stroke (stroke q q) (stroke q q)) q q (stroke (or p q) (or p q)))).
    pose (S4 := (ax_mp S2 S3)).
    exact (ax_mp S1 S4).
Qed.

Theorem pm_add : forall (p q : Prop), (impl q (or p q)).
Proof.
    intros.
    exact (pm1_3 p q).
Qed.

Theorem orir : forall (p q : Prop), (impl q (or p q)).
Proof.
    intros.
    exact (pm_add p q).
Qed.

Theorem oriri : forall (p : Prop) {q : Prop} (H : q), (or p q).
Proof.
    intros.
    exact (mp H (orir p q)).
Qed.

Theorem pm1_4 : forall (p q : Prop), (impl (or p q) (or q p)).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke p p) (stroke q q))).
    pose (S2 := (scharle8 (stroke (or p q) (or p q)))).
    pose (S3 := (scharle21 (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (or p q) (or p q) (stroke (or q p) (or q p)))).
    pose (S4 := (ax_mp S2 S3)).
    exact (ax_mp S1 S4).
Qed.

Theorem pm_perm : forall (p q : Prop), (impl (or p q) (or q p)).
Proof.
    intros.
    exact (pm1_4 p q).
Qed.

Theorem or_comm : forall (p q : Prop), (impl (or p q) (or q p)).
Proof.
    intros.
    exact (pm_perm p q).
Qed.

Theorem or_commi : forall {p q : Prop} (H : (or p q)), (or q p).
Proof.
    intros.
    exact (mp H (or_comm p q)).
Qed.

Theorem pm1_5 : forall (p q r : Prop), (impl (or p (or q r)) (or q (or p r))).
Proof.
    intros.
    pose (S1 := (nicod_assoc (stroke p p) (stroke q q) (stroke r r))).
    pose (S2 := (scharle8 (stroke (or p (or q r)) (or p (or q r))))).
    pose (S3 := (scharle21 (stroke (stroke (or p (or q r)) (or p (or q r))) (stroke (or p (or q r)) (or p (or q r)))) (or p (or q r)) (or p (or q r)) (stroke (or q (or p r)) (or q (or p r))))).
    pose (S4 := (ax_mp S2 S3)).
    exact (ax_mp S1 S4).
Qed.

Theorem pm_assoc : forall (p q r : Prop), (impl (or p (or q r)) (or q (or p r))).
Proof.
    intros.
    exact (pm1_5 p q r).
Qed.

Theorem pm1_6 : forall (p q r : Prop), (impl (impl q r) (impl (or p q) (or p r))).
Proof.
    intros.
    pose (S1 := (nicod_sum p q r)).
    pose (S2 := (scharle8 (stroke (or p q) (or p q)))).
    pose (S3 := (scharle21 (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (or p q) (or p q) (stroke (or p r) (or p r)))).
    pose (S4 := (ax_mp S2 S3)).
    pose (S5 := (scharle21 (stroke q (stroke r r)) (stroke (or p q) (stroke (or p r) (or p r))) (stroke (or p q) (stroke (or p r) (or p r))) (stroke (impl (or p q) (or p r)) (impl (or p q) (or p r))))).
    pose (S6 := (ax_mp S1 S5)).
    pose (S7 := (ax_mp S4 S6)).
    pose (S8 := (scharle24 q (stroke q q))).
    pose (S9 := (scharle21 q (stroke (stroke q q) (stroke q q)) (stroke (stroke q q) (stroke q q)) (stroke r r))).
    pose (S10 := (ax_mp S8 S9)).
    pose (S11 := (scharle21 (impl q r) (stroke q (stroke r r)) (stroke q (stroke r r)) (stroke (impl (or p q) (or p r)) (impl (or p q) (or p r))))).
    pose (S12 := (ax_mp S10 S11)).
    pose (S13 := (ax_mp S7 S12)).
    pose (S14 := (scharle8 (stroke (impl q r) (impl q r)))).
    pose (S15 := (scharle21 (stroke (stroke (impl q r) (impl q r)) (stroke (impl q r) (impl q r))) (impl q r) (impl q r) (stroke (impl (or p q) (or p r)) (impl (or p q) (or p r))))).
    pose (S16 := (ax_mp S14 S15)).
    exact (ax_mp S13 S16).
Qed.

Theorem pm_sum : forall (p q r : Prop), (impl (impl q r) (impl (or p q) (or p r))).
Proof.
    intros.
    exact (pm1_6 p q r).
Qed.

Theorem or_subr : forall {p q : Prop} (H0 : (impl p q)) (r : Prop), (impl (or r p) (or r q)).
Proof.
    intros.
    exact (mp H0 (pm_sum r p q)).
Qed.

Theorem or_subri : forall {p q r : Prop} (H0 : (or r p)) (H1 : (impl p q)), (or r q).
Proof.
    intros.
    exact (mp H0 (or_subr H1 r)).
Qed.

Theorem pm2_01 : forall (p : Prop), (impl (impl p (not p)) (not p)).
Proof.
    intros.
    exact (pm_taut (not p)).
Qed.

Theorem pm2_02 : forall (p q : Prop), (impl q (impl p q)).
Proof.
    intros.
    exact (pm_add (not p) q).
Qed.

Theorem implir : forall (p q : Prop), (impl q (impl p q)).
Proof.
    intros.
    exact (pm2_02 p q).
Qed.

Theorem impliri : forall (p : Prop) {q : Prop} (H : q), (impl p q).
Proof.
    intros.
    exact (mp H (implir p q)).
Qed.

Theorem pm2_03 : forall (p q : Prop), (impl (impl p (not q)) (impl q (not p))).
Proof.
    intros.
    exact (pm_perm (not p) (not q)).
Qed.

Theorem pm_transp1 : forall (p q : Prop), (impl (impl p (not q)) (impl q (not p))).
Proof.
    intros.
    exact (pm2_03 p q).
Qed.

Theorem pm2_04 : forall (p q r : Prop), (impl (impl p (impl q r)) (impl q (impl p r))).
Proof.
    intros.
    exact (pm_assoc (not p) (not q) r).
Qed.

Theorem pm_comm : forall (p q r : Prop), (impl (impl p (impl q r)) (impl q (impl p r))).
Proof.
    intros.
    exact (pm2_04 p q r).
Qed.

Theorem pm2_05 : forall (p q r : Prop), (impl (impl q r) (impl (impl p q) (impl p r))).
Proof.
    intros.
    exact (pm_sum (not p) q r).
Qed.

Theorem pm_syll2 : forall (p q r : Prop), (impl (impl q r) (impl (impl p q) (impl p r))).
Proof.
    intros.
    exact (pm2_05 p q r).
Qed.

Theorem impl_subr : forall {p q : Prop} (H : (impl p q)) (r : Prop), (impl (impl r p) (impl r q)).
Proof.
    intros.
    exact (mp H (pm_syll2 r p q)).
Qed.

Theorem impl_subri : forall {p q r : Prop} (H0 : (impl p q)) (H1 : (impl r p)), (impl r q).
Proof.
    intros.
    exact (mp H1 (impl_subr H0 r)).
Qed.

Theorem pm2_06 : forall (p q r : Prop), (impl (impl p q) (impl (impl q r) (impl p r))).
Proof.
    intros.
    pose (S1 := (pm_comm (impl q r) (impl p q) (impl p r))).
    pose (S2 := (pm2_05 p q r)).
    exact (mp S2 S1).
Qed.

Theorem pm_syll : forall (p q r : Prop), (impl (impl p q) (impl (impl q r) (impl p r))).
Proof.
    intros.
    exact (pm2_06 p q r).
Qed.

Theorem impl_subl : forall {p q : Prop} (H : (impl q p)) (r : Prop), (impl (impl p r) (impl q r)).
Proof.
    intros.
    exact (mp H (pm_syll q p r)).
Qed.

Theorem impl_subli : forall {p q r : Prop} (H0 : (impl q p)) (H1 : (impl p r)), (impl q r).
Proof.
    intros.
    exact (mp H1 (impl_subl H0 r)).
Qed.

Theorem syll : forall {p q r : Prop} (H0 : (impl p q)) (H1 : (impl q r)), (impl p r).
Proof.
    intros.
    pose (S1 := (pm2_06 p q r)).
    pose (S2 := (mp H0 S1)).
    exact (mp H1 S2).
Qed.

Theorem pm2_07 : forall (p : Prop), (impl p (or p p)).
Proof.
    intros.
    exact (pm1_3 p p).
Qed.

Theorem pm2_08 : forall (p : Prop), (impl p p).
Proof.
    intros.
    pose (S1 := (pm2_05 p (or p p) p)).
    pose (S2 := (pm_taut p)).
    pose (S3 := (mp S2 S1)).
    pose (S4 := (pm2_07 p)).
    exact (mp S4 S3).
Qed.

Theorem pm_id : forall (p : Prop), (impl p p).
Proof.
    intros.
    exact (pm2_08 p).
Qed.

Theorem id : forall (p : Prop), (impl p p).
Proof.
    intros.
    exact (pm_id p).
Qed.

Theorem pm2_1 : forall (p : Prop), (or (not p) p).
Proof.
    intros.
    exact (pm2_08 p).
Qed.

Theorem pm2_11 : forall (p : Prop), (or p (not p)).
Proof.
    intros.
    pose (S1 := (pm_perm (not p) p)).
    exact (mp (pm2_1 p) S1).
Qed.

Theorem ex_mid : forall (p : Prop), (or p (not p)).
Proof.
    intros.
    exact (pm2_11 p).
Qed.

Theorem pm2_12 : forall (p : Prop), (impl p (not (not p))).
Proof.
    intros.
    exact (pm2_11 (not p)).
Qed.

Theorem notdi : forall (p : Prop), (impl p (not (not p))).
Proof.
    intros.
    exact (pm2_12 p).
Qed.

Theorem notdii : forall {p : Prop} (H : p), (not (not p)).
Proof.
    intros.
    exact (mp H (notdi p)).
Qed.

Theorem pm2_13 : forall (p : Prop), (or p (not (not (not p)))).
Proof.
    intros.
    pose (S1 := (pm_sum p (not p) (not (not (not p))))).
    pose (S2 := (pm2_12 (not p))).
    pose (S3 := (mp S2 S1)).
    exact (mp (pm2_11 p) S3).
Qed.

Theorem pm2_14 : forall (p : Prop), (impl (not (not p)) p).
Proof.
    intros.
    pose (S1 := (pm_perm p (not (not (not p))))).
    exact (mp (pm2_13 p) S1).
Qed.

Theorem notde : forall (p : Prop), (impl (not (not p)) p).
Proof.
    intros.
    exact (pm2_14 p).
Qed.

Theorem notdei : forall {p : Prop} (H : (not (not p))), p.
Proof.
    intros.
    exact (mp H (notde p)).
Qed.

Theorem pm2_15 : forall (p q : Prop), (impl (impl (not p) q) (impl (not q) p)).
Proof.
    intros.
    pose (S1 := (pm2_05 (not p) q (not (not q)))).
    pose (S2 := (pm2_12 q)).
    pose (S3 := (mp S2 S1)).
    pose (S4 := (pm2_03 (not p) (not q))).
    pose (S5 := (pm2_05 (not q) (not (not p)) p)).
    pose (S6 := (mp (pm2_14 p) S5)).
    pose (S7 := (pm2_05 (impl (not p) q) (impl (not p) (not (not q))) (impl (not q) (not (not p))))).
    pose (S8 := (mp S4 S7)).
    pose (S9 := (mp S3 S8)).
    pose (S10 := (pm2_05 (impl (not p) q) (impl (not q) (not (not p))) (impl (not q) p))).
    pose (S11 := (mp S6 S10)).
    exact (mp S9 S11).
Qed.

Theorem pm_transp2 : forall (p q : Prop), (impl (impl (not p) q) (impl (not q) p)).
Proof.
    intros.
    exact (pm2_15 p q).
Qed.

Theorem pm2_16 : forall (p q : Prop), (impl (impl p q) (impl (not q) (not p))).
Proof.
    intros.
    pose (S1 := (pm2_12 q)).
    pose (S2 := (mp S1 (pm2_05 p q (not (not q))))).
    pose (S3 := (pm2_03 p (not q))).
    exact (syll S2 S3).
Qed.

Theorem not_sub : forall {p q : Prop} (H : (impl q p)), (impl (not p) (not q)).
Proof.
    intros.
    exact (mp H (pm2_16 q p)).
Qed.

Theorem not_subi : forall {p q : Prop} (H0 : (not p)) (H1 : (impl q p)), (not q).
Proof.
    intros.
    exact (mp H0 (not_sub H1)).
Qed.

Theorem pm_transp0 : forall (p q : Prop), (impl (impl p q) (impl (not q) (not p))).
Proof.
    intros.
    exact (pm2_16 p q).
Qed.

Theorem pm2_17 : forall (p q : Prop), (impl (impl (not q) (not p)) (impl p q)).
Proof.
    intros.
    pose (S1 := (pm2_03 (not q) p)).
    pose (S2 := (pm2_14 q)).
    pose (S3 := (mp S2 (pm2_05 p (not (not q)) q))).
    exact (syll S1 S3).
Qed.

Theorem pm_transp3 : forall (p q : Prop), (impl (impl (not p) (not q)) (impl q p)).
Proof.
    intros.
    exact (pm2_17 q p).
Qed.

Theorem pm2_18 : forall (p : Prop), (impl (impl (not p) p) p).
Proof.
    intros.
    pose (S1 := pm2_12 p).
    pose (S2 := (mp S1 (pm2_05 (not p) p (not (not p))))).
    pose (S3 := (pm2_01 (not p))).
    pose (S4 := (syll S2 S3)).
    pose (S5 := (pm2_14 p)).
    exact (syll S4 S5).
Qed.

Theorem pm2_2 : forall (p q : Prop), (impl p (or p q)).
Proof.
    intros.
    pose (S1 := (pm_add q p)).
    pose (S2 := (pm_perm q p)).
    exact (syll S1 S2).
Qed.

Theorem oril : forall (p q : Prop), (impl p (or p q)).
Proof.
    intros.
    exact (pm2_2 p q).
Qed.

Theorem orili : forall {p : Prop} (H : p) (q : Prop), (or p q).
Proof.
    intros.
    exact (mp H (oril p q)).
Qed.

Theorem pm2_21 : forall (p q : Prop), (impl (not p) (impl p q)).
Proof.
    intros.
    exact (pm2_2 (not p) q).
Qed.

Theorem implil : forall (p q : Prop), (impl (not p) (impl p q)).
Proof.
    intros.
    exact (pm2_21 p q).
Qed.

Theorem implili : forall {p : Prop} (H : (not p)) (q : Prop), (impl p q).
Proof.
    intros.
    exact (mp H (implil p q)).
Qed.

Theorem pm2_24 : forall (p q : Prop), (impl p (impl (not p) q)).
Proof.
    intros.
    exact (mp (pm2_21 p q) (pm_comm (not p) p q)).
Qed.

Theorem pm2_25 : forall (p q : Prop), (or p (impl (or p q) q)).
Proof.
    intros.
    pose (S1 := (pm2_1 (or p q))).
    exact (mp S1 (pm_assoc (not (or p q)) p q)).
Qed.

Theorem pm2_26 : forall (p q : Prop), (or (not p) (impl (impl p q) q)).
Proof.
    intros.
    exact (pm2_25 (not p) q).
Qed.

Theorem pm2_27 : forall (p q : Prop), (impl p (impl (impl p q) q)).
Proof.
    intros.
    exact (pm2_26 p q).
Qed.

Theorem pm2_3 : forall (p q r : Prop), (impl (or p (or q r)) (or p (or r q))).
Proof.
    intros.
    pose (S1 := (pm_perm q r)).
    exact (mp S1 (pm_sum p (or q r) (or r q))).
Qed.

Theorem pm2_31 : forall (p q r : Prop), (impl (or p (or q r)) (or (or p q) r)).
Proof.
    intros.
    pose (S1 := (pm2_3 p q r)).
    pose (S2 := (syll S1 (pm_assoc p r q))).
    exact (syll S2 (pm_perm r (or p q))).
Qed.

Theorem or_assoc2 : forall (p q r : Prop), (impl (or p (or q r)) (or (or p q) r)).
Proof.
    intros.
    exact (pm2_31 p q r).
Qed.

Theorem or_associ2 : forall {p q r : Prop} (H : (or p (or q r))), (or (or p q) r).
Proof.
    intros.
    exact (mp H (or_assoc2 p q r)).
Qed.

Theorem pm2_32 : forall (p q r : Prop), (impl (or (or p q) r) (or p (or q r))).
Proof.
    intros.
    pose (S1 := (pm_perm (or p q) r)).
    pose (S2 := (syll S1 (pm_assoc r p q))).
    exact (syll S2 (pm2_3 p r q)).
Qed.

Theorem or_assoc : forall (p q r : Prop), (impl (or (or p q) r) (or p (or q r))).
Proof.
    intros.
    exact (pm2_32 p q r).
Qed.

Theorem or_associ : forall {p q r : Prop} (H : (or (or p q) r)), (or p (or q r)).
Proof.
    intros.
    exact (mp H (or_assoc p q r)).
Qed.

Definition or3 := fun (p q r : Prop) => (or (or p q) r).

Theorem pm2_36 : forall (p q r : Prop), (impl (impl q r) (impl (or p q) (or r p))).
Proof.
    intros.
    pose (S1 := (pm_perm p r)).
    pose (S2 := (mp S1 (pm_syll2 (or p q) (or p r) (or r p)))).
    pose (S3 := (pm_sum p q r)).
    exact (syll S3 S2).
Qed.

Theorem pm2_37 : forall (p q r : Prop), (impl (impl q r) (impl (or q p) (or p r))).
Proof.
    intros.
    pose (S1 := (pm_perm q p)).
    pose (S2 := (mp S1 (pm_syll (or q p) (or p q) (or p r)))).
    pose (S3 := (pm_sum p q r)).
    exact (syll S3 S2).
Qed.

Theorem pm2_38 : forall (p q r : Prop), (impl (impl q r) (impl (or q p) (or r p))).
Proof.
    intros.
    pose (S1 := (pm_perm q p)).
    pose (S2 := (mp S1 (pm_syll (or q p) (or p q) (or r p)))).
    pose (S3 := (pm2_36 p q r)).
    exact (syll S3 S2).
Qed.

Theorem or_subl : forall {p q : Prop} (H : (impl p q)) (r : Prop), (impl (or p r) (or q r)).
Proof.
    intros.
    exact (mp H (pm2_38 r p q)).
Qed.

Theorem or_subli : forall {p q r : Prop} (H0 : (or q p)) (H1 : (impl q r)), (or r p).
Proof.
    intros.
    exact (mp H0 (or_subl H1 p)).
Qed.

Theorem pm2_4 : forall (p q : Prop), (impl (or p (or p q)) (or p q)).
Proof.
    intros.
    pose (S1 := (pm2_31 p p q)).
    exact (syll S1 (mp (pm_taut p) (pm2_38 q (or p p) p))).
Qed.

Theorem pm2_41 : forall (p q : Prop), (impl (or q (or p q)) (or p q)).
Proof.
    intros.
    pose (S1 := (pm_assoc q p q)).
    exact (syll S1 (mp (pm_taut q) (pm_sum p (or q q) q))).
Qed.

Theorem pm2_42 : forall (p q : Prop), (impl (or (not p) (impl p q)) (impl p q)).
Proof.
    intros.
    exact (pm2_4 (not p) q).
Qed.

Theorem pm2_43 : forall (p q : Prop), (impl (impl p (impl p q)) (impl p q)).
Proof.
    intros.
    exact (pm2_42 p q).
Qed.

Theorem pm2_45 : forall (p q : Prop), (impl (not (or p q)) (not p)).
Proof.
    intros.
    exact (mp (pm2_2 p q) (pm_transp0 p (or p q))).
Qed.

Theorem pm2_46 : forall (p q : Prop), (impl (not (or p q)) (not q)).
Proof.
    intros.
    exact (mp (pm1_3 p q) (pm_transp0 q (or p q))).
Qed.

Theorem pm2_47 : forall (p q : Prop), (impl (not (or p q)) (or (not p) q)).
Proof.
    intros.
    exact (syll (pm2_45 p q) (pm2_2 (not p) q)).
Qed.

Theorem pm2_48 : forall (p q : Prop), (impl (not (or p q)) (or p (not q))).
Proof.
    intros.
    exact (syll (pm2_46 p q) (pm1_3 p (not q))).
Qed.

Theorem pm2_49 : forall (p q : Prop), (impl (not (or p q)) (or (not p) (not q))).
Proof.
    intros.
    exact (syll (pm2_45 p q) (pm2_2 (not p) (not q))).
Qed.

Theorem pm2_5 : forall (p q : Prop), (impl (not (impl p q)) (impl (not p) q)).
Proof.
    intros.
    exact (pm2_47 (not p) q).
Qed.

Theorem pm2_51 : forall (p q : Prop), (impl (not (impl p q)) (impl p (not q))).
Proof.
    intros.
    exact (pm2_48 (not p) q).
Qed.

Theorem pm2_52 : forall (p q : Prop), (impl (not (impl p q)) (impl (not p) (not q))).
Proof.
    intros.
    exact (pm2_49 (not p) q).
Qed.

Theorem pm2_521 : forall (p q : Prop), (impl (not (impl p q)) (impl q p)).
Proof.
    intros.
    exact (syll (pm2_52 p q) (pm2_17 q p)).
Qed.

Theorem pm2_53 : forall (p q : Prop), (impl (or p q) (impl (not p) q)).
Proof.
    intros.
    exact (mp (pm2_12 p) (pm2_38 q p (not (not p)))).
Qed.

Theorem pm2_54 : forall (p q : Prop), (impl (impl (not p) q) (or p q)).
Proof.
    intros.
    exact (mp (pm2_14 p) (pm2_38 q (not (not p)) p)).
Qed.

Theorem pm2_55 : forall (p q : Prop), (impl (not p) (impl (or p q) q)).
Proof.
    intros.
    exact (mp (pm2_53 p q) (pm_comm (or p q) (not p) q)).
Qed.

Theorem pm2_56 : forall (p q : Prop), (impl (not q) (impl (or p q) p)).
Proof.
    intros.
    exact (syll (pm2_55 q p) (impl_subl (pm_perm p q) p)).
Qed.

Theorem pm2_6 : forall (p q : Prop), (impl (impl (not p) q) (impl (impl p q) q)).
Proof.
    intros.
    pose (S1 := (pm2_38 q (not p) q)).
    pose (S2 := (mp (pm_taut q) (pm_syll2 (or (not p) q) (or q q) q))).
    exact (syll S1 S2).
Qed.

Theorem pm2_61 : forall (p q : Prop), (impl (impl p q) (impl (impl (not p) q) q)).
Proof.
    intros.
    exact (mp (pm2_6 p q) (pm_comm (impl (not p) q) (impl p q) q)).
Qed.

Theorem pm2_62 : forall (p q : Prop), (impl (or p q) (impl (impl p q) q)).
Proof.
    intros.
    exact (syll (pm2_53 p q) (pm2_6 p q)).
Qed.

Theorem pm2_621 : forall (p q : Prop), (impl (impl p q) (impl (or p q) q)).
Proof.
    intros.
    exact (mp (pm2_62 p q) (pm_comm (or p q) (impl p q) q)).
Qed.

Theorem pm2_63 : forall (p q : Prop), (impl (or p q) (impl (impl p q) q)).
Proof.
    intros.
    exact (pm2_62 p q).
Qed.

Theorem pm2_64 : forall (p q : Prop), (impl (or p q) (impl (or p (not q)) p)).
Proof.
    intros.
    exact (syll (syll (pm_perm p q) (pm2_63 q p)) (impl_subl (pm_perm p (not q)) p)).
Qed.

Theorem pm2_65 : forall (p q : Prop), (impl (impl p q) (impl (impl p (not q)) (not p))).
Proof.
    intros.
    exact (pm2_64 (not p) q).
Qed.

Theorem pm2_67 : forall (p q : Prop), (impl (impl (or p q) q) (impl p q)).
Proof.
    intros.
    pose (S1 := (mp (pm2_54 p q) (pm_syll (impl (not p) q) (or p q) q))).
    pose (S2 := (mp (pm2_24 p q) (pm_syll p (impl (not p) q) q))).
    exact (syll S1 S2).
Qed.

Theorem pm2_68 : forall (p q : Prop), (impl (impl (impl p q) q) (or p q)).
Proof.
    intros.
    pose (S1 := (pm2_67 (not p) q)).
    exact (syll S1 (pm2_54 p q)).
Qed.

Theorem pm2_69 : forall (p q : Prop), (impl (impl (impl p q) q) (impl (impl q p) p)).
Proof.
    intros.
    exact (syll (syll (pm2_68 p q) (pm_perm p q)) (pm2_62 q p)).
Qed.

Theorem pm2_73 : forall (p q r : Prop), (impl (impl p q) (impl (or3 p q r) (or q r))).
Proof.
    intros.
    exact (syll (pm2_621 p q) (pm2_38 r (or p q) q)).
Qed.

Theorem pm2_74 : forall (p q r : Prop), (impl (impl q p) (impl (or3 p q r) (or p r))).
Proof.
    intros.
    exact (syll (pm2_73 q p r) (mp (syll (syll (or_assoc p q r) (pm_assoc p q r)) (or_assoc2 q p r)) (pm_syll (or3 p q r) (or3 q p r) (or p r)))).
Qed.

Theorem pm2_75 : forall (p q r : Prop), (impl (or p q) (impl (or p (impl q r)) (or p r))).
Proof.
    intros.
    exact (syll (or_comm p q) (syll (syll (pm2_53 q p) (pm2_74 p (not q) r)) (impl_subl (pm2_31 p (not q) r) (or p r)))).
Qed.

Theorem pm2_76 : forall (p q r : Prop), (impl (or p (impl q r)) (impl (or p q) (or p r))).
Proof.
    intros.
    exact (mp (pm2_75 p q r) (pm_comm (or p q) (or p (impl q r)) (or p r))).
Qed.

Theorem pm2_77 : forall (p q r : Prop), (impl (impl p (impl q r)) (impl (impl p q) (impl p r))).
Proof.
    intros.
    exact (pm2_76 (not p) q r).
Qed.

Theorem mpc : forall {p q r : Prop} (H0 : (impl p q)) (H1 : (impl p (impl q r))), (impl p r).
Proof.
    intros.
    exact (mp H0 (mp H1 (pm2_77 p q r))).
Qed.

Theorem pm2_8 : forall (q r s : Prop), (impl (or q r) (impl (or (not r) s) (or q s))).
Proof.
    intros.
    pose (S1 := (syll (pm_perm q r) (pm2_53 r q))).
    exact (syll S1 (pm2_38 s (not r) q)).
Qed.

Theorem pm2_81 : forall (p q r s : Prop), (impl (impl q (impl r s)) (impl (or p q) (impl (or p r) (or p s)))).
Proof.
    intros.
    pose (S1 := (pm_sum p q (impl r s))).
    pose (S2 := (mp (pm2_76 p r s) (pm_syll2 (or p q) (or p (impl r s)) (impl (or p r) (or p s))))).
    exact (syll S1 S2).
Qed.

Theorem pm2_82 : forall (p q r s : Prop), (impl (or3 p q r) (impl (or3 p (not r) s) (or3 p q s))).
Proof.
    intros.
    exact (syll (syll (or_assoc p q r) (mp (pm2_8 q r s) (pm2_81 p (or q r) (or (not r) s) (or q s)))) (syll (impl_subl (or_assoc p (not r) s) (or p (or q s))) (impl_subr (or_assoc2 p q s) (or3 p (not r) s)))).
Qed.

Theorem pm2_83 : forall (p q r s : Prop), (impl (impl p (impl q r)) (impl (impl p (impl r s)) (impl p (impl q s)))).
Proof.
    intros.
    exact (syll (syll (or_assoc2 (not p) (not q) r) (pm2_82 (not p) (not q) r s)) (syll (impl_subl (or_assoc2 (not p) (not r) s) (or3 (not p) (not q) s)) (impl_subr (or_assoc (not p) (not q) s) (impl p (impl r s))))).
Qed.

Theorem syllc : forall {p q r s : Prop} (H0 : (impl p (impl q r))) (H1 : (impl p (impl r s))), (impl p (impl q s)).
Proof.
    intros.
    exact (mp H1 (mp H0 (pm2_83 p q r s))).
Qed.

Theorem pm2_85 : forall (p q r : Prop), (impl (impl (or p q) (or p r)) (or p (impl q r))).
Proof.
    intros.
    pose (S1 := (mp (pm_add p q) (pm_syll q (or p q) r))).
    pose (S2 := (pm2_55 p r)).
    pose (S3 := (syll S2 (pm_syll2 (or p q) (or p r) r))).
    pose (S4 := (syll S3 (impl_subr S1 (impl (or p q) (or p r))))).
    pose (S5 := (mp S4 (pm_comm (not p) (impl (or p q) (or p r)) (impl q r)))).
    exact (syll S5 (pm2_54 p (impl q r))).
Qed.

Theorem pm2_86 : forall (p q r : Prop), (impl (impl (impl p q) (impl p r)) (impl p (impl q r))).
Proof.
    intros.
    exact (pm2_85 (not p) q r).
Qed.

Definition and := fun (p q : Prop) => (not (or (not p) (not q))).

Theorem pm3_03 : forall {p q : Prop} (H0 : p) (H1 : q), (and p q).
Proof.
    intros.
    pose (S1 := (pm2_11 (or (not p) (not q)))).
    pose (S2 := (mp S1 (pm2_32 (not p) (not q) (not (or (not p) (not q)))))).
    exact (mp H1 (mp H0 S2)).
Qed.

Theorem andi : forall {p q : Prop} (H0 : p) (H1 : q), (and p q).
Proof.
    intros.
    exact (pm3_03 H0 H1).
Qed.

Theorem pm3_1 : forall (p q : Prop), (impl (and p q) (not (or (not p) (not q)))).
Proof.
    intros.
    exact (pm_id (and p q)).
Qed.

Theorem pm3_11 : forall (p q : Prop), (impl (not (or (not p) (not q))) (and p q)).
Proof.
    intros.
    exact (pm_id (and p q)).
Qed.

Theorem pm3_12 : forall (p q : Prop), (or3 (not p) (not q) (and p q)).
Proof.
    intros.
    exact (pm2_11 (or (not p) (not q))).
Qed.

Theorem pm3_13 : forall (p q : Prop), (impl (not (and p q)) (or (not p) (not q))).
Proof.
    intros.
    exact (mp (pm3_11 p q) (pm_transp2 (or (not p) (not q)) (and p q))).
Qed.

Theorem pm3_14 : forall (p q : Prop), (impl (or (not p) (not q)) (not (and p q))).
Proof.
    intros.
    exact (mp (pm3_1 p q) (pm_transp1 (and p q) (or (not p) (not q)))).
Qed.

Theorem pm3_2 : forall (p q : Prop), (impl p (impl q (and p q))).
Proof.
    intros.
    exact (mp (pm3_12 p q) (or_assoc (not p) (not q) (and p q))).
Qed.

Theorem pm3_21 : forall (p q : Prop), (impl q (impl p (and p q))).
Proof.
    intros.
    exact (mp (pm3_2 p q) (pm_comm p q (and p q))).
Qed.

Theorem pm3_22 : forall (p q : Prop), (impl (and p q) (and q p)).
Proof.
    intros.
    pose (S1 := (pm3_13 q p)).
    pose (S2 := (syll S1 (pm_perm (not q) (not p)))).
    pose (S3 := (syll S2 (pm3_14 p q))).
    exact (mp S3 (pm_transp3 (and q p) (and p q))).
Qed.

Theorem and_comm : forall (p q : Prop), (impl (and p q) (and q p)).
Proof.
    intros.
    exact (pm3_22 p q).
Qed.

Theorem and_commi : forall {p q : Prop} (H : (and p q)), (and q p).
Proof.
    intros.
    exact (mp H (and_comm p q)).
Qed.

Theorem pm3_24 : forall (p q : Prop), (not (and p (not p))).
Proof.
    intros.
    pose (S1 := (pm2_11 (not p))).
    exact (mp S1 (pm3_14 p (not p))).
Qed.

Theorem pm3_26 : forall (p q : Prop), (impl (and p q) p).
Proof.
    intros.
    pose (S1 := (pm2_02 q p)).
    pose (S2 := (mp S1 (pm2_31 (not p) (not q) p))).
    exact (mp S2 (pm2_53 (or (not p) (not q)) p)).
Qed.

Theorem andel : forall (p q : Prop), (impl (and p q) p).
Proof.
    intros.
    exact (pm3_26 p q).
Qed.

Theorem andeli : forall {p q : Prop} (H : (and p q)), p.
Proof.
    intros.
    exact (mp H (andel p q)).
Qed.

Theorem pm3_27 : forall (p q : Prop), (impl (and p q) q).
Proof.
    intros.
    pose (S1 := (pm3_22 p q)).
    exact (syll S1 (pm3_26 q p)).
Qed.

Theorem ander : forall (p q : Prop), (impl (and p q) q).
Proof.
    intros.
    exact (pm3_27 p q).
Qed.

Theorem anderi : forall {p q : Prop} (H : (and p q)), q.
Proof.
    intros.
    exact (mp H (ander p q)).
Qed.

Theorem pm3_3 : forall (p q r : Prop), (impl (impl (and p q) r) (impl p (impl q r))).
Proof.
    intros.
    pose (S1 := (pm_id (impl (and p q) r))).
    pose (S2 := (syll S1 (pm_transp2 (or (not p) (not q)) r))).
    pose (S3 := (syll S2 (pm_comm (not r) p (not q)))).
    exact (syll S3 (mp (pm_transp3 r q) (pm_syll2 p (impl (not r) (not q)) (impl q r)))).
Qed.

Theorem pm_exp : forall (p q r : Prop), (impl (impl (and p q) r) (impl p (impl q r))).
Proof.
    intros.
    exact (pm3_3 p q r).
Qed.

Theorem pm3_31 : forall (p q r : Prop), (impl (impl p (impl q r)) (impl (and p q) r)).
Proof.
    intros.
    pose (S1 := (pm_id (impl p (impl q r)))).
    pose (S2 := (syll S1 (pm2_31 (not p) (not q) r))).
    exact (syll S2 (pm2_53 (or (not p) (not q)) r)).
Qed.

Theorem pm_imp : forall (p q r : Prop), (impl (impl p (impl q r)) (impl (and p q) r)).
Proof.
    intros.
    exact (pm3_31 p q r).
Qed.

Theorem pm3_33 : forall (p q r : Prop), (impl (and (impl p q) (impl q r)) (impl p r)).
Proof.
    intros.
    exact (mp (pm_syll p q r) (pm_imp (impl p q) (impl q r) (impl p r))).
Qed.

Theorem pm_asyll : forall (p q r : Prop), (impl (and (impl p q) (impl q r)) (impl p r)).
Proof.
    intros.
    exact (pm3_33 p q r).
Qed.

Theorem pm3_34 : forall (p q r : Prop), (impl (and (impl q r) (impl p q)) (impl p r)).
Proof.
    intros.
    exact (mp (pm_syll2 p q r) (pm_imp (impl q r) (impl p q) (impl p r))).
Qed.

Theorem pm_asyll2 : forall (p q r : Prop), (impl (and (impl q r) (impl p q)) (impl p r)).
Proof.
    intros.
    exact (pm3_34 p q r).
Qed.

Theorem pm3_35 : forall (p q : Prop), (impl (and p (impl p q)) q).
Proof.
    intros.
    exact (mp (pm2_27 p q) (pm_imp p (impl p q) q)).
Qed.

Theorem pm3_37 : forall (p q r : Prop), (impl (impl (and p q) r) (impl (and p (not r)) (not q))).
Proof.
    intros.
    pose (S1 := (pm_transp0 q r)).
    pose (S2 := (mp S1 (pm_syll2 p (impl q r) (impl (not r) (not q))))).
    pose (S3 := (pm_exp p q r)).
    pose (S4 := (pm_imp p (not r) (not q))).
    exact (syll (syll S3 S2) S4).
Qed.

Theorem pm3_4 : forall (p q : Prop), (impl (and p q) (impl p q)).
Proof.
    intros.
    exact (mp (pm2_51 p q) (pm_transp2 (impl p q) (impl p (not q)))).
Qed.

Theorem pm3_41 : forall (p q r : Prop), (impl (impl p r) (impl (and p q) r)).
Proof.
    intros.
    exact (mp (pm3_26 p q) (pm_syll (and p q) p r)).
Qed.

Theorem pm3_42 : forall (p q r : Prop), (impl (impl q r) (impl (and p q) r)).
Proof.
    intros.
    exact (mp (pm3_27 p q) (pm_syll (and p q) q r)).
Qed.

Theorem pm3_43 : forall (p q r : Prop), (impl (and (impl p q) (impl p r)) (impl p (and q r))).
Proof.
    intros.
    pose (S1 := (pm3_2 q r)).
    pose (S2 := (mp S1 (pm_syll2 p q (impl r (and q r))))).
    pose (S3 := (syll S2 (pm2_77 p r (and q r)))).
    exact (mp S3 (pm_imp (impl p q) (impl p r) (impl p (and q r)))).
Qed.

Theorem pm_comp : forall (p q r : Prop), (impl (and (impl p q) (impl p r)) (impl p (and q r))).
Proof.
    intros.
    exact (pm3_43 p q r).
Qed.

Theorem andd : forall {p q r : Prop} (H0 : (impl p q)) (H1 : (impl p r)), (impl p (and q r)).
Proof.
    intros.
    exact (mp (andi H0 H1) (pm3_43 p q r)).
Qed.

Theorem pm3_44 : forall (p q r : Prop), (impl (and (impl q p) (impl r p)) (impl (or q r) p)).
Proof.
    intros.
    pose (S1 := (pm_asyll (not q) r p)).
    pose (S2 := (syll S1 (pm2_6 q p))).
    pose (S3 := (mp S2 (pm_exp (impl (not q) r) (impl r p) (impl (impl q p) p)))).
    pose (S4 := (syll S3 (syll (pm_comm (impl r p) (impl q p) p) (pm_imp (impl q p) (impl r p) p)))).
    pose (S5 := (mp S4 (pm_comm (impl (not q) r) (and (impl q p) (impl r p)) p))).
    exact (syll S5 (mp (pm2_53 q r) (pm_syll (or q r) (impl (not q) r) p))).
Qed.

Theorem ored : forall {p q r s : Prop} (H0 : (impl p (or q r))) (H1 : (impl p (impl q s))) (H2 : (impl p (impl r s))), (impl p s).
Proof.
    intros.
    pose (S1 := (andd H1 H2)).
    pose (S2 := (syll S1 (pm3_44 s q r))).
    exact (mpc H0 S2).
Qed.

Theorem ore : forall {p q r : Prop} (H0 : (impl p r)) (H1 : (impl q r)), (impl (or p q) r).
Proof.
    intros.
    exact (mp (andi H0 H1) (pm3_44 r p q)).
Qed.

Theorem orei : forall {p q r : Prop} (H0 : (or p q)) (H1 : (impl p r)) (H2 : (impl q r)), r.
Proof.
    intros.
    exact (mp H0 (ore H1 H2)).
Qed.

Theorem pm3_45 : forall (p q r : Prop), (impl (impl p q) (impl (and p r) (and q r))).
Proof.
    intros.
    pose (S1 := (pm_syll p q (not r))).
    exact (syll S1 (pm_transp0 (impl q (not r)) (impl p (not r)))).
Qed.

Theorem pm_fact : forall (p q r : Prop), (impl (impl p q) (impl (and p r) (and q r))).
Proof.
    intros.
    exact (pm3_45 p q r).
Qed.

Theorem and_subl : forall {p q : Prop} (H : (impl p q)) (r : Prop), (impl (and p r) (and q r)).
Proof.
    intros.
    exact (mp H (pm_fact p q r)).
Qed.

Theorem and_subli : forall {p q r : Prop} (H0 : (and p r)) (H1 : (impl p q)), (and q r).
Proof.
    intros.
    exact (mp H0 (and_subl H1 r)).
Qed.

Theorem and_subr : forall {p q : Prop} (H : (impl p q)) (r : Prop), (impl (and r p) (and r q)).
Proof.
    intros.
    exact (syll (and_comm r p) (syll (and_subl H r) (and_comm q r))).
Qed.

Theorem and_subri : forall {p q r : Prop} (H0 : (and r p)) (H1 : (impl p q)), (and r q).
Proof.
    intros.
    exact (mp H0 (and_subr H1 r)).
Qed.

Theorem pm3_47 : forall (p q r s : Prop), (impl (and (impl p r) (impl q s)) (impl (and p q) (and r s))).
Proof.
    intros.
    pose (S1 := (pm3_26 (impl p r) (impl q s))).
    pose (S2 := (syll S1 (pm_fact p r q))).
    pose (S3 := (syll S2 (mp (pm3_22 r q) (pm_syll2 (and p q) (and r q) (and q r))))).
    pose (S4 := (pm3_27 (impl p r) (impl q s))).
    pose (S5 := (syll S4 (pm_fact q s r))).
    pose (S6 := (syll S5 (mp (pm3_22 s r) (pm_syll2 (and q r) (and s r) (and r s))))).
    exact (mp S6 (mp S3 (pm2_83 (and (impl p r) (impl q s)) (and p q) (and q r) (and r s)))).
Qed.

Theorem pm3_48 : forall (p q r s : Prop), (impl (and (impl p r) (impl q s)) (impl (or p q) (or r s))).
Proof.
    intros.
    pose (S1 := (pm3_26 (impl p r) (impl q s))).
    pose (S2 := (syll S1 (pm_sum q p r))).
    pose (S3 := (syll S2 (mp (pm_perm p q) (pm_syll (or p q) (or q p) (or q r))))).
    pose (S4 := (pm3_27 (impl p r) (impl q s))).
    pose (S5 := (syll S4 (pm_sum r q s))).
    pose (S6 := (syll S5 (mp (pm_perm q r) (pm_syll (or q r) (or r q) (or r s))))).
    exact (mp S6 (mp S3 (pm2_83 (and (impl p r) (impl q s)) (or p q) (or q r) (or r s)))).
Qed.

Definition bi := fun (p q : Prop) => (and (impl p q) (impl q p)).

Theorem pm4_1 : forall (p q : Prop), (bi (impl p q) (impl (not q) (not p))).
Proof.
    intros.
    exact (andi (pm2_16 p q) (pm2_17 p q)).
Qed.

Theorem pm4_11 : forall (p q : Prop), (bi (bi p q) (bi (not p) (not q))).
Proof.
    intros.
    exact (andi (syll (mp (andi (pm2_16 p q) (pm2_16 q p)) (pm3_47 (impl p q) (impl q p) (impl (not q) (not p)) (impl (not p) (not q)))) (pm3_22 (impl (not q) (not p)) (impl (not p) (not q)))) (syll (mp (andi (pm2_17 q p) (pm2_17 p q)) (pm3_47 (impl (not p) (not q)) (impl (not q) (not p)) (impl q p) (impl p q))) (pm3_22 (impl q p) (impl p q)))).
Qed.

Theorem pm4_12 : forall (p q : Prop), (bi (bi p (not q)) (bi q (not p))).
Proof.
    intros.
    exact (andi (mp (andi (pm2_03 p q) (pm2_15 q p)) (pm3_47 (impl p (not q)) (impl (not q) p) (impl q (not p)) (impl (not p) q))) (mp (andi (pm2_03 q p) (pm2_15 p q)) (pm3_47 (impl q (not p)) (impl (not p) q) (impl p (not q)) (impl (not q) p)))).
Qed.

Theorem pm4_13 : forall (p : Prop), (bi p (not (not p))).
Proof.
    intros.
    exact (andi (pm2_12 p) (pm2_14 p)).
Qed.

Theorem pm4_14 : forall (p q r : Prop), (bi (impl (and p q) r) (impl (and p (not r)) (not q))).
Proof.
    intros.
    exact (andi (pm3_37 p q r) (syll (syll (pm3_37 p (not r) (not q)) (impl_subr (anderi (pm4_13 r)) (and p (not (not q))))) (impl_subl (and_subr (andeli (pm4_13 q)) p) r))).
Qed.

Theorem pm4_15 : forall (p q r : Prop), (bi (impl (and p q) (not r)) (impl (and q r) (not p))).
Proof.
    intros.
    exact (andi (syll (syll (impl_subl (and_comm q p) (not r)) (andeli (pm4_14 q p (not r)))) (impl_subl (and_subr (andeli (pm4_13 r)) q) (not p))) (syll (impl_subl (and_subr (anderi (pm4_13 r)) q) (not p)) (syll (anderi (pm4_14 q p (not r))) (impl_subl (pm3_22 p q) (not r))))).
Qed.

Theorem pm4_2 : forall (p : Prop), (bi p p).
Proof.
    intros.
    exact (mp (id p) (mp (id p) (pm3_2 (impl p p) (impl p p)))).
Qed.

Theorem bi_id : forall (p : Prop), (bi p p).
Proof.
    intros.
    exact (pm4_2 p).
Qed.

Theorem pm4_21 : forall (p q : Prop), (bi (bi p q) (bi q p)).
Proof.
    intros.
    exact (andi (pm3_22 (impl p q) (impl q p)) (pm3_22 (impl q p) (impl p q))).
Qed.

Theorem bi_comm : forall (p q : Prop), (impl (bi p q) (bi q p)).
Proof.
    intros.
    exact (andeli (pm4_21 p q)).
Qed.

Theorem bi_commi : forall {p q : Prop} (H : (bi p q)), (bi q p).
Proof.
    intros.
    exact (mp H (bi_comm p q)).
Qed.

Theorem pm4_22 : forall (p q r : Prop), (impl (and (bi p q) (bi q r)) (bi p r)).
Proof.
    intros.
    pose (S1 := (pm3_26 (bi p q) (bi q r))).
    pose (S2 := (syll S1 (pm3_26 (impl p q) (impl q p)))).
    pose (S3 := (pm3_27 (bi p q) (bi q r))).
    pose (S4 := (syll S3 (pm3_26 (impl q r) (impl r q)))).
    pose (S5 := (mp S4 (mp S2 (pm2_83 (and (bi p q) (bi q r)) p q r)))).
    pose (S6 := (pm3_27 (bi p q) (bi q r))).
    pose (S7 := (syll S6 (pm3_27 (impl q r) (impl r q)))).
    pose (S8 := (pm3_26 (bi p q) (bi q r))).
    pose (S9 := (syll S8 (pm3_27 (impl p q) (impl q p)))).
    pose (S10 := (mp S9 (mp S7 (pm2_83 (and (bi p q) (bi q r)) r q p)))).
    exact (mp (andi S5 S10) (pm_comp (and (bi p q) (bi q r)) (impl p r) (impl r p))).
Qed.

Theorem bi_trans : forall {p q r s : Prop} (H0 : (impl p (bi q r))) (H1 : (impl p (bi r s))), (impl p (bi q s)).
Proof.
    intros.
    exact (syll (andd H0 H1) (pm4_22 q r s)).
Qed.

Theorem bi_transi : forall {p q r : Prop} (H0 : (bi p q)) (H1 : (bi q r)), (bi p r).
Proof.
    intros.
    exact (mp (andi H0 H1) (pm4_22 p q r)).
Qed.

Theorem pm4_24 : forall (p : Prop), (bi p (and p p)).
Proof.
    intros.
    pose (S1 := (pm3_26 p p)).
    pose (S2 := (pm3_2 p p)).
    pose (S3 := (mp S2 (pm2_43 p (and p p)))).
    exact (andi S3 S1).
Qed.

Theorem pm4_25 : forall (p : Prop), (bi p (or p p)).
Proof.
    intros.
    exact (andi (pm_add p p) (pm_taut p)).
Qed.

Theorem pm4_3 : forall (p q : Prop), (bi (and p q) (and q p)).
Proof.
    intros.
    exact (andi (pm3_22 p q) (pm3_22 q p)).
Qed.

Theorem pm4_31 : forall (p q : Prop), (bi (or p q) (or q p)).
Proof.
    intros.
    exact (andi (pm_perm p q) (pm_perm q p)).
Qed.

Theorem pm4_32 : forall (p q r : Prop), (bi (and (and p q) r) (and p (and q r))).
Proof.
    intros.
    pose (S1 := (pm4_15 p q r)).
    pose (S2 := (bi_transi S1 (andi (pm2_03 (and q r) p) (pm2_03 p (and q r))))).
    exact (mp S2 (andeli (pm4_11 (impl (and p q) (not r)) (impl p (not (and q r)))))).
Qed.

Theorem and_assoc : forall (p q r : Prop), (impl (and (and p q) r) (and p (and q r))).
Proof.
    intros.
    exact (andeli (pm4_32 p q r)).
Qed.

Theorem and_associ : forall {p q r : Prop} (H : (and (and p q) r)), (and p (and q r)).
Proof.
    intros.
    exact (mp H (and_assoc p q r)).
Qed.

Theorem and_assoc2 : forall (p q r : Prop), (impl (and p (and q r)) (and (and p q) r)).
Proof.
    intros.
    exact (anderi (pm4_32 p q r)).
Qed.

Theorem and_associ2 : forall {p q r : Prop} (H : (and p (and q r))), (and (and p q) r).
Proof.
    intros.
    exact (mp H (and_assoc2 p q r)).
Qed.

Theorem pm4_33 : forall (p q r : Prop), (bi (or (or p q) r) (or p (or q r))).
Proof.
    intros.
    exact (andi (pm2_32 p q r) (pm2_31 p q r)).
Qed.

Definition and3 := fun (p q r : Prop) => (and (and p q) r).

Theorem pm4_36 : forall (p q r : Prop), (impl (bi p q) (bi (and p r) (and q r))).
Proof.
    intros.
    exact (mp (andi (pm_fact p q r) (pm_fact q p r)) (pm3_47 (impl p q) (impl q p) (impl (and p r) (and q r)) (impl (and q r) (and p r)))).
Qed.

Theorem pm4_37 : forall (p q r : Prop), (impl (bi p q) (bi (or p r) (or q r))).
Proof.
    intros.
    exact (mp (andi (syll (syll (pm_sum r p q) (impl_subl (or_comm p r) (or r q))) (impl_subr (or_comm r q) (or p r))) (syll (syll (pm_sum r q p) (impl_subl (or_comm q r) (or r p))) (impl_subr (or_comm r p) (or q r)))) (pm3_47 (impl p q) (impl q p) (impl (or p r) (or q r)) (impl (or q r) (or p r)))).
Qed.

Theorem pm4_38 : forall (p q r s : Prop), (impl (and (bi p r) (bi q s)) (bi (and p q) (and r s))).
Proof.
    intros.
    exact (syll (andeli (pm4_32 (impl p r) (impl r p) (and (impl q s) (impl s q)))) (syll (and_subr (anderi (pm4_32 (impl r p) (impl q s) (impl s q))) (impl p r)) (syll (and_subr (and_subl (pm3_22 (impl r p) (impl q s)) (impl s q)) (impl p r)) (syll (and_subr (andeli (pm4_32 (impl q s) (impl r p) (impl s q))) (impl p r)) (syll (anderi (pm4_32 (impl p r) (impl q s) (and (impl r p) (impl s q)))) (mp (andi (pm3_47 p q r s) (pm3_47 r s p q)) (pm3_47 (and (impl p r) (impl q s)) (and (impl r p) (impl s q)) (impl (and p q) (and r s)) (impl (and r s) (and p q))))))))).
Qed.

Theorem pm4_39 : forall (p q r s : Prop), (impl (and (bi p r) (bi q s)) (bi (or p q) (or r s))).
Proof.
    intros.
    exact (syll (andeli (pm4_32 (impl p r) (impl r p) (and (impl q s) (impl s q)))) (syll (and_subr (anderi (pm4_32 (impl r p) (impl q s) (impl s q))) (impl p r)) (syll (and_subr (and_subl (pm3_22 (impl r p) (impl q s)) (impl s q)) (impl p r)) (syll (and_subr (andeli (pm4_32 (impl q s) (impl r p) (impl s q))) (impl p r)) (syll (anderi (pm4_32 (impl p r) (impl q s) (and (impl r p) (impl s q)))) (mp (andi (pm3_48 p q r s) (pm3_48 r s p q)) (pm3_47 (and (impl p r) (impl q s)) (and (impl r p) (impl s q)) (impl (or p q) (or r s)) (impl (or r s) (or p q))))))))).
Qed.

Theorem pm4_4 : forall (p q r : Prop), (bi (and p (or q r)) (or (and p q) (and p r))).
Proof.
    intros.
    pose (S1 := (andi (pm3_2 p q) (pm3_2 p r))).
    pose (S2 := (mp S1 (pm_comp p (impl q (and p q)) (impl r (and p r))))).
    pose (S3 := (syll S2 (pm3_48 q r (and p q) (and p r)))).
    pose (S4 := (mp S3 (pm_imp p (or q r) (or (and p q) (and p r))))).
    pose (S5 := (andi (pm3_26 p q) (pm3_26 p r))).
    pose (S6 := (mp S5 (pm3_44 p (and p q) (and p r)))).
    pose (S7 := (andi (pm3_27 p q) (pm3_27 p r))).
    pose (S8 := (mp S7 (pm3_48 (and p q) (and p r) q r))).
    pose (S9 := (mp (andi S6 S8) (pm_comp (or (and p q) (and p r)) p (or q r)))).
    exact (andi S4 S9).
Qed.

Theorem and_distr : forall (p q r : Prop), (impl (and p (or q r)) (or (and p q) (and p r))).
Proof.
    intros.
    exact (andeli (pm4_4 p q r)).
Qed.

Theorem and_distri : forall {p q r : Prop} (H : (and p) (or q r)), (or (and p q) (and p r)).
Proof.
    intros.
    exact (mp H (and_distr p q r)).
Qed.

Theorem and_fact : forall (p q r : Prop), (impl (or (and p q) (and p r)) (and p (or q r))).
Proof.
    intros.
    exact (anderi (pm4_4 p q r)).
Qed.

Theorem and_facti : forall {p q r : Prop} (H : (or (and p q) (and p r))), (and p (or q r)).
Proof.
    intros.
    exact (mp H (and_fact p q r)).
Qed.

Theorem pm4_41 : forall (p q r : Prop), (bi (or p (and q r)) (and (or p q) (or p r))).
Proof.
    intros.
    pose (S1 := (mp (pm3_26 q r)) (pm_sum p (and q r) q)).
    pose (S2 := (mp (pm3_27 q r)) (pm_sum p (and q r) r)).
    pose (S3 := (mp (andi S1 S2) (pm_comp (or p (and q r)) (or p q) (or p r)))).
    pose (S4 := (mp (andi (pm2_53 p q) (pm2_53 p r)) (pm3_47 (or p q) (or p r) (impl (not p) q) (impl (not p) r)))).
    pose (S5 := (syll S4 (pm_comp (not p) q r))).
    pose (S6 := (syll S5 (pm2_54 p (and q r)))).
    exact (andi S3 S6).
Qed.

Theorem or_distr : forall (p q r : Prop), (impl (or p (and q r)) (and (or p q) (or p r))).
Proof.
    intros.
    exact (andeli (pm4_41 p q r)).
Qed.

Theorem or_distri : forall {p q r : Prop} (H : (or p (and q r))), (and (or p q) (or p r)).
Proof.
    intros.
    exact (mp H (or_distr p q r)).
Qed.

Theorem or_fact : forall (p q r : Prop), (impl (and (or p q) (or p r)) (or p (and q r))).
Proof.
    intros.
    exact (anderi (pm4_41 p q r)).
Qed.

Theorem or_facti : forall {p q r : Prop} (H : (and (or p q) (or p r))), (or p (and q r)).
Proof.
    intros.
    exact (mp H (or_fact p q r)).
Qed.

Theorem pm4_42 : forall (p q : Prop), (bi p (or (and p q) (and p (not q)))).
Proof.
Admitted.

Theorem pm4_43 : forall (p q : Prop), (bi p (and (or p q) (or p (not q)))).
Proof.
Admitted.

Theorem pm4_44 : forall (p q : Prop), (bi p (or p (and p q))).
Proof.
Admitted.

Theorem pm4_45 : forall (p q : Prop), (bi p (and p (or p q))).
Proof.
Admitted.

Theorem pm4_5 : forall (p q : Prop), (bi (and p q) (not (or (not p) (not q)))).
Proof.
Admitted.

Theorem pm4_51 : forall (p q : Prop), (bi (not (and p q)) (or (not p) (not q))).
Proof.
Admitted.

Theorem pm4_52 : forall (p q : Prop), (bi (and p (not q)) (not (or (not p) q))).
Proof.
Admitted.

Theorem pm4_53 : forall (p q : Prop), (bi (not (and p (not q))) (or (not p) q)).
Proof.
Admitted.

Theorem pm4_54 : forall (p q : Prop), (bi (and (not p) q) (not (or p (not q)))).
Proof.
Admitted.

Theorem pm4_55 : forall (p q : Prop), (bi (not (and (not p) q)) (or p (not q))).
Proof.
Admitted.

Theorem pm4_56 : forall (p q : Prop), (bi (and (not p) (not q)) (not (or p q))).
Proof.
Admitted.

Theorem pm4_57 : forall (p q : Prop), (bi (not (and (not p) (not q))) (or p q)).
Proof.
Admitted.

Theorem pm4_6 : forall (p q : Prop), (bi (impl p q) (or (not p) q)).
Proof.
Admitted.

Theorem pm4_61 : forall (p q : Prop), (bi (not (impl p q)) (and p (not q))).
Proof.
Admitted.

Theorem pm4_62 : forall (p q : Prop), (bi (impl p (not q)) (or (not p) (not q))).
Proof.
Admitted.

Theorem pm4_63 : forall (p q : Prop), (bi (not (impl p (not q))) (and p q)).
Proof.
Admitted.

Theorem pm4_64 : forall (p q : Prop), (bi (impl (not p) q) (or p q)).
Proof.
Admitted.

Theorem pm4_65 : forall (p q : Prop), (bi (not (impl (not p) q)) (and (not p) (not q))).
Proof.
Admitted.

Theorem pm4_66 : forall (p q : Prop), (bi (impl (not p) (not q)) (or p (not q))).
Proof.
Admitted.

Theorem pm4_67 : forall (p q : Prop), (bi (not (impl (not p) (not q))) (and (not p) q)).
Proof.
Admitted.

Theorem pm4_7 : forall (p q : Prop), (bi (impl p q) (impl p (and p q))).
Proof.
Admitted.

Theorem pm4_71 : forall (p q : Prop), (bi (impl p q) (bi p (and p q))).
Proof.
Admitted.

Theorem pm4_72 : forall (p q : Prop), (bi (impl p q) (bi q (or p q))).
Proof.
Admitted.

Theorem pm4_73 : forall (p q : Prop), (impl q (bi p (and p q))).
Proof.
Admitted.

Theorem pm4_74 : forall (p q : Prop), (impl (not p) (bi q (or p q))).
Proof.
Admitted.

Theorem pm4_76 : forall (p q r : Prop), (bi (and (impl p q) (impl p r)) (impl p (and q r))).
Proof.
Admitted.

Theorem pm4_77 : forall (p q r : Prop), (bi (and (impl q p) (impl q r)) (impl (or q r) p)).
Proof.
Admitted.

Theorem pm4_78 : forall (p q r : Prop), (bi (or (impl p q) (impl p r)) (impl p (or q r))).
Proof.
Admitted.

Theorem pm4_79 : forall (p q r : Prop), (bi (or (impl q p) (impl r p)) (impl (and q r) p)).
Proof.
Admitted.

Theorem pm4_8 : forall (p : Prop), (bi (impl p (not p)) (not p)).
Proof.
Admitted.

Theorem pm4_81 : forall (p : Prop), (bi (impl (not p) p) p).
Proof.
Admitted.

Theorem pm4_82 : forall (p q : Prop), (bi (and (impl p q) (impl p (not q))) (not p)).
Proof.
Admitted.

Theorem pm4_83 : forall (p q : Prop), (bi (and (impl p q) (impl (not p) q)) q).
Proof.
Admitted.

Theorem pm4_84 : forall (p q r : Prop), (impl (bi p q) (bi (impl p r) (impl q r))).
Proof.
Admitted.

Theorem pm4_85 : forall (p q r : Prop), (impl (bi p q) (bi (impl r p) (impl r q))).
Proof.
Admitted.

Theorem pm4_86 : forall (p q r : Prop), (impl (bi p q) (bi (bi p r) (bi q r))).
Proof.
Admitted.

Definition bi4 := fun (p q r s : Prop) => (and (and (bi p q) (bi q r)) (bi r s)).

Theorem pm4_87 : forall (p q r : Prop), (bi4 (impl (and p q) r) (impl p (impl q r)) (impl q (impl p r)) (impl (and q p) r)).
Proof.
Admitted.

Theorem pm5_1 : forall (p q : Prop), (impl (and p q) (bi p q)).
Proof.
Admitted.

Theorem pm5_11 : forall (p q : Prop), (or (impl p q) (impl (not p) q)).
Proof.
Admitted.

Theorem pm5_12 : forall (p q : Prop), (or (impl p q) (impl p (not q))).
Proof.
Admitted.

Theorem pm5_13 : forall (p q : Prop), (or (impl p q) (impl q p)).
Proof.
Admitted.

Theorem pm5_14 : forall (p q r : Prop), (or (impl p q) (impl q r)).
Proof.
Admitted.

Theorem pm5_15 : forall (p q : Prop), (or (bi p q) (bi p (not q))).
Proof.
Admitted.

Theorem pm5_16 : forall (p q : Prop), (not (and (bi p q) (bi p (not q)))).
Proof.
Admitted.

Theorem pm5_17 : forall (p q : Prop), (bi (and (or p q) (not (and p q))) (bi p (not q))).
Proof.
Admitted.

Theorem pm5_18 : forall (p q : Prop), (bi (bi p q) (not (bi p (not q)))).
Proof.
Admitted.

Theorem pm5_19 : forall (p : Prop), (not (bi p (not p))).
Proof.
Admitted.

Theorem pm5_21 : forall (p q : Prop), (impl (and (not p) (not q)) (bi p q)).
Proof.
Admitted.

Theorem pm5_22 : forall (p q : Prop), (bi (not (bi p q)) (or (and p (not q)) (and q (not p)))).
Proof.
Admitted.

Theorem pm5_23 : forall (p q : Prop), (bi (bi p q) (or (and p q) (and (not p) (not q)))).
Proof.
Admitted.

Theorem pm5_24 : forall (p q : Prop), (bi (not (or (and p q) (and (not p) (not q)))) (or (and p (not q)) (and (not p) q))).
Proof.
Admitted.

Theorem pm5_25 : forall (p q : Prop), (bi (or p q) (impl (impl p q) q)).
Proof.
Admitted.

Theorem pm5_3 : forall (p q r : Prop), (bi (impl (and p q) r) (impl (and p q) (and p r))).
Proof.
Admitted.

Theorem pm5_31 : forall (p q r : Prop), (impl (and r (impl p q)) (impl p (and q r))).
Proof.
Admitted.

Theorem pm5_32 : forall (p q r : Prop), (bi (impl p (bi q r)) (bi (and p q) (and p r))).
Proof.
Admitted.

Theorem pm5_33 : forall (p q r : Prop), (bi (and p (impl q r)) (and p (impl (and p q) r))).
Proof.
Admitted.

Theorem pm5_35 : forall (p q r : Prop), (impl (and (impl p q) (impl p r)) (impl p (bi q r))).
Proof.
Admitted.

Theorem pm5_36 : forall (p q r : Prop), (bi (and p (bi p q)) (and q (bi p q))).
Proof.
Admitted.

Theorem pm5_4 : forall (p q : Prop), (bi (impl p (impl p q)) (impl p q)).
Proof.
Admitted.

Theorem pm5_41 : forall (p q r : Prop), (bi (impl (impl p q) (impl p r)) (impl p (impl q r))).
Proof.
Admitted.

Theorem pm5_42 : forall (p q r : Prop), (bi (impl p (impl q r)) (impl p (impl q (and p r)))).
Proof.
Admitted.

Theorem pm5_44 : forall (p q r : Prop), (impl (impl p q) (bi (impl p r) (impl p (and q r)))).
Proof.
Admitted.

Theorem pm5_5 : forall (p q : Prop), (impl p (bi (impl p q) q)).
Proof.
Admitted.

Theorem pm5_501 : forall (p q : Prop), (impl p (bi q (bi p q))).
Proof.
Admitted.

Theorem pm5_53 : forall (p q r s : Prop), (bi (impl (or3 p q r) s) (and3 (impl p s) (impl q s) (impl r s))).
Proof.
Admitted.

Theorem pm5_54 : forall (p q : Prop), (or (bi (and p q) p) (bi (and p q) q)).
Proof.
Admitted.

Theorem pm5_55 : forall (p q : Prop), (or (bi (or p q) p) (bi (or p q) q)).
Proof.
Admitted.

Theorem pm5_6 : forall (p q r : Prop), (bi (impl (and p (not q)) r) (impl p (or q r))).
Proof.
Admitted.

Theorem pm5_61 : forall (p q : Prop), (bi (and (or p q) (not q)) (and p (not q))).
Proof.
Admitted.

Theorem pm5_62 : forall (p q : Prop), (bi (or (and p q) (not q)) (or p (not q))).
Proof.
Admitted.

Theorem pm5_63 : forall (p q : Prop), (bi (or p q) (or p (and (not p) q))).
Proof.
Admitted.

Theorem pm5_7 : forall (p q r : Prop), (bi (bi (or p r) (or q r)) (or r (bi p q))).
Proof.
Admitted.

Theorem pm5_71 : forall (p q r : Prop), (impl (impl q (not r)) (bi (and (or p q) r) (and p r))).
Proof.
Admitted.

Theorem pm5_74 : forall (p q r : Prop), (bi (impl p (bi q r)) (bi (impl p q) (impl p r))).
Proof.
Admitted.

Theorem pm5_75 : forall (p q r : Prop), (impl (and (impl r (not q)) (bi p (or q r))) (bi (and p (not q)) r)).
Proof.
Admitted.

Axiom set : forall (x : Type), Prop.
Axiom el : forall (x y : Type), Prop.
Axiom all : forall (P : forall (x : Type), Prop), Prop.
Definition ex := fun (P : forall (x : Type), Prop) => (not (all (fun (x : Type) => (not (P x))))).
Definition eq := fun (x y : Type) => (all (fun (z : Type) => (bi (el z x) (el z y)))).

Axiom ax_spec : forall {x : Type} (Vx : (set x)) (P : forall (y : Type), Prop), (impl (all P) (P x)).
Axiom ax_gen : forall (P : forall (x : Type), Prop) (H : (forall (x : Type) (Vx : (set x)), (P x))), (all P).
Axiom ax_quant_impl : forall (p : Prop) (Q : forall (x : Type), Prop), (impl (all (fun (x : Type) => (impl p (Q x)))) (impl p (all Q))).
Axiom ax_ex : (ex (fun (x : Type) => (eq x x))).

Theorem pm10_1 : forall {x : Type} (H : (set x)) (P : forall (y : Type), Prop), (impl (all P) (P x)).
Proof.
    intros.
    exact (ax_spec H P).
Qed.

Theorem pm10_11 : forall (P : forall (x : Type), Prop) (H : forall (x : Type) (Vx : (set x)), (P x)), (all P).
Proof.
    intros.
    exact (ax_gen P H).
Qed.

Theorem pm10_12 : forall (p : Prop) (Q : forall (x : Type), Prop), (impl (all (fun (x : Type) => (or p (Q x)))) (or p (all Q))).
Proof.
    intros.
    pose (S1 := (ax_quant_impl (not p) Q)).
    enough (S2 : (impl (all (fun (x : Type) => (or p (Q x)))) (all (fun (x : Type) => (impl (not p) (Q x)))))).
    pose (S3 := (syll S2 S1)).
    enough (S4 : (impl (impl (not p) (all Q)) (or p (all Q)))).
    exact (syll S3 S4).
    pose (S4 := (id (impl (not p) (all Q)))).
    pose (S5 := (impliri (impl (not p) (all Q)) (ex_mid p))).
    pose (S6 := (impliri (impl (not p) (all Q)) (oril p (all Q)))).
    pose (S7 := (syllc S4 (impliri (impl (not p) (all Q)) (orir p (all Q))))).
    exact (ored S5 S6 S7).
    enough (S2 : (all (fun (x : Type) => (impl (or p (Q x)) (impl (not p) (Q x)))))).
    enough (S3 : (impl (all (fun (x : Type) => (impl (or p (Q x)) (impl (not p) (Q x))))) (impl (all (fun (x : Type) => (or p (Q x)))) (all (fun (x : Type) => (impl (not p) (Q x))))))).
    exact (mp S2 S3).
    enough (S3 : (all (fun (x : Type) => (impl (all (fun (y : Type) => (impl (or p (Q y)) (impl (not p) (Q y))))) (impl (all (fun (y : Type) => (or p (Q y)))) (impl (not p) (Q x))))))).
    pose (S4 := (mp S3 (ax_quant_impl (all (fun (x : Type) => (impl (or p (Q x)) (impl (not p) (Q x))))) (fun (x : Type) => (impl (all (fun (y : Type) => (or p (Q y)))) (impl (not p) (Q x))))))).
    exact (syll S4 (ax_quant_impl (all (fun (x : Type) => (or p (Q x)))) (fun (x : Type) => (impl (not p) (Q x))))).
    assert (S3 : forall (x : Type) (Vx : (set x)), (impl (all (fun (y : Type) => (impl (or p (Q y)) (impl (not p) (Q y))))) (impl (all (fun (y : Type) => (or p (Q y)))) (impl (not p) (Q x))))).
    intros.
    enough (S3 : (impl (all (fun (y : Type) => (or p (Q y)))) (impl (not p) (Q x)))).
    exact (impliri (all (fun (y : Type) => (impl (or p (Q y)) (impl (not p) (Q y))))) S3).
    pose (S3 := (ax_spec Vx (fun (y : Type) => (or p (Q y))))).
    pose (S4 := (impliri (all (fun (y : Type) => (or p (Q y)))) (implir (not p) (Q x)))).
    pose (S5 := (impliri (all (fun (y : Type) => (or p (Q y)))) (syll (notdi p) (implil (not p) (Q x))))).
    exact (ored S3 S5 S4).
    exact (ax_gen (fun (x : Type) => (impl (all (fun (y : Type) => (impl (or p (Q y)) (impl (not p) (Q y))))) (impl (all (fun (y : Type) => (or p (Q y)))) (impl (not p) (Q x))))) S3).
    assert (S2 : forall (x : Type) (Vx : (set x)), (impl (or p (Q x)) (impl (not p) (Q x)))).
    intros.
    pose (S2 := (implir (not p) (Q x))).
    pose (S3 := (syll (notdi p) (implil (not p) (Q x)))).
    exact (ore S3 S2).
    exact (ax_gen (fun (x : Type) => (impl (or p (Q x)) (impl (not p) (Q x)))) S2).
Qed.

Theorem pm10_14 : forall {x : Type} (Vx : (set x)) (P Q : forall (y : Type), Prop), (impl (and (all P) (all Q)) (and (P x) (Q x))).
Proof.
    intros.
    pose (S1 := (pm10_1 Vx P)).
    pose (S2 := (pm10_1 Vx Q)).
    pose (S3 := (andi S1 S2)).
    exact (mp S3 (pm3_47 (all P) (all Q) (P x) (Q x))).
Qed.

Theorem pm10_2 : forall (p : Prop) (Q : forall (x : Type), Prop), (bi (all (fun (x : Type) => (or p (Q x)))) (or p (all Q))).
Proof.
    intros.
    assert (S1 : forall (x : Type) (Vx : (set x)), (impl (or p (all Q)) (or p (Q x)))).
    intros.
    exact (mp (pm10_1 Vx Q) (pm_sum p (all Q) (Q x))).
    pose (S2 := (pm10_11 (fun (x : Type) => (impl (or p (all Q)) (or p (Q x)))) S1)).
    pose (S3 := (mp S2 (pm10_12 (not (or p (all Q))) (fun (x : Type) => (or p (Q x)))))).
    pose (S4 := (pm10_12 p Q)).
    exact (andi S4 S3).
Qed.

Theorem pm10_21 : forall (p : Prop) (Q : forall (x : Type), Prop), (bi (all (fun (x : Type) => (impl p (Q x)))) (impl p (all Q))).
Proof.
    intros.
    exact (pm10_2 (not p) Q).
Qed.

Theorem pm10_22 : forall (P Q : forall (x : Type), Prop), (bi (all (fun (x : Type) => (and (P x) (Q x)))) (and (all P) (all Q))).
Proof.
    intros.
    assert (S1 : forall (x : Type) (Vx : (set x)), (impl (all (fun (y : Type) => (and (P y) (Q y)))) (P x))).
    intros.
    pose (S1 := (pm10_1 Vx (fun (x : Type) => (and (P x) (Q x))))).
    exact (syll S1 (andel (P x) (Q x))).
    pose (S2 := (pm10_11 (fun (x : Type) => (impl (all (fun (y : Type) => (and (P y) (Q y)))) (P x))) S1)).
    pose (S3 := (mp S2 (andeli (pm10_21 (all (fun (x : Type) => (and (P x) (Q x)))) P)))).
    assert (S4 : forall (x : Type) (Vx : (set x)), (impl (all (fun (y : Type) => (and (P y) (Q y)))) (Q x))).
    intros.
    pose (S4 := (pm10_1 Vx (fun (x : Type) => (and (P x) (Q x))))).
    exact (syll S4 (ander (P x) (Q x))).
    pose (S5 := (pm10_11 (fun (x : Type) => (impl (all (fun (y : Type) => (and (P y) (Q y)))) (Q x))) S4)).
    pose (S6 := (mp S5 (andeli (pm10_21 (all (fun (x : Type) => (and (P x) (Q x)))) Q)))).
    pose (S7 := (mp (andi S3 S6) (pm_comp (all (fun (x : Type) => (and (P x) (Q x)))) (all P) (all Q)))).
    pose (S8 := (pm10_11 (fun (x : Type) => (impl (and (all P) (all Q)) (and (P x) (Q x)))) (fun (x : Type) (Vx : (set x)) => (pm10_14 Vx P Q)))).
    pose (S9 := (mp S8 (andeli (pm10_21 (and (all P) (all Q)) (fun (x : Type) => (and (P x) (Q x))))))).
    exact (andi S7 S9).
Qed.

Theorem pm10_23 : forall (p : Prop) (Q : (forall (x : Type), Prop)), (bi (all (fun (x : Type) => (impl (Q x) p))) (impl (ex Q) p)).
Proof.
    intros.
    pose (S1 := (pm_transp2 (all (fun (x : Type) => (not (Q x)))) p)).
    pose (S2 := (syll S1 (anderi (pm10_21 (not p) (fun (x : Type) => (not (Q x))))))).
    assert (S3 : forall (x : Type) (Vx : (set x)), (impl (impl (ex Q) p) (impl (Q x) p))).
    intros.
    pose (S3 := (syll S2 (pm10_1 Vx (fun (y : Type) => (impl (not p) (not (Q y))))))).
    exact (syll S3 (pm_transp3 p (Q x))).
    pose (S4 := (pm10_11 (fun (x : Type) => (impl (impl (ex Q) p) (impl (Q x) p))) S3)).
    pose (S5 := (mp S4 (andeli (pm10_21 (impl (ex Q) p) (fun (x : Type) => (impl (Q x) p)))))).
    assert (S6 : forall (x : Type) (Vx : (set x)), (impl (all (fun (y : Type) => (impl (Q y) p))) (impl (not p) (not (Q x))))).
    intros.
    pose (S6 := (pm10_1 Vx (fun (y : Type) => (impl (Q y) p)))).
    exact (syll S6 (pm_transp0 (Q x) p)).
    pose (S7 := (mp (pm10_11 (fun (x : Type) => (impl (all (fun (y : Type) => (impl (Q y) p))) (impl (not p) (not (Q x))))) S6) (andeli (pm10_21 (all (fun (x : Type) => (impl (Q x) p))) (fun (x : Type) => (impl (not p) (not (Q x)))))))).
    pose (S8 := (syll S7 (andeli (pm10_21 (not p) (fun (x : Type) => (not (Q x))))))).
    pose (S9 := (syll S8 (pm_transp2 p (all (fun (x : Type) => (not (Q x))))))).
    exact (andi S9 S5).
Qed.

Theorem pm10_24 : forall {x : Type} (Vx : (set x)) (P : (forall (y : Type), Prop)), (impl (P x) (ex P)).
Proof.
    intros.
    pose (S1 := (pm10_1 Vx (fun (y : Type) => (not (P y))))).
    exact (mp S1 (pm_transp1 (all (fun (y : Type) => (not (P y)))) (P x))).
Qed.

Theorem pm10_25 : forall (P : (forall (x : Type), Prop)), (impl (all P) (ex P)).
Proof.
    intros.
    assert (S1 : forall (x : Type) (Vx : (set x)), (impl (eq x x) (impl (all P) (ex P)))).
    intros.
    pose (S1 := (syll (pm10_1 Vx P) (pm10_24 Vx P))).
    exact (impliri (eq x x) S1).
    pose (S2 := (ax_gen (fun (x : Type) => (impl (eq x x) (impl (all P) (ex P)))) S1)).
    pose (S3 := (mp S2 (andeli (pm10_23 (impl (all P) (ex P)) (fun (x : Type) => (eq x x)))))).
    exact (mp ax_ex S3).
Qed.
