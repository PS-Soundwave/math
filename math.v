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

Theorem orr : forall (p q : Prop), (impl q (or p q)).
Proof.
    intros.
    exact (pm_add p q).
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

Theorem implr : forall (p q : Prop), (impl q (impl p q)).
Proof.
    intros.
    exact (pm2_02 p q).
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

Theorem pm2_12 : forall (p : Prop), (impl p (not (not p))).
Proof.
    intros.
    exact (pm2_11 (not p)).
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

Theorem orl : forall (p q : Prop), (impl p (or p q)).
Proof.
    intros.
    exact (pm2_2 p q).
Qed.

Theorem pm2_21 : forall (p q : Prop), (impl (not p) (impl p q)).
Proof.
    intros.
    exact (pm2_2 (not p) q).
Qed.

Theorem impll : forall (p q : Prop), (impl (not p) (impl p q)).
Proof.
    intros.
    exact (pm2_21 p q).
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
