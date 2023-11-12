Require Import Ltac2.Ltac2.
Require Import pm1.
Require Import pm2.

Definition and := fun (p q : Prop) => (not (or (not p) (not q))).

Theorem pm3_03 : forall {p q : Prop} (Wp : p) (Wq : q), (and p q).
Proof.
    intros.
    pose (S1 := (pm2_11 (or (not p) (not q)))).
    pose (S2 := (mp S1 (pm2_32 (not p) (not q) (not (or (not p) (not q)))))).
    exact (mp Wq (mp Wp S2)).
Qed.

Theorem pm3_1 : forall (p q : Prop), (impl (and p q) (not (or (not p) (not q)))).
Proof.
    intros.
    exact (id (and p q)).
Qed.

Theorem pm3_11 : forall (p q : Prop), (impl (not (or (not p) (not q))) (and p q)).
Proof.
    intros.
    exact (id (not (or (not p) (not q)))).
Qed.

Theorem pm3_12 : forall (p q : Prop), (or3 (not p) (not q) (and p q)).
Proof.
    intros.
    exact (pm2_11 (or (not p) (not q))).
Qed.

Theorem pm3_13 : forall (p q : Prop), (impl (not (and p q)) (or (not p) (not q))).
Proof.
    intros.
    exact (mp (pm3_11 p q) (transp2 (or (not p) (not q)) (and p q))).
Qed.

Theorem pm3_14 : forall (p q : Prop), (impl (or (not p) (not q)) (not (and p q))).
Proof.
    intros.
    exact (mp (pm3_1 p q) (transp1 (and p q) (or (not p) (not q)))).
Qed.

Theorem pm3_2 : forall (p q : Prop), (impl p (impl q (and p q))).
Proof.
    intros.
    exact (mp (pm3_12 p q) (pm2_32 (not p) (not q) (and p q))).
Qed.

Theorem pm3_21 : forall (p q : Prop), (impl q (impl p (and p q))).
Proof.
    intros.
    exact (mp (pm3_2 p q) (comm p q (and p q))).
Qed.

Theorem pm3_22 : forall (p q : Prop), (impl (and p q) (and q p)).
Proof.
    intros.
    pose (S1 := (pm3_13 q p)).
    pose (S2 := (mp (perm (not q) (not p)) (mp S1 (syll (not (and q p)) (or (not q) (not p)) (or (not p) (not q)))))).
    pose (S3 := (mp (pm3_14 p q) (mp S2 (syll (not (and q p)) (or (not p) (not q)) (not (and p q)))))).
    exact (mp S3 (transp3 (and p q) (and q p))).
Qed.

Theorem pm3_24 : forall (p : Prop), (not (and p (not p))).
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

Definition simpl := pm3_26.

Theorem pm3_27 : forall (p q : Prop), (impl (and p q) q).
Proof.
    intros.
    pose (S1 := (pm3_22 p q)).
    exact (mp (pm3_26 q p) (mp S1 (syll (and p q) (and q p) q))).
Qed.

Definition simpr := pm3_27.

Theorem pm3_3 : forall (p q r : Prop), (impl (impl (and p q) r) (impl p (impl q r))).
Proof.
    intros.
    pose (S1 := (id (impl (and p q) r))).
    pose (S2 := (mp (transp2 (or (not p) (not q)) r) (mp S1 (syll (impl (and p q) r) (impl (not (or (not p) (not q))) r) (impl (not r) (or (not p) (not q))))))).
    pose (S3 := (mp (comm (not r) p (not q)) (mp S2 (syll (impl (and p q) r) (impl (not r) (impl p (not q))) (impl p (impl (not r) (not q))))))).
    exact (mp (mp (transp3 q r) (syllr p (impl (not r) (not q)) (impl q r))) (mp S3 (syll (impl (and p q) r) (impl p (impl (not r) (not q))) (impl p (impl q r))))).
Qed.

Definition exp := pm3_3.

Theorem pm3_31 : forall (p q r : Prop), (impl (impl p (impl q r)) (impl (and p q) r)).
Proof.
    intros.
    pose (S1 := (id (impl p (impl q r)))).
    pose (S2 := (mp (pm2_31 (not p) (not q) r) (mp S1 (syll (impl p (impl q r)) (or (not p) (or (not q) r)) (or (or (not p) (not q)) r))))).
    exact (mp (pm2_53 (or (not p) (not q)) r) (mp S2 (syll (impl p (impl q r)) (or (or (not p) (not q)) r) (impl (not (or (not p) (not q))) r)))).
Qed.

Definition imp := pm3_31.

Theorem pm3_33 : forall (p q r : Prop), (impl (and (impl p q) (impl q r)) (impl p r)).
Proof.
    intros.
    exact (mp (syll p q r) (imp (impl p q) (impl q r) (impl p r))).
Qed.

Definition sylla := pm3_33.

Theorem pm3_34 : forall (p q r : Prop), (impl (and (impl q r) (impl p q)) (impl p r)).
Proof.
    intros.
    exact (mp (syllr p q r) (imp (impl q r) (impl p q) (impl p r))).
Qed.

Definition syllar := pm3_34.

Theorem pm3_35 : forall (p q : Prop), (impl (and p (impl p q)) q).
Proof.
    intros.
    exact (mp (pm2_27 p q) (imp p (impl p q) q)).
Qed.

Definition ass := pm3_35.

Theorem pm3_37 : forall (p q r : Prop), (impl (impl (and p q) r) (impl (and p (not r)) (not q))).
Proof.
    intros.
    pose (S1 := (transp0 q r)).
    pose (S2 := (mp S1 (syllr p (impl q r) (impl (not r) (not q))))).
    pose (S3 := (exp p q r)).
    pose (S4 := (imp p (not r) (not q))).
    exact (mp (mp S4 (mp S2 (syll (impl p (impl q r)) (impl p (impl (not r) (not q))) (impl (and p (not r)) (not q))))) (mp S3 (syll (impl (and p q) r) (impl p (impl q r)) (impl (and p (not r)) (not q))))).
Qed.

Definition transpa := pm3_37.

Theorem pm3_4 : forall (p q : Prop), (impl (and p q) (impl p q)).
Proof.
    intros.
    exact (mp (pm2_51 p q) (transp2 (impl p q) (impl p (not q)))).
Qed.

Theorem pm3_41 : forall (p q r : Prop), (impl (impl p r) (impl (and p q) r)).
Proof.
    intros.
    exact (mp (pm3_26 p q) (syll (and p q) p r)).
Qed.

Theorem pm3_42 : forall (p q r : Prop), (impl (impl q r) (impl (and p q) r)).
Proof.
    intros.
    exact (mp (pm3_27 p q) (syll (and p q) q r)).
Qed.

Theorem pm3_43 : forall (p q r : Prop), (impl (and (impl p q) (impl p r)) (impl p (and q r))).
Proof.
    intros.
    pose (S1 := (pm3_2 q r)).
    pose (S2 := (mp S1 (syllr p q (impl r (and q r))))).
    pose (S3 := (mp (pm2_77 p r (and q r)) (mp S2 (syll (impl p q) (impl p (impl r (and q r))) (impl (impl p r) (impl p (and q r))))))).
    exact (mp S3 (imp (impl p q) (impl p r) (impl p (and q r)))).
Qed.

Definition comp := pm3_43.

Theorem pm3_44 : forall (p q r : Prop), (impl (and (impl q p) (impl r p)) (impl (or q r) p)).
Proof.
    intros.
    pose (S1 := (sylla (not q) r p)).
    pose (S2 := (mp (pm2_6 q p) (mp S1 (syll (and (impl (not q) r) (impl r p)) (impl (not q) p) (impl (impl q p) p))))).
    pose (S3 := (mp S2 (exp (impl (not q) r) (impl r p) (impl (impl q p) p)))).
    pose (S4 := (mp (mp (imp (impl q p) (impl r p) p) (mp (comm (impl r p) (impl q p) p) (syll (impl (impl r p) (impl (impl q p) p)) (impl (impl q p) (impl (impl r p) p)) (impl (and (impl q p) (impl r p)) p)))) (mp S3 (syll (impl (not q) r) (impl (impl r p) (impl (impl q p) p)) (impl (and (impl q p) (impl r p)) p))))).
    pose (S5 := (mp S4 (comm (impl (not q) r) (and (impl q p) (impl r p)) p))).
    exact (mp (mp (pm2_53 q r) (syll (or q r) (impl (not q) r) p)) (mp S5 (syll (and (impl q p) (impl r p)) (impl (impl (not q) r) p) (impl (or q r) p)))).
Qed.

Theorem pm3_45 : forall (p q r : Prop), (impl (impl p q) (impl (and p r) (and q r))).
Proof.
    intros.
    pose (S1 := (syll p q (not r))).
    exact (mp (transp0 (impl q (not r)) (impl p (not r))) (mp S1 (syll (impl p q) (impl (impl q (not r)) (impl p (not r))) (impl (not (impl p (not r))) (not (impl q (not r))))))).
Qed.

Definition fact := pm3_45.

Theorem pm3_47 : forall (p q r s : Prop), (impl (and (impl p r) (impl q s)) (impl (and p q) (and r s))).
Proof.
    intros.
    pose (S1 := (pm3_26 (impl p r) (impl q s))).
    pose (S2 := (mp (fact p r q) (mp S1 (syll (and (impl p r) (impl q s)) (impl p r) (impl (and p q) (and r q)))))).
    pose (S3 := (mp (mp (pm3_22 r q) (syllr (and p q) (and r q) (and q r))) (mp S2 (syll (and (impl p r) (impl q s)) (impl (and p q) (and r q)) (impl (and p q) (and q r)))))).
    pose (S4 := (pm3_27 (impl p r) (impl q s))).
    pose (S5 := (mp (fact q s r) (mp S4 (syll (and (impl p r) (impl q s)) (impl q s) (impl (and q r) (and s r)))))).
    pose (S6 := (mp (mp (pm3_22 s r) (syllr (and q r) (and s r) (and r s))) (mp S5 (syll (and (impl p r) (impl q s)) (impl (and q r) (and s r)) (impl (and q r) (and r s)))))).
    exact (mp S6 (mp S3 (pm2_83 (and (impl p r) (impl q s)) (and p q) (and q r) (and r s)))).
Qed.

Theorem pm3_48 : forall (p q r s : Prop), (impl (and (impl p r) (impl q s)) (impl (or p q) (or r s))).
Proof.
    intros.
    pose (S1 := (pm3_26 (impl p r) (impl q s))).
    pose (S2 := (mp (pm2_38 q p r) (mp S1 (syll (and (impl p r) (impl q s)) (impl p r) (impl (or p q) (or r q)))))).
    pose (S3 := (mp (mp (perm r q) (syllr (or p q) (or r q) (or q r))) (mp S2 (syll (and (impl p r) (impl q s)) (impl (or p q) (or r q)) (impl (or p q) (or q r)))))).
    pose (S4 := (pm3_27 (impl p r) (impl q s))).
    pose (S5 := (mp (pm2_38 r q s) (mp S4 (syll (and (impl p r) (impl q s)) (impl q s) (impl (or q r) (or s r)))))).
    pose (S6 := (mp (mp (perm s r) (syllr (or q r) (or s r) (or r s))) (mp S5 (syll (and (impl p r) (impl q s)) (impl (or q r) (or s r)) (impl (or q r) (or r s)))))).
    exact (mp S6 (mp S3 (pm2_83 (and (impl p r) (impl q s)) (or p q) (or q r) (or r s)))).
Qed.
