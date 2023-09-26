Require Import Ltac2.Ltac2.
Require Import pm1.

Theorem pm2_01 : forall (p : Prop), (impl (impl p (not p)) (not p)).
Proof.
    intros.
    exact (taut (not p)).
Qed.

Definition abs := pm2_01.

Theorem pm2_02 : forall (p q : Prop), (impl q (impl p q)).
Proof.
    intros.
    exact (add (not p) q).
Qed.

Definition simp := pm2_02.

Theorem pm2_03 : forall (p q : Prop), (impl (impl p (not q)) (impl q (not p))).
Proof.
    intros.
    exact (perm (not p) (not q)).
Qed.

Definition transp1 := pm2_03.

Theorem pm2_04 : forall (p q r : Prop), (impl (impl p (impl q r)) (impl q (impl p r))).
Proof.
    intros.
    exact (assoc (not p) (not q) r).
Qed.

Definition comm := pm2_04.

Theorem pm2_05 : forall (p q r : Prop), (impl (impl q r) (impl (impl p q) (impl p r))).
Proof.
    intros.
    exact (sum (not p) q r).
Qed.

Definition syllr := pm2_05.

Theorem pm2_06 : forall (p q r : Prop), (impl (impl p q) (impl (impl q r) (impl p r))).
Proof.
    intros.
    pose (S1 := (comm (impl q r) (impl p q) (impl p r))).
    pose (S2 := (pm2_05 p q r)).
    exact (pm1_11 S2 S1).
Qed.

Definition syll := pm2_06.

Theorem pm2_07 : forall (p : Prop), (impl p (or p p)).
Proof.
    intros.
    exact (pm1_3 p p).
Qed.

Theorem pm2_08 : forall (p : Prop), (impl p p).
Proof.
    intros.
    pose (S1 := (pm2_05 p (or p p) p)).
    pose (S2 := (taut p)).
    pose (S3 := (pm1_11 S2 S1)).
    pose (S4 := (pm2_07 p)).
    exact (pm1_11 S4 S3).
Qed.

Definition id := pm2_08.

Theorem pm2_1 : forall (p : Prop), (or (not p) p).
Proof.
    intros.
    exact (pm2_08 p).
Qed.

Theorem pm2_11 : forall (p : Prop), (or p (not p)).
Proof.
    intros.
    pose (S1 := (perm (not p) p)).
    exact (pm1_11 (pm2_1 p) S1).
Qed.

Theorem pm2_12 : forall (p : Prop), (impl p (not (not p))).
Proof.
    intros.
    exact (pm2_11 (not p)).
Qed.

Theorem pm2_13 : forall (p : Prop), (or p (not (not (not p)))).
Proof.
    intros.
    pose (S1 := (sum p (not p) (not (not (not p))))).
    pose (S2 := (pm2_12 (not p))).
    pose (S3 := (pm1_11 S2 S1)).
    exact (pm1_11 (pm2_11 p) S3).
Qed.

Theorem pm2_14 : forall (p : Prop), (impl (not (not p)) p).
Proof.
    intros.
    pose (S1 := (perm p (not (not (not p))))).
    exact (pm1_11 (pm2_13 p) S1).
Qed.

Theorem pm2_15 : forall (p q : Prop), (impl (impl (not p) q) (impl (not q) p)).
Proof.
    intros.
    pose (S1 := (pm2_05 (not p) q (not (not q)))).
    pose (S2 := (pm2_12 q)).
    pose (S3 := (pm1_11 S2 S1)).
    pose (S4 := (pm2_03 (not p) (not q))).
    pose (S5 := (pm2_05 (not q) (not (not p)) p)).
    pose (S6 := (pm1_11 (pm2_14 p) S5)).
    pose (S7 := (pm2_05 (impl (not p) q) (impl (not p) (not (not q))) (impl (not q) (not (not p))))).
    pose (S8 := (pm1_11 S4 S7)).
    pose (S9 := (pm1_11 S3 S8)).
    pose (S10 := (pm2_05 (impl (not p) q) (impl (not q) (not (not p))) (impl (not q) p))).
    pose (S11 := (pm1_11 S6 S10)).
    exact (pm1_11 S9 S11).
Qed.

Definition transp2 := pm2_15.

Theorem pm2_16 : forall (p q : Prop), (impl (impl p q) (impl (not q) (not p))).
Proof.
    intros.
    pose (S1 := (pm2_12 q)).
    pose (S2 := (pm1_11 S1 (pm2_05 p q (not (not q))))).
    pose (S3 := (pm2_03 p (not q))).
    exact (pm1_11 S3 (pm1_11 S2 (syll (impl p q) (impl p (not (not q))) (impl (not q) (not p))))).
Qed.

Definition transp0 := pm2_16.

Theorem pm2_17 : forall (p q : Prop), (impl (impl (not q) (not p)) (impl p q)).
Proof.
    intros.
    pose (S1 := (pm2_03 (not q) p)).
    pose (S2 := (pm2_14 q)).
    pose (S3 := (pm1_11 S2 (pm2_05 p (not (not q)) q))).
    exact (pm1_11 S3 (pm1_11 S1 (syll (impl (not q) (not p)) (impl p (not (not q))) (impl p q)))).
Qed.

Definition transp3 := pm2_17.

Theorem pm2_18 : forall (p : Prop), (impl (impl (not p) p) p).
Proof.
    intros.
    pose (S1 := (pm2_12 p)).
    pose (S2 := (pm1_11 S1 (pm2_05 (not p) p (not (not p))))).
    pose (S3 := (pm2_01 (not p))).
    pose (S4 := (pm1_11 S3 (pm1_11 S2 (syll (impl (not p) p) (impl (not p) (not (not p))) (not (not p)))))).
    pose (S5 := (pm2_14 p)).
    exact (pm1_11 S5 (pm1_11 S4 (syll (impl (not p) p) (not (not p)) p))).
Qed.

Theorem pm2_2 : forall (p q : Prop), (impl p (or p q)).
Proof.
    intros.
    pose (S1 := (add q p)).
    pose (S2 := (perm q p)).
    exact (pm1_11 S2 (pm1_11 S1 (syll p (or q p) (or p q)))).
Qed.

Theorem pm2_21 : forall (p q : Prop), (impl (not p) (impl p q)).
Proof.
    intros.
    exact (pm2_2 (not p) q).
Qed.

Theorem pm2_24 : forall (p q : Prop), (impl p (impl (not p) q)).
Proof.
    intros.
    exact (pm1_11 (pm2_21 p q) (comm (not p) p q)).
Qed.

Theorem pm2_25 : forall (p q : Prop), (or p (impl (or p q) q)).
Proof.
    intros.
    pose (S1 := (pm2_1 (or p q))).
    exact (pm1_11 S1 (pm1_5 (not (or p q)) p q)).
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
    pose (S1 := (perm q r)).
    exact (pm1_11 S1 (sum p (or q r) (or r q))).
Qed.

Theorem pm2_31 : forall (p q r : Prop), (impl (or p (or q r)) (or (or p q) r)).
Proof.
    intros.
    pose (S1 := (pm2_3 p q r)).
    pose (S2 := (pm1_11 (assoc p r q) (pm1_11 S1 (syll (or p (or q r)) (or p (or r q)) (or r (or p q)))))).
    exact (pm1_11 (perm r (or p q)) (pm1_11 S2 (syll (or p (or q r)) (or r (or p q)) (or (or p q) r)))).
Qed.

Theorem pm2_32 : forall (p q r : Prop), (impl (or (or p q) r) (or p (or q r))).
Proof.
    intros.
    pose (S1 := (perm (or p q) r)).
    pose (S2 := (pm1_11 (assoc r p q) (pm1_11 S1 (syll (or (or p q) r) (or r (or p q)) (or p (or r q)))))).
    exact (pm1_11 (pm2_3 p r q) (pm1_11 S2 (syll (or (or p q) r) (or p (or r q)) (or p (or q r))))).
Qed.

Definition or3 := fun (p q r : Prop) => (or (or p q) r).

Theorem pm2_36 : forall (p q r : Prop), (impl (impl q r) (impl (or p q) (or r p))).
Proof.
    intros.
    pose (S1 := (perm p r)).
    pose (S2 := (pm1_11 S1 (syllr (or p q) (or p r) (or r p)))).
    pose (S3 := (sum p q r)).
    exact (pm1_11 S2 (pm1_11 S3 (syll (impl q r) (impl (or p q) (or p r)) (impl (or p q) (or r p))))).
Qed.

Theorem pm2_37 : forall (p q r : Prop), (impl (impl q r) (impl (or q p) (or p r))).
Proof.
    intros.
    pose (S1 := (perm q p)).
    pose (S2 := (pm1_11 S1 (syll (or q p) (or p q) (or p r)))).
    pose (S3 := (sum p q r)).
    exact (pm1_11 S2 (pm1_11 S3 (syll (impl q r) (impl (or p q) (or p r)) (impl (or q p) (or p r))))).
Qed.

Theorem pm2_38 : forall (p q r : Prop), (impl (impl q r) (impl (or q p) (or r p))).
Proof.
    intros.
    pose (S1 := (perm q p)).
    pose (S2 := (pm1_11 S1 (syll (or q p) (or p q) (or r p)))).
    pose (S3 := (pm2_36 p q r)).
    exact (pm1_11 S2 (pm1_11 S3 (syll (impl q r) (impl (or p q) (or r p)) (impl (or q p) (or r p))))).
Qed.

Theorem pm2_4 : forall (p q : Prop), (impl (or p (or p q)) (or p q)).
Proof.
    intros.
    pose (S1 := (pm2_31 p p q)).
    exact (pm1_11 (pm1_11 (taut p) (pm2_38 q (or p p) p)) (pm1_11 S1 (syll (or p (or p q)) (or (or p p) q) (or p q)))).
Qed.

Theorem pm2_41 : forall (p q : Prop), (impl (or q (or p q)) (or p q)).
Proof.
    intros.
    pose (S1 := (assoc q p q)).
    exact (pm1_11 (pm1_11 (taut q) (sum p (or q q) q)) (pm1_11 S1 (syll (or q (or p q)) (or p (or q q)) (or p q)))).
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
    exact (pm1_11 (pm2_2 p q) (transp0 p (or p q))).
Qed.

Theorem pm2_46 : forall (p q : Prop), (impl (not (or p q)) (not q)).
Proof.
    intros.
    exact (pm1_11 (pm1_3 p q) (transp0 q (or p q))).
Qed.

Theorem pm2_47 : forall (p q : Prop), (impl (not (or p q)) (or (not p) q)).
Proof.
    intros.
    exact (pm1_11 (pm2_2 (not p) q) (pm1_11 (pm2_45 p q) (syll (not (or p q)) (not p) (or (not p) q)))).
Qed.

Theorem pm2_48 : forall (p q : Prop), (impl (not (or p q)) (or p (not q))).
Proof.
    intros.
    exact (pm1_11 (pm1_3 p (not q)) (pm1_11 (pm2_46 p q) (syll (not (or p q)) (not q) (or p (not q))))).
Qed.

Theorem pm2_49 : forall (p q : Prop), (impl (not (or p q)) (or (not p) (not q))).
Proof.
    intros.
    exact (pm1_11 (pm2_2 (not p) (not q)) (pm1_11 (pm2_45 p q) (syll (not (or p q)) (not p) (or (not p) (not q))))).
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
    exact (pm1_11 (pm2_17 q p) (pm1_11 (pm2_52 p q) (syll (not (impl p q)) (impl (not p) (not q)) (impl q p)))).
Qed.

Theorem pm2_53 : forall (p q : Prop), (impl (or p q) (impl (not p) q)).
Proof.
    intros.
    exact (pm1_11 (pm2_12 p) (pm2_38 q p (not (not p)))).
Qed.

Theorem pm2_54 : forall (p q : Prop), (impl (impl (not p) q) (or p q)).
Proof.
    intros.
    exact (pm1_11 (pm2_14 p) (pm2_38 q (not (not p)) p)).
Qed.

Theorem pm2_55 : forall (p q : Prop), (impl (not p) (impl (or p q) q)).
Proof.
    intros.
    exact (pm1_11 (pm2_53 p q) (comm (or p q) (not p) q)).
Qed.

Theorem pm2_56 : forall (p q : Prop), (impl (not q) (impl (or p q) p)).
Proof.
    intros.
    exact (pm1_11 (pm1_11 (perm p q) (syll (or p q) (or q p) p)) (pm1_11 (pm2_55 q p) (syll (not q) (impl (or q p) p) (impl (or p q) p)))).
Qed.

Theorem pm2_6 : forall (p q : Prop), (impl (impl (not p) q) (impl (impl p q) q)).
Proof.
    intros.
    pose (S1 := (pm2_38 q (not p) q)).
    pose (S2 := (pm1_11 (taut q) (syllr (or (not p) q) (or q q) q))).
    exact (pm1_11 S2 (pm1_11 S1 (syll (impl (not p) q) (impl (or (not p) q) (or q q)) (impl (or (not p) q) q)))).
Qed.

Theorem pm2_61 : forall (p q : Prop), (impl (impl p q) (impl (impl (not p) q) q)).
Proof.
    intros.
    exact (pm1_11 (pm2_6 p q) (comm (impl (not p) q) (impl p q) q)).
Qed.

Theorem pm2_62 : forall (p q : Prop), (impl (or p q) (impl (impl p q) q)).
Proof.
    intros.
    exact (pm1_11 (pm2_6 p q) (pm1_11 (pm2_53 p q) (syll (or p q) (impl (not p) q) (impl (impl p q) q)))).
Qed.

Theorem pm2_621 : forall (p q : Prop), (impl (impl p q) (impl (or p q) q)).
Proof.
    intros.
    exact (pm1_11 (pm2_62 p q) (comm (or p q) (impl p q) q)).
Qed.

Theorem pm2_63 : forall (p q : Prop), (impl (or p q) (impl (or (not p) q) q)).
Proof.
    intros.
    exact (pm2_62 p q).
Qed.

Theorem pm2_64 : forall (p q : Prop), (impl (or p q) (impl (or p (not q)) p)).
Proof.
    intros.
    exact (pm1_11 (pm1_11 (pm1_11 (perm p (not q)) (syll (or p (not q)) (or (not q) p) p)) (pm1_11 (pm2_63 q p) (syll (or q p) (impl (or (not q) p) p) (impl (or p (not q)) p)))) (pm1_11 (perm p q) (syll (or p q) (or q p) (impl (or p (not q)) p)))).
Qed.

Theorem pm2_65 : forall (p q : Prop), (impl (impl p q) (impl (impl p (not q)) (not p))).
Proof.
    intros.
    exact (pm2_64 (not p) q).
Qed.

Theorem pm2_67 : forall (p q : Prop), (impl (impl (or p q) q) (impl p q)).
Proof.
    intros.
    pose (S1 := (pm1_11 (pm2_54 p q) (syll (impl (not p) q) (or p q) q))).
    pose (S2 := (pm1_11 (pm2_24 p q) (syll p (impl (not p) q) q))).
    exact (pm1_11 S2 (pm1_11 S1 (syll (impl (or p q) q) (impl (impl (not p) q) q) (impl p q)))).
Qed.

Theorem pm2_68 : forall (p q : Prop), (impl (impl (impl p q) q) (or p q)).
Proof.
    intros.
    pose (S1 := (pm2_67 (not p) q)).
    exact (pm1_11 (pm2_54 p q) (pm1_11 S1 (syll (impl (impl p q) q) (impl (not p) q) (or p q)))).
Qed.

Theorem pm2_69 : forall (p q : Prop), (impl (impl (impl p q) q) (impl (impl q p) p)).
Proof.
    intros.
    exact (pm1_11 (pm2_62 q p) (pm1_11 (pm1_11 (perm p q) (pm1_11 (pm2_68 p q) (syll (impl (impl p q) q) (or p q) (or q p)))) (syll (impl (impl p q) q) (or q p) (impl (impl q p) p)))).
Qed.

Theorem pm2_73 : forall (p q r : Prop), (impl (impl p q) (impl (or3 p q r) (or q r))).
Proof.
    intros.
    exact (pm1_11 (pm2_38 r (or p q) q) (pm1_11 (pm2_621 p q) (syll (impl p q) (impl (or p q) q) (impl (or3 p q r) (or q r))))).
Qed.

Theorem pm2_74 : forall (p q r : Prop), (impl (impl q p) (impl (or3 p q r) (or p r))).
Proof.
    intros.
    exact (pm1_11 (pm1_11 (pm1_11 (perm p q) (pm2_38 r (or p q) (or q p))) (syll (or3 p q r) (or3 q p r) (or p r))) (pm1_11 (pm2_73 q p r) (syll (impl q p) (impl (or3 q p r) (or p r)) (impl (or3 p q r) (or p r))))).
Qed.

Theorem pm2_75 : forall (p q r : Prop), (impl (or p q) (impl (or p (impl q r)) (or p r))).
Proof.
    intros.
    exact (pm1_11 (pm1_11 (pm2_31 p (not q) r) (syll (or p (impl q r)) (or3 p (not q) r) (or p r))) (pm1_11 (pm1_11 (pm1_11 (pm2_74 p (not q) r) (pm1_11 (pm2_53 q p) (syll (or q p) (impl (not q) p) (impl (or3 p (not q) r) (or p r))))) (pm1_11 (perm p q) (syll (or p q) (or q p) (impl (or3 p (not q) r) (or p r))))) (syll (or p q) (impl (or3 p (not q) r) (or p r)) (impl (or p (impl q r)) (or p r))))).
Qed.

Theorem pm2_76 : forall (p q r : Prop), (impl (or p (impl q r)) (impl (or p q) (or p r))).
Proof.
    intros.
    exact (pm1_11 (pm2_75 p q r) (comm (or p q) (or p (impl q r)) (or p r))).
Qed.

Theorem pm2_77 : forall (p q r : Prop), (impl (impl p (impl q r)) (impl (impl p q) (impl p r))).
Proof.
    intros.
    exact (pm2_76 (not p) q r).
Qed.

Theorem pm2_8 : forall (q r s : Prop), (impl (or q r) (impl (or (not r) s) (or q s))).
Proof.
    intros.
    pose (S1 := (pm1_11 (pm2_53 r q) (pm1_11 (perm q r) (syll (or q r) (or r q) (impl (not r) q))))).
    exact (pm1_11 (pm2_38 s (not r) q) (pm1_11 S1 (syll (or q r) (impl (not r) q) (impl (or (not r) s) (or q s))))).
Qed.

Theorem pm2_81 : forall (p q r s : Prop), (impl (impl q (impl r s)) (impl (or p q) (impl (or p r) (or p s)))).
Proof.
    intros.
    pose (S1 := (sum p q (impl r s))).
    pose (S2 := (pm1_11 (pm2_76 p r s) (syllr (or p q) (or p (impl r s)) (impl (or p r) (or p s))))).
    exact (pm1_11 S2 (pm1_11 S1 (syll (impl q (impl r s)) (impl (or p q) (or p (impl r s))) (impl (or p q) (impl (or p r) (or p s)))))).
Qed.

Theorem pm2_82 : forall (p q r s : Prop), (impl (or3 p q r) (impl (or3 p (not r) s) (or3 p q s))).
Proof.
    intros.
    exact (pm1_11 (pm1_11 (pm1_11 (pm1_11 (pm2_32 p (not r) s) (syll (or3 p (not r) s) (or p (or (not r) s)) (or3 p q s))) (pm1_11 (pm1_11 (pm2_31 p q s) (syllr (or p (or (not r) s)) (or p (or q s)) (or3 p q s))) (syll (impl (or p (or (not r) s)) (or p (or q s))) (impl (or p (or (not r) s)) (or3 p q s)) (impl (or3 p (not r) s) (or3 p q s))))) (pm1_11 (pm1_11 (pm2_8 q r s) (pm2_81 p (or q r) (or (not r) s) (or q s))) (syll (or p (or q r)) (impl (or p (or (not r) s)) (or p (or q s))) (impl (or3 p (not r) s) (or3 p q s))))) (pm1_11 (pm2_32 p q r) (syll (or3 p q r) (or p (or q r)) (impl (or3 p (not r) s) (or3 p q s))))).
Qed.

Theorem pm2_83 : forall (p q r s : Prop), (impl (impl p (impl q r)) (impl (impl p (impl r s)) (impl p (impl q s)))).
Proof.
    intros.
    exact (pm1_11 (pm1_11 (pm1_11 (pm1_11 (pm2_31 (not p) (not r) s) (syll (impl p (impl r s)) (or3 (not p) (not r) s) (impl p (impl q s)))) (pm1_11 (pm1_11 (pm2_32 (not p) (not q) s) (syllr (or3 (not p) (not r) s) (or3 (not p) (not q) s) (impl p (impl q s)))) (syll (impl (or3 (not p) (not r) s) (or3 (not p) (not q) s)) (impl (or3 (not p) (not r) s) (impl p (impl q s))) (impl (impl p (impl r s)) (impl p (impl q s)))))) (pm1_11 (pm2_82 (not p) (not q) r s) (syll (or3 (not p) (not q) r) (impl (or3 (not p) (not r) s) (or3 (not p) (not q) s)) (impl (impl p (impl r s)) (impl p (impl q s)))))) (pm1_11 (pm2_31 (not p) (not q) r) (syll (impl p (impl q r)) (or3 (not p) (not q) r) (impl (impl p (impl r s)) (impl p (impl q s)))))).
Qed.

Theorem pm2_85 : forall (p q r : Prop), (impl (impl (or p q) (or p r)) (or p (impl q r))).
Proof.
    intros.
    pose (S1 := (pm1_11 (add p q) (syll q (or p q) r))).
    pose (S2 := (pm2_55 p r)).
    pose (S3 := (pm1_11 (syllr (or p q) (or p r) r) (pm1_11 S2 (syll (not p) (impl (or p r) r) (impl (impl (or p q) (or p r)) (impl (or p q) r)))))).
    pose (S4 := (pm1_11 (pm1_11 S1 (syllr (impl (or p q) (or p r)) (impl (or p q) r) (impl q r))) (pm1_11 S3 (syll (not p) (impl (impl (or p q) (or p r)) (impl (or p q) r)) (impl (impl (or p q) (or p r)) (impl q r)))))).
    pose (S5 := (pm1_11 S4 (comm (not p) (impl (or p q) (or p r)) (impl q r)))).
    exact (pm1_11 (pm2_54 p (impl q r)) (pm1_11 S5 (syll (impl (or p q) (or p r)) (impl (not p) (impl q r)) (or p (impl q r))))).
Qed.

Theorem pm2_86 : forall (p q r : Prop), (impl (impl (impl p q) (impl p r)) (impl p (impl q r))).
Proof.
    intros.
    exact (pm2_85 (not p) q r).
Qed.
