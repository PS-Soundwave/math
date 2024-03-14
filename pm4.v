Require Import Ltac2.Ltac2.
Require Import pm1.
Require Import pm2.
Require Import pm3.

Definition bi := fun (p q : Prop) => (and (impl p q) (impl q p)).
Definition bi3 := fun (p q r : Prop) => (and (bi p q) (bi q r)).

Theorem pm4_1 : forall (p q : Prop), (bi (impl p q) (impl (not q) (not p))).
Proof.
    intros.
    exact (pm3_03 (pm2_16 p q) (pm2_17 p q)).
Qed.

Theorem pm4_11 : forall (p q : Prop), (bi (bi p q) (bi (not p) (not q))).
Proof.
    intros.
    exact (pm3_03 (mp (pm3_22 (impl (not q) (not p)) (impl (not p) (not q))) (mp (mp (pm3_03 (pm2_16 p q) (pm2_16 q p)) (pm3_47 (impl p q) (impl q p) (impl (not q) (not p)) (impl (not p) (not q)))) (syll (bi p q) (bi (not q) (not p)) (bi (not p) (not q))))) (mp (pm3_22 (impl q p) (impl p q)) (mp (mp (pm3_03 (pm2_17 q p) (pm2_17 p q)) (pm3_47 (impl (not p) (not q)) (impl (not q) (not p)) (impl q p) (impl p q))) (syll (bi (not p) (not q)) (bi q p) (bi p q))))).
Qed.

Theorem pm4_12 : forall (p q : Prop), (bi (bi p (not q)) (bi q (not p))).
Proof.
    intros.
    exact (pm3_03 (mp (pm3_03 (pm2_03 p q) (pm2_15 q p)) (pm3_47 (impl p (not q)) (impl (not q) p) (impl q (not p)) (impl (not p) q))) (mp (pm3_03 (pm2_03 q p) (pm2_15 p q)) (pm3_47 (impl q (not p)) (impl (not p) q) (impl p (not q)) (impl (not q) p)))).
Qed.

Theorem pm4_13 : forall (p : Prop), (bi p (not (not p))).
Proof.
    intros.
    exact (pm3_03 (pm2_12 p) (pm2_14 p)).
Qed.

Theorem pm4_14 : forall (p q r : Prop), (bi (impl (and p q) r) (impl (and p (not r)) (not q))).
Proof.
    intros.
    enough (S1 : (impl (impl (and p q) r) (impl (and p (not r)) (not q)))).
    enough (S2 : (impl (impl (and p (not r)) (not q)) (impl (and p q) r))).
    exact (pm3_03 S1 S2).
Admitted.

Theorem pm4_15 : forall (p q r : Prop), (bi (impl (and p q) (not r)) (impl (and q r) (not p))).
Proof.
Admitted.

Theorem pm4_2 : forall (p : Prop), (bi p p).
Proof.
Admitted.

Theorem pm4_21 : forall (p q : Prop), (bi (bi p q) (bi q p)).
Proof.
Admitted.

Theorem pm4_22 : forall (p q r : Prop), (impl (and (bi p q) (bi q r)) (bi p q)).
Proof.
Admitted.

Theorem pm4_24 : forall (p : Prop), (bi p (and p p)).
Proof.
Admitted.

Theorem pm4_25 : forall (p : Prop), (bi p (or p p)).
Proof.
Admitted.

Theorem pm4_3 : forall (p q : Prop), (bi (and p q) (and q p)).
Proof.
Admitted.

Theorem pm4_31 : forall (p q : Prop), (bi (or p q) (or q p)).
Proof.
Admitted.

Theorem pm4_32 : forall (p q r : Prop), (bi (and (and p q) r) (and p (and q r))).
Proof.
Admitted.

Theorem pm4_33 : forall (p q r : Prop), (bi (or (or p q) r) (or p (or q r))).
Proof.
Admitted.

Theorem pm4_36 : forall (p q r : Prop), (impl (bi p q) (bi (and p r) (and q r))).
Proof.
Admitted.

Theorem pm4_37 : forall (p q r : Prop), (impl (bi p q) (bi (or p r) (or q r))).
Proof.
Admitted.

Theorem pm4_38 : forall (p q r s : Prop), (impl (and (bi p r) (bi q s)) (bi (and p q) (and r s))).
Proof.
Admitted.

Theorem pm4_39 : forall (p q r s : Prop), (impl (and (bi p r) (bi q s)) (bi (or p q) (or r s))).
Proof.
Admitted.

Theorem pm4_4 : forall (p q r : Prop), (bi (and p (or q r)) (or (and p q) (and p r))).
Proof.
Admitted.

Theorem pm4_41 : forall (p q r : Prop), (bi (or p (and q r)) (or (and p q) (and p r))).
Proof.
Admitted.

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

Theorem pm4_57 : forall (p q : Prop), (bi (not (and (not p) (not q))) (not (or p q))).
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

Theorem pm4_77 : forall (p q r : Prop), (bi (and (impl q p) (impl r p)) (impl (or q r) p)).
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
