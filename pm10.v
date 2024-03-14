Require Import Ltac2.Ltac2.
Require Import pm1.
Require Import axiom_pred.
Require Import pm2.
Require Import pm3.
Require Import pm4.

Section pm10.

Context {uni : Universe}.

Definition pimpl := fun (P Q : forall (_ : U), Prop) => (all (fun (x : U) => (impl (P x) (Q x)))).
Definition pbi := fun (P Q : forall (_ : U), Prop) => (all (fun (x : U) => (bi (P x) (Q x)))).

Theorem pm10_1 : forall (P : forall (_ : U), Prop) (x : U), (impl (all P) (P x)).
Proof.
    intros.
    exact (spec P x).
Qed.

Definition spec (P : forall (_ : U), Prop) (x : U) := (pm10_1 P x).

Theorem pm10_11 : forall {P : forall (_ : U), Prop} (H : forall (x : U), (P x)), (all P).
Proof.
    intros.
    enough (S1 : forall (x : U), (impl (impl (all P) (all P)) (P x))).
    pose (S2 := (gen S1)).
    exact (mp (id (all P)) S2).
    intros.
    exact (mp (H x) (pm2_02 (impl (all P) (all P)) (P x))).
Qed.

Definition gen {P : forall (_ : U), Prop} (H : forall (x : U), (P x)) := (pm10_11 H).

Theorem pm10_12 : forall (p : Prop) (Q : forall (_ : U), Prop), (impl (all (fun (x : U) => (or p (Q x)))) (or p (all Q))).
Proof.
    intros.
    enough (S1 : forall (R S : forall (_ : U), Prop), (impl (all (fun (x : U) => (impl (R x) (S x)))) (impl (all R) (all S)))).
    enough (S2 : (impl (all (fun (x : U) => (or p (Q x)))) (all (fun (x : U) => (impl (not p) (Q x)))))).
    enough (S3 : forall (x : U), (impl (and (all (fun (y : U) => (impl (not p) (Q y)))) (not p)) (Q x))).
    pose (S4 := (axiom_pred.gen S3)).
    pose (S5 := (mp S4 (exp (all (fun (x : U) => (impl (not p) (Q x)))) (not p) (all Q)))).
    pose (S6 := (mp (pm2_54 p (all Q)) (mp S5 (syll (all (fun (x : U) => (impl (not p) (Q x)))) (impl (not p) (all Q)) (or p (all Q)))))).
    exact (mp S6 (mp S2 (syll (all (fun (x : U) => (or p (Q x)))) (all (fun (x : U) => (impl (not p) (Q x)))) (or p (all Q))))).
    intros.
    pose (S3 := (spec (fun (y : U) => (impl (not p) (Q y))) x)).
    exact (mp S3 (imp (all (fun (y : U) => (impl (not p) (Q y)))) (not p) (Q x))).
    enough (S2 : forall (x : U), (impl (or p (Q x)) (impl (not p) (Q x)))).
    pose (S3 := (pm10_11 S2)).
    exact (mp S3 (S1 (fun (x : U) => (or p (Q x))) (fun (x : U) => (impl (not p) (Q x))))).
    intros.
    exact (pm2_53 p (Q x)).
    intros.
    enough (S1 : forall (x : U), (impl (and (all (fun (y : U) => (impl (R y) (S y)))) (all R)) (S x))).
    pose (S2 := (axiom_pred.gen S1)).
    exact (mp S2 (exp (all (fun (x : U) => (impl (R x) (S x)))) (all R) (all S))).
    intros.
    pose (S1 := (spec (fun (y : U) => (impl (R y) (S y))) x)).
    pose (S2 := (spec R x)).
    pose (S3 := (mp (pm3_03 S1 S2) (pm3_47 (all (fun (y : U) => (impl (R y) (S y)))) (all R) (impl (R x) (S x)) (R x)))).
    pose (S4 := (mp (pm3_22 (impl (R x) (S x)) (R x)) (mp S3 (syll (and (all (fun (y : U) => (impl (R y) (S y)))) (all R)) (and (impl (R x) (S x)) (R x)) (and (R x) (impl (R x) (S x))))))).
    exact (mp (ass (R x) (S x)) (mp S4 (syll (and (all (fun (y : U) => (impl (R y) (S y)))) (all R)) (and (R x) (impl (R x) (S x))) (S x)))).
Qed.

Theorem pm10_13 : forall (P Q : forall (_ : U), Prop) (x : U) (H0 : (P x)) (H1 : (Q x)), (and (P x) (Q x)).
Proof.
    intros.
    pose (S1 := (pm2_11 (or (not (P x)) (not (Q x))))).
    pose (S2 := (mp S1 (pm2_32 (not (P x)) (not (Q x)) (and (P x) (Q x))))).
    exact (mp H1 (mp H0 S2)).
Qed.

Theorem pm10_14 : forall (P Q : forall (_ : U), Prop) (x : U), (impl (and (all P) (all Q)) (and (P x) (Q x))).
Proof.
    intros.
    pose (S1 := (pm10_1 P x)).
    pose (S2 := (pm10_1 Q x)).
    pose (S3 := (pm10_13 (fun (y : U) => (impl (all P) (P y))) (fun (y : U) => (impl (all Q) ( Q y))) x S1 S2)).
    exact (mp S3 (pm3_47 (all P) (all Q) (P x) (Q x))).
Qed.

Theorem pm10_2 : forall (p : Prop) (Q : forall (_ : U), Prop), (bi (all (fun (x : U) => (or p (Q x)))) (or p (all Q))).
Proof.
    intros.
    enough (S1 : forall (x : U), (impl (or p (all Q)) (or p (Q x)))).
    pose (S2 := (pm10_11 S1)).
    pose (S3 := (mp S2 (pm10_12 (not (or p (all Q))) (fun (x : U) => (or p (Q x)))))).
    pose (S4 := (pm10_12 p Q)).
    exact (pm3_03 S4 S3).
    intros.
    exact (mp (pm10_1 Q x) (pm1_6 p (all Q) (Q x))).
Qed.

Theorem pm10_21 : forall (p : Prop) (Q : forall (_ : U), Prop), (bi (all (fun (x : U) => (impl p (Q x)))) (impl p (all Q))).
Proof.
    intros.
    exact (pm10_2 (not p) Q).
Qed.

Theorem pm10_22 : forall (P Q : forall (_ : U), Prop), (bi (all (fun (x : U) => (and (P x) (Q x)))) (and (all P) (all Q))).
Proof.
    intros.
    enough (S1 : forall (x : U), (impl (all (fun (y : U) => (and (P y) (Q y)))) (and (P x) (Q x)))).
    enough (S2 : forall (x : U), (impl (all (fun (y : U) => (and (P y) (Q y)))) (P x))).
    pose (S3 := (pm10_11 S2)).
    pose (S4 := (mp S3 (mp (pm10_21 (all (fun (x : U) => (and (P x) (Q x)))) P) (simpl (impl (all (fun (x : U) => (impl (all (fun (y : U) => (and (P y) (Q y)))) (P x)))) (impl (all (fun (x : U) => (and (P x) (Q x)))) (all P))) (impl (impl (all (fun (x : U) => (and (P x) (Q x)))) (all P)) (all (fun (x : U) => (impl (all (fun (y : U) => (and (P y) (Q y)))) (P x))))))))).
    enough (S5 : forall (x : U), (impl (all (fun (y : U) => (and (P y) (Q y)))) (Q x))).
    pose (S6 := (pm10_11 S5)).
    pose (S7 := (mp S6 (mp (pm10_21 (all (fun (x : U) => (and (P x) (Q x)))) Q) (simpl (impl (all (fun (x : U) => (impl (all (fun (y : U) => (and (P y) (Q y)))) (Q x)))) (impl (all (fun (x : U) => (and (P x) (Q x)))) (all Q))) (impl (impl (all (fun (x : U) => (and (P x) (Q x)))) (all Q)) (all (fun (x : U) => (impl (all (fun (y : U) => (and (P y) (Q y)))) (Q x))))))))).
    pose (S8 := (mp (pm3_03 S4 S7) (comp (all (fun (x : U) => (and (P x) (Q x)))) (all P) (all Q)))).
    enough (S9 : forall (x : U), (impl (and (all P) (all Q)) (and (P x) (Q x)))).
    pose (S10 := (pm10_11 S9)).
    pose (S11 := (mp S10 (mp (pm10_21 (and (all P) (all Q)) (fun (x : U) => (and (P x) (Q x)))) (simpl (impl (all (fun (x : U) => (impl (and (all P) (all Q)) (and (P x) (Q x))))) (impl (and (all P) (all Q)) (all (fun (x : U) => (and (P x) (Q x)))))) (impl (impl (and (all P) (all Q)) (all (fun (x : U) => (and (P x) (Q x))))) (all (fun (x : U) => (impl (and (all P) (all Q)) (and (P x) (Q x)))))))))).
    exact (pm3_03 S8 S11).
    intros.
    exact (pm10_14 P Q x).
    intros.
    exact (mp (pm3_27 (P x) (Q x)) (mp (S1 x) (syll (all (fun (y : U) => (and (P y) (Q y)))) (and (P x) (Q x)) (Q x)))).
    intros.
    exact (mp (pm3_26 (P x) (Q x)) (mp (S1 x) (syll (all (fun (y : U) => (and (P y) (Q y)))) (and (P x) (Q x)) (P x)))).
    intros.
    exact (pm10_1 (fun (y : U) => (and (P y) (Q y))) x).
Qed.

Theorem pm10_23 : forall (P : forall (_ : U), Prop) (q : Prop), (bi (all (fun (x : U) => (impl (P x) q))) (impl (ex P) q)).
Proof.
    intros.
    pose (S1 := (transp2 (all (fun (x : U) => (not (P x)))) q)).
    pose (S2 := (mp (mp (pm10_21 (not q) (fun (x : U) => (not (P x)))) (simpr (impl (all (fun (x : U) => (impl (not q) (not (P x))))) (impl (not q) (all (fun (x : U) => (not (P x)))))) (impl (impl (not q) (all (fun (x : U) => (not (P x))))) (all (fun (x : U) => (impl (not q) (not (P x)))))))) (mp S1 (syll (impl (ex P) q) (impl (not q) (all (fun (x : U) => (not (P x))))) (all (fun (x : U) => (impl (not q) (not (P x))))))))).
    enough (S3 : forall (x : U), (impl (impl (ex P) q) (impl (not q) (not (P x))))).
    enough (S4 : forall (x : U), (impl (impl (ex P) q) (impl (P x) q))).
    pose (S5 := (pm10_11 S4)).
    pose (S6 := (mp S5 (mp (pm10_21 (impl (ex P) q) (fun (x : U) => (impl (P x) q))) (simpl (impl (all (fun (x : U) => (impl (impl (ex P) q) (impl (P x) q)))) (impl (impl (ex P) q) (all (fun (x : U) => (impl (P x) q))))) (impl (impl (impl (ex P) q) (all (fun (x : U) => (impl (P x) q)))) (all (fun (x : U) => (impl (impl (ex P) q) (impl (P x) q))))))))).
    enough (S7 : forall (x : U), (impl (all (fun (y : U) => (impl (P y) q))) (impl (P x) q))).
    enough (S8 : forall (x : U), (impl (all (fun (y : U) => (impl (P y) q))) (impl (not q) (not (P x))))).
    pose (S9 := (mp (gen S8) (mp (pm10_21 (all (fun (x : U) => (impl (P x) q))) (fun (x : U) => (impl (not q) (not (P x))))) (simpl (impl (all (fun (x : U) => (impl (all (fun (y : U) => (impl (P y) q))) (impl (not q) (not (P x)))))) (impl (all (fun (x : U) => (impl (P x) q))) (all (fun (x : U) => (impl (not q) (not (P x))))))) (impl (impl (all (fun (x : U) => (impl (P x) q))) (all (fun (x : U) => (impl (not q) (not (P x)))))) (all (fun (x : U) => (impl (all (fun (y : U) => (impl (P y) q))) (impl (not q) (not (P x))))))))))).
    pose (S10 := (mp (mp (pm10_21 (not q) (fun (x : U) => (not (P x)))) (simpl (impl (all (fun (x : U) => (impl (not q) (not (P x))))) (impl (not q) (all (fun (x : U) => (not (P x)))))) (impl (impl (not q) (all (fun (x : U) => (not (P x))))) (all (fun (x : U) => (impl (not q) (not (P x)))))))) (mp S9 (syll (all (fun (x : U) => (impl (P x) q))) (all (fun (x : U) => (impl (not q) (not (P x))))) (impl (not q) (all (fun (x : U) => (not (P x))))))))).
    pose (S11 := (mp (transp2 q (all (fun (x : U) => (not (P x))))) (mp S10 (syll (all (fun (x : U) => (impl (P x) q))) (impl (not q) (all (fun (x : U) => (not (P x))))) (impl (ex P) q))))).
    exact (pm3_03 S11 S6).
    intros.
    exact (mp (transp0 (P x) q) (mp (S7 x) (syll (all (fun (y : U) => (impl (P y) q))) (impl (P x) q) (impl (not q) (not (P x)))))).
    intros.
    exact (pm10_1 (fun (y : U) => (impl (P y) q)) x).
    intros.
    exact (mp (transp3 (P x) q) (mp (S3 x) (syll (impl (ex P) q) (impl (not q) (not (P x))) (impl (P x) q)))).
    intros.
    exact (mp (pm10_1 (fun (y : U) => (impl (not q) (not (P y)))) x) (mp S2 (syll (impl (ex P) q) (all (fun (y : U) => (impl (not q) (not (P y))))) (impl (not q) (not (P x)))))).
Qed.

Theorem pm10_24 : forall (P : forall (_ : U), Prop) (x : U), (impl (P x) (ex P)).
Proof.
    intros.
    pose (S1 := (pm10_1 (fun (y : U) => (not (P y))) x)).
    exact (mp S1 (transp1 (all (fun (y : U) => (not (P y)))) (P x))).
Qed.

Theorem pm10_25 : forall {p : Prop} (H : (ex (fun (x : U) => p))) (Q : forall (_ : U), Prop), (impl (all Q) (ex Q)).
Proof.
    intros.
    enough (S1 : forall (x : U), (impl (all Q) (ex Q))).
    enough (S2 : forall (x : U), (impl p (impl (all Q) (ex Q)))).
    pose (S3 := (gen S2)).
    pose (S4 := (pm10_23 (fun (x : U) => p) (impl (all Q) (ex Q)))).
    pose (S5 := (mp S4 (simpl (impl (all (fun (x : U) => (impl p (impl (all Q) (ex Q))))) (impl (ex (fun (x : U) => p)) (impl (all Q) (ex Q)))) (impl (impl (ex (fun (x : U) => p)) (impl (all Q) (ex Q))) (all (fun (x : U) => (impl p (impl (all Q) (ex Q))))))))).
    pose (S6 := (mp S3 S5)).
    exact (mp H S6).
    intros.
    exact (mp (S1 x) (pm2_02 p (impl (all Q) (ex Q)))).
    intros.
    exact (mp (pm10_24 Q x) (mp (pm10_1 Q x) (syll (all Q) (Q x) (ex Q)))).
Qed.

Theorem pm10_251 : forall {p : Prop} (H : (ex (fun (x : U) => p))) (Q : forall (_ : U), Prop), (impl (all (fun (x : U) => (not (Q x)))) (not (all Q))).
Proof.
    intros.
    exact (mp (pm10_25 H Q) (transp1 (all Q) (all (fun (x : U) => (not (Q x)))))).
Qed.

Theorem pm10_252 : forall (P : forall (_ : U), Prop), (bi (not (ex P)) (all (fun (x : U) => (not (P x))))).
Proof.
    intros.
    exact (mp (pm4_13 (all (fun (x : U) => (not (P x))))) (mp (pm4_21 (all (fun (x : U) => (not (P x)))) (not (ex P))) (simpl (impl (bi (all (fun (x : U) => (not (P x)))) (not (ex P))) (bi (not (ex P)) (all (fun (x : U) => (not (P x)))))) (impl (bi (not (ex P)) (all (fun (x : U) => (not (P x))))) (bi (all (fun (x : U) => (not (P x)))) (not (ex P))))))).
Qed.

Theorem pm10_253 : forall (P : forall (_ : U), Prop), (bi (not (all P)) (ex (fun (x : U) => (not (P x))))).
Proof.
Admitted.

Theorem pm10_26 : forall (P Q : forall (_ : U), Prop) (x : U), (impl (and (all (fun (y : U) => (impl (P y) (Q y)))) (P x)) (Q x)).
Proof.
Admitted.

Theorem pm10_27 : forall (P Q : forall (_ : U), Prop), (impl (all (fun (x : U) => (impl (P x) (Q x)))) (impl (all P) (all Q))).
Proof.
Admitted.

Theorem pm10_271 : forall (P Q : forall (_ : U), Prop), (impl (all (fun (x : U) => (bi (P x) (Q x)))) (bi (all P) (all Q))).
Proof.
Admitted.

Theorem pm10_28 : forall (P Q : forall (_ : U), Prop), (impl (all (fun (x : U) => (impl (P x) (Q x)))) (impl (ex P) (ex Q))).
Proof.
Admitted.

Theorem pm10_281 : forall (P Q : forall (_ : U), Prop), (impl (all (fun (x : U) => (bi (P x) (Q x)))) (bi (ex P) (ex Q))).
Proof.
Admitted.

Theorem pm10_29 : forall (P Q R : forall (_ : U), Prop), (bi (and (all (fun (x : U) => (impl (P x) (Q x)))) (all (fun (x : U) => (impl (P x) (R x))))) (all (fun (x : U) => (impl (P x) (and (Q x) (R x)))))).
Proof.
Admitted.

Theorem pm10_3 : forall (P Q R : forall (_ : U), Prop), (impl (and (all (fun (x : U) => (impl (P x) (Q x)))) (all (fun (x : U) => (impl (Q x) (R x))))) (all (fun (x : U) => (impl (P x) (R x))))).
Proof.
Admitted.

Theorem pm10_301 : forall (P Q R : forall (_ : U), Prop), (impl (and (all (fun (x : U) => (bi (P x) (Q x)))) (all (fun (x : U) => (bi (Q x) (R x))))) (all (fun (x : U) => (bi (P x) (R x))))).
Proof.
Admitted.

Theorem pm10_31 : forall (P Q R : forall (_ : U), Prop), (impl (all (fun (x : U) => (impl (P x) (Q x)))) (all (fun (x : U) => (impl (and (P x) (R x)) (and (Q x) (R x)))))).
Proof.
Admitted.

Theorem pm10_311 : forall (P Q R : forall (_ : U), Prop), (impl (all (fun (x : U) => (bi (P x) (Q x)))) (all (fun (x : U) => (bi (and (P x) (R x)) (and (Q x) (R x)))))).
Proof.
Admitted.

Theorem pm10_32 : forall (P Q : forall (_ : U), Prop), (bi (pbi P Q) (pbi Q P)).
Proof.
Admitted.

Theorem pm10_321 : forall (P Q R : forall (_ : U), Prop), (impl (and (pbi P Q) (pbi P R)) (pbi Q R)).
Proof.
Admitted.

Theorem pm10_322 : forall (P Q R : forall (_ : U), Prop), (impl (and (pbi Q P) (pbi R P)) (pbi Q R)).
Proof.
Admitted.

Theorem pm10_33 : forall (P : forall (_ : U), Prop) (q : Prop), (bi (all (fun (x : U) => (and (P x) q))) (and (all P) q)).
Proof.
Admitted.

Theorem pm10_34 : forall (P : forall (_ : U), Prop) (q : Prop), (bi (ex (fun (x : U) => (impl (P x) q))) (impl (all P) q)).
Proof.
Admitted.

Theorem pm10_35 : forall (p : Prop) (Q : forall (_ : U), Prop), (bi (ex (fun (x : U) => (and p (Q x)))) (and p (ex Q))).
Proof.
Admitted.

Theorem pm10_36 : forall (P : forall (_ : U), Prop) (q : Prop), (bi (ex (fun (x : U) => (or (P x) q))) (or (ex P) q)).
Proof.
Admitted.

Theorem pm10_37 : forall (p : Prop) (Q : forall (_ : U), Prop), (bi (ex (fun (x : U) => (impl p (Q x)))) (impl p (ex Q))).
Proof.
Admitted.

Theorem pm10_39 : forall (P Q R S : forall (_ : U), Prop), (impl (and (pimpl P R) (pimpl Q S)) (pimpl (fun (x : U) => (and (P x) (Q x))) (fun (x : U) => (and (R x) (S x))))).
Proof.
Admitted.

Theorem pm10_4 : forall (P Q R S : forall (_ : U), Prop), (impl (and (pbi P R) (pbi Q S)) (pbi (fun (x : U) => (and (P x) (Q x))) (fun (x : U) => (and (R x) (S x))))).
Proof.
Admitted.

Theorem pm10_41 : forall (P Q : forall (_ : U), Prop), (impl (or (all P) (all Q)) (all (fun (x : U) => (or (P x) (Q x))))).
Proof.
Admitted.

Theorem pm10_411 : forall (P Q R S : forall (_ : U), Prop), (impl (and (pbi P R) (pbi Q S)) (pbi (fun (x : U) => (or (P x) (Q x))) (fun (x : U) => (or (R x) (S x))))).
Proof.
Admitted.

Theorem pm10_412 : forall (P Q : forall (_ : U), Prop), (bi (pbi P Q) (pbi (fun (x : U) => (not (P x))) (fun (x : U) => (not (Q x))))).
Proof.
Admitted.

Theorem pm10_413 : forall (P Q R S : forall (_ : U), Prop), (impl (and (pbi P R) (pbi Q S)) (pbi (fun (x : U) => (impl (P x) (Q x))) (fun (x : U) => (impl (R x) (S x))))).
Proof.
Admitted.

Theorem pm10_414 : forall (P Q R S : forall (_ : U), Prop), (impl (and (pbi P R) (pbi Q S)) (pbi (fun (x : U) => (bi (P x) (Q x))) (fun (x : U) => (bi (R x) (S x))))).
Proof.
Admitted.

Theorem pm10_42 : forall (P Q : forall (_ : U), Prop), (bi (or (ex P) (ex Q)) (ex (fun (x : U) => (or (P x) (Q x))))).
Proof.
Admitted.

Theorem pm10_43 : forall (P Q : forall (_ : U), Prop) (x : U), (bi (and (pbi P Q) (P x)) (and (pbi P Q) (Q x))).
Proof.
Admitted.

Theorem pm10_5 : forall (P Q : forall (_ : U), Prop), (impl (ex (fun (x : U) => (and (P x) (Q x)))) (and (ex P) (ex Q))).
Proof.
Admitted.

Theorem pm10_51 : forall (P Q : forall (_ : U), Prop), (bi (not (ex (fun (x : U) => (and (P x) (Q x))))) (pimpl P (fun (x : U) => (not (Q x))))).
Proof.
Admitted.

Theorem pm10_52 : forall (P : forall (_ : U), Prop) (q : Prop), (impl (ex P) (bi (all (fun (x : U) => (impl (P x) q))) q)).
Proof.
Admitted.

Theorem pm10_53 : forall (P Q : forall (_ : U), Prop), (impl (not (ex P)) (pimpl P Q)).
Proof.
Admitted.

Theorem pm10_541 : forall (Q R : forall (_ : U), Prop) (p : Prop), (bi (pimpl Q (fun (x : U) => (or p (R x)))) (or p (pimpl Q R))).
Proof.
Admitted.

Theorem pm10_542 : forall (Q R : forall (_ : U), Prop) (p : Prop), (bi (pimpl Q (fun (x : U) => (impl p (R x)))) (impl p (pimpl Q R))).
Proof.
Admitted.

Theorem pm10_55 : forall (P Q : forall (_ : U), Prop), (bi (and (ex (fun (x : U) => (and (P x) (Q x)))) (pimpl P Q)) (and (ex P) (pimpl P Q))).
Proof.
Admitted.

Theorem pm10_56 : forall (P Q R : forall (_ : U), Prop), (impl (and (pimpl P Q) (ex (fun (x : U) => (and (P x) (R x))))) (ex (fun (x : U) => (and (Q x) (R x))))).
Proof.
Admitted.

Theorem pm10_57 : forall (P Q R : forall (_ : U), Prop), (impl (pimpl P (fun (x : U) => (or (Q x) (R x)))) (or (pimpl P Q) (ex (fun (x : U) => (and (P x) (R x)))))).
Proof.
Admitted.

End pm10.
