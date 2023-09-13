Require Import Ltac2.Ltac2.
Require Import axiom.

Theorem scharle2 : forall (p q r s t : Prop), (stroke (stroke t (stroke s (stroke s s))) (stroke (stroke (stroke p (stroke q r)) t) (stroke (stroke p (stroke q r)) t))).
Proof.
    intros.
    pose (S1 := (scharle (stroke p (stroke q r)) (stroke s (stroke s s)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) t)).
    exact (mp (scharle p q r s) S1).
Qed.

Theorem scharle3 : forall (p q r s t w : Prop), (stroke (stroke w (stroke (stroke p (stroke q r)) t)) (stroke (stroke (stroke t (stroke s (stroke s s))) w) (stroke (stroke t (stroke s (stroke s s))) w))).
Proof.
    intros.
    pose (S1 := (scharle (stroke t (stroke s (stroke s s))) (stroke (stroke p (stroke q r)) t) (stroke (stroke p (stroke q r)) t) w)).
    exact (mp (scharle2 p q r s t) S1).
Qed.

Theorem scharle4 : forall (p q r s t : Prop), (stroke (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))) (stroke p (stroke q r))).
Proof.
    intros.
    pose (S1 := (scharle3 s s s t (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke p (stroke q r)))).
    exact (mp (scharle p q r s) S1).
Qed.

Theorem scharle5 : forall (p q r s t : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s t) (stroke (stroke t s) (stroke t s))) (stroke t (stroke t t)))).
Proof.
    intros.
    pose (S1 := (scharle2 p q r t (stroke (stroke (stroke s t) (stroke (stroke t s) (stroke t s))) (stroke t (stroke t t))))).
    exact (mp (scharle4 t t t s t) S1).
Qed.

Theorem scharle6 : forall (t : Prop), (stroke t (stroke t t)).
Proof.
    intros.
    pose (S1 := (scharle5 (stroke t (stroke t t)) (stroke (stroke t t) (stroke (stroke t t) (stroke t t))) (stroke t (stroke t t)) t t)).
    exact (mp (scharle5 t t t t t) S1).
Qed.

Theorem scharle7 : forall (s t : Prop), (stroke (stroke s t) (stroke (stroke t s) (stroke t s))).
Proof.
    intros.
    pose (S1 := (scharle t t t s)).
    exact (mp (scharle6 t) S1).
Qed.

Theorem scharle8 : forall (t : Prop), (stroke (stroke t t) t).
Proof.
    intros.
    pose (S1 := (scharle7 t (stroke t t))).
    exact (mp (scharle6 t) S1).
Qed.

Theorem scharle9 : forall (s t : Prop), (stroke (stroke (stroke t s) (stroke t s)) (stroke s t)).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke s t) (stroke (stroke t s) (stroke t s)))).
    exact (mp (scharle7 s t) S1).
Qed.

Theorem scharle10 : forall (p s t : Prop), (stroke (stroke p s) (stroke (stroke (stroke (stroke t s) (stroke t s)) p) (stroke (stroke (stroke t s) (stroke t s)) p))).
Proof.
    intros.
    pose (S1 := (scharle (stroke (stroke t s) (stroke t s)) s t p)).
    exact (mp (scharle9 s t) S1).
Qed.

Theorem scharle11 : forall (p s : Prop), (stroke (stroke (stroke s p) (stroke s p)) (stroke p p)).
Proof.
    intros.
    pose (S1 := (scharle10 (stroke p p) p s)).
    exact (mp (scharle8 p) S1).
Qed.

Theorem scharle12 : forall (p s : Prop), (stroke (stroke p p) (stroke (stroke s p) (stroke s p))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke s p) (stroke s p)) (stroke p p))).
    exact (mp (scharle11 p s) S1).
Qed.

Theorem scharle13 : forall (p r s : Prop), (stroke (stroke r (stroke s p)) (stroke (stroke (stroke p p) r) (stroke (stroke p p) r))).
Proof.
    intros.
    pose (S1 := (scharle (stroke p p) (stroke s p) (stroke s p) r)).
    exact (mp (scharle12 p s) S1).
Qed.

Theorem scharle14 : forall (p q r s : Prop), (stroke (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r))).
Proof.
    intros.
    pose (S1 := (scharle13 (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke p (stroke q r)) (stroke s (stroke s s)))).
    exact (mp (scharle p q r s) S1).
Qed.

Theorem scharle15 : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))(stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r)))).
    exact (mp (scharle14 p q r s) S1).
Qed.

Theorem scharle16 : forall (p s t : Prop), (stroke (stroke p (stroke t s)) (stroke (stroke (stroke s t) p) (stroke (stroke s t) p))).
Proof.
    intros.
    pose (S1 := (scharle15 (stroke s t) (stroke t s) (stroke t s) p)).
    exact (mp (scharle7 s t) S1).
Qed.

Theorem scharle17 : forall (p s t : Prop), (stroke (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)) (stroke p (stroke t s))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke p (stroke t s)) (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)))).
    exact (mp (scharle16 p s t) S1).
Qed.

Theorem scharle18 : forall (p s t : Prop), (stroke (stroke (stroke t s) p) (stroke (stroke (stroke s t) p) (stroke (stroke s t) p))).
Proof.
    intros.
    pose (S1 := (scharle16 (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)) (stroke t s) p)).
    exact (mp (scharle17 p s t) S1).
Qed.

Theorem scharle19 : forall (p s t : Prop), (stroke (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)) (stroke (stroke t s) p)).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke t s) p) (stroke (stroke (stroke s t) p) (stroke (stroke s t) p)))).
    exact (mp (scharle18 p s t) S1).
Qed.

Theorem scharle20 : forall (p q r s t : Prop), (stroke (stroke t (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke (stroke (stroke p (stroke q r)) t) (stroke (stroke p (stroke q r)) t))).
Proof.
    intros.
    pose (S1 := (scharle15 (stroke p (stroke q r)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) t)).
    exact (mp (scharle15 p q r s) S1).
Qed.

Theorem scharle21 : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))).
Proof.
    intros.
    pose (S1 := (scharle20 p q r s (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s)))))).
    exact (mp (scharle19 (stroke (stroke p s) (stroke p s)) q s) S1).
Qed.

Theorem scharle22 : forall (p s t : Prop), (stroke (stroke p s) (stroke (stroke (stroke (stroke t s) (stroke t s)) p) (stroke (stroke (stroke t s) (stroke t s)) p))).
Proof.
    intros.
    pose (S1 := (scharle (stroke (stroke t s) (stroke t s)) s t p)).
    exact (mp (scharle9 s t) S1).
Qed.

Theorem scharle23 : forall (p t : Prop), (stroke (stroke (stroke t (stroke p p)) (stroke t (stroke p p))) p).
Proof.
    intros.
    pose (S1 := (scharle22 p (stroke p p) t)).
    exact (mp (scharle6 p) S1).
Qed.

Theorem scharle24 : forall (p t : Prop), (stroke p (stroke (stroke t (stroke p p)) (stroke t (stroke p p)))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke t (stroke p p)) (stroke t (stroke p p))) p)).
    exact (mp (scharle23 p t) S1).
Qed.

Theorem scharle25 : forall (p q s t : Prop), (stroke (stroke q (stroke (stroke s t) p)) (stroke (stroke (stroke (stroke t s) p) q) (stroke (stroke (stroke t s) p ) q))).
Proof.
    intros.
    pose (S1 := (scharle (stroke (stroke t s) p) (stroke (stroke s t) p) (stroke (stroke s t) p) q)).
    exact (mp (scharle18 p s t) S1).
Qed.

Theorem scharle26 : forall (p s t : Prop), (stroke (stroke (stroke p (stroke s t)) (stroke (stroke s t) p)) (stroke p (stroke t s))).
Proof.
    intros.
    pose (S1 := (scharle25 (stroke (stroke s t) p) (stroke p (stroke t s)) (stroke s t) p)).
    exact (mp (scharle16 p s t) S1).
Qed.

Theorem scharle27 : forall (p s t : Prop), (stroke (stroke p (stroke t s)) (stroke (stroke p (stroke s t)) (stroke (stroke s t) p))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke p (stroke s t)) (stroke (stroke s t) p)) (stroke p (stroke t s)))).
    exact (mp (scharle26 p s t) S1).
Qed.

Theorem scharle28 : forall (p q s t : Prop), (stroke (stroke (stroke p (stroke s t)) q) (stroke (stroke (stroke p (stroke t s)) q) (stroke (stroke p (stroke t s)) q))).
Proof.
    intros.
    pose (S1 := (scharle21 (stroke p (stroke t s)) (stroke p (stroke s t)) (stroke (stroke s t) p) q)).
    exact (mp (scharle27 p s t) S1).
Qed.

Theorem scharle29 : forall (p q s t : Prop), (stroke (stroke (stroke t s) (stroke q p)) (stroke (stroke (stroke s t) (stroke p q)) (stroke (stroke s t) (stroke p q)))).
Proof.
    intros.
    pose (S1 := (scharle28 (stroke t s) (stroke (stroke (stroke s t) (stroke p q)) (stroke (stroke s t) (stroke p q))) p q)).
    exact (mp (scharle18 (stroke p q) s t) S1).
Qed.

Theorem scharle30 : forall (p q r s t : Prop), (stroke (stroke r (stroke (stroke s t) (stroke p q))) (stroke (stroke (stroke (stroke t s) (stroke q p)) r) (stroke (stroke (stroke t s) (stroke q p)) r))).
Proof.
    intros.
    pose (S1 := (scharle (stroke (stroke t s) (stroke q p)) (stroke (stroke s t) (stroke p q)) (stroke (stroke s t) (stroke p q)) r)).
    exact (mp (scharle29 p q s t) S1).
Qed.

Theorem scharle31 : forall (p s : Prop), (stroke (stroke (stroke (stroke p p) s) (stroke (stroke p p) s)) p).
Proof.
    intros.
    pose (S1 := (scharle30 s (stroke p p) p s (stroke p p))).
    exact (mp (scharle24 p s) S1).
Qed.

Theorem scharle32 : forall (p s : Prop), (stroke p (stroke (stroke (stroke p p) s) (stroke (stroke p p) s))).
Proof.
    intros.
    pose (S1 := (scharle7 (stroke (stroke (stroke p p) s) (stroke (stroke p p) s)) p)).
    exact (mp (scharle31 p s) S1).
Qed.
