Require Import Ltac2.Ltac2.
Require Import natural_deduction.

Module constructive_set_theory.

Inductive Pi (A : Type) (B : forall (_ : A), Type) :=
| Pii : forall (f : forall (a : A), (B a)), (Pi A B).

(*Definition pii := fun {A : Type} {B : forall (_ : A), Type} (f : forall (a : A), (B a)) => (Pii A B f).
Definition pie := fun {A : Type} {B : forall (_ : A), Type} (t : (Pi A B)) => (match t with | Pii _ _ f => f end).
*)
Inductive Sigma (A : Type) (B : forall (_ : A), Type) :=
| Sigmai : forall (a : A) (b : (B a)), (Sigma A B).

Definition sigmael := fun {A : Type} {B : forall (_ : A), Type} (t : (Sigma A B)) => (match t with | (Sigmai _ _ a _) => a end).

Inductive Impl (A B : Type) :=
| Impli : forall (f : forall (_ : A), B), (Impl A B).

Definition imple := fun {A B : Type} (t : (Impl A B)) => (match t with | (Impli _ _ f) => f end).

Inductive Product (A B : Type) :=
| Producti : forall (a : A) (b : B), (Product A B).
(*
Definition producti := fun {A B : Type} (a : A) (b : B) => (Producti A B a b).
Definition productel := fun {A B : Type} (t : (Product A B)) => (match t with | (Producti _ _ a _) => a end).
Definition producter := fun {A B : Type} (t : (Product A B)) => (match t with | (Producti _ _ _ b) => b end).
*)
Inductive Sum (A B : Type) :=
| Sumil : forall (_ : A), (Sum A B)
| Sumir : forall (_ : B), (Sum A B).
(*
Definition sumil := fun {A : Type} (a : A) (B : Type) => (Sumil A B a).
Definition sumir := fun (A : Type) {B : Type} (b : B) => (Sumir A B b).
Definition sume := fun {A B : Type} (t : (Sum A B)) (C : forall (_ : (Sum A B)), Type) (f : forall (a : A), (C (sumil a B))) (g : forall (b : B), (C (sumir A b))) => (match t return (C t) with | Sumil _ _ a => (f a) | Sumir _ _ b => (g b) end).
Definition sumre := fun {A B C : Type} (t : (Sum A B)) (f : forall (_ : A), C) (g : forall (_ : B), C) => (sume t (fun (_ : (Sum A B)) => C) f g).
*)

Inductive False :=.

Inductive Bool :=
| boolt : Bool
| boolf : Bool.

Definition boole := fun (b : Bool) (A : forall (_ : Bool), Type) (B : (A boolt)) (C : (A boolf)) => (match b return (A b) with | boolt => B | boolf => C end).
Definition boolre := fun {A : Type} (b : Bool) (B : A) (C : A) => (boole b (fun (_ : Bool) => A) B C).

Inductive V :=
| sup : forall (A : Type) (_ : forall (_ : A), V), V.

Definition bar := fun (x : V) => (match x with | (sup A _) => A end).
Definition tilde := fun (x : V) => (match x return forall (_ : (bar x)), V with | (sup _ f) => f end).

Definition Not := fun (A : Type) => (Impl A False).

Definition Eq := fix f (x : V) := fun (y : V) => (Product (Pi (bar x) (fun (z : (bar x)) => (Sigma (bar y) (fun (w : (bar y)) => (f ((tilde x) z) ((tilde y) w)))))) (Pi (bar y) (fun (w : (bar y)) => (Sigma (bar x) (fun (z : (bar x)) => (f ((tilde x) z) ((tilde y) w))))))).
(*
Theorem refl : forall (x : V), (Eq x x).
Proof.
    exact (fix f (x : V) : (Eq x x) := (match x with | (sup A g) => (producti (pii (fun (y : A) => (sigmai (fun (z : A) => (Eq (g y) (g z))) y (f (g y))))) (pii (fun (z : A) => (sigmai (fun (y : A) => (Eq (g y) (g z))) z (f (g z)))))) end)).
Defined.

Theorem sym : forall (x y : V), (Pi (Eq x y) (fun (_ : (Eq x y)) => (Eq y x))).
Proof.
    exact (fix f (x : V) : forall (y : V), (Pi (Eq x y) (fun (_ : (Eq x y)) => (Eq y x))) := fun (y : V) => (match x with | (sup A g) => (match y with | (sup B h) => (pii (fun (H : (Eq (sup A g) (sup B h))) => (producti (pii (fun (z : B) => (sigmai (fun (w : A) => (Eq (h z) (g w))) (sigmael ((pie (producter H)) z)) ((pie (f (g (sigmael ((pie (producter H)) z))) (h z))) (sigmaer ((pie (producter H)) z)))))) (pii (fun (w : A) => (sigmai (fun (z : B) => (Eq (h z) (g w))) (sigmael ((pie (productel H)) w)) ((pie (f (g w) (h (sigmael (pie (productel H) w))))) (sigmaer ((pie (productel H)) w))))))))) end) end)).
Defined.

Theorem symi : forall {x y : V} (H : (Eq x y)), (Eq y x).
Proof.
    intros.
    exact ((pie (sym x y)) H).
Qed.

Theorem trans : forall (x y z : V), (Impl (Product (Eq x y) (Eq y z)) (Eq x z)).
Proof.
    exact (fix f (x : V) : forall (y z : V), (Impl (Product (Eq x y) (Eq y z)) (Eq x z)) := fun (y z : V) => (match x with | (sup A g) => (match y with | (sup B h) => (impli (fun (H : (Product (Eq (sup A g) (sup B h)) (Eq (sup B h) z))) => (producti (pii (fun (w : A) => (sigmai (fun (v : (bar z)) => (Eq (g w) ((tilde z) v))) (sigmael ((pie (productel (producter H))) (sigmael ((pie (productel (productel H))) w)))) ((imple (f (g w) (h (sigmael ((pie (productel (productel H))) w))) ((tilde z) (sigmael ((pie (productel (producter H))) (sigmael ((pie (productel (productel H))) w))))))) (producti (sigmaer ((pie (productel (productel H))) w)) (sigmaer ((pie (productel (producter H))) (sigmael ((pie (productel (productel H))) w))))))))) (pii (fun (v : (bar z)) => (sigmai (fun (w : A) => (Eq (g w) ((tilde z) v))) (sigmael ((pie (producter (productel H))) (sigmael ((pie (producter (producter H))) v)))) ((imple (f (g (sigmael ((pie (producter (productel H))) (sigmael ((pie (producter (producter H))) v))))) (h (sigmael ((pie (producter (producter H))) v))) ((tilde z) v))) (producti (sigmaer ((pie (producter (productel H))) (sigmael ((pie (producter (producter H))) v)))) (sigmaer ((pie (producter (producter H))) v)))))))))) end) end)).
Defined.

Theorem transi : forall {x y z : V} (H1 : (Eq x y)) (H2 : (Eq y z)), (Eq x z).
Proof.
    intros.
    exact ((imple (trans x y z)) (producti H1 H2)).
Qed.
*)
Definition El := fun (x y : V) => (Sigma (bar y) (fun (z : (bar y)) => (Eq x ((tilde y) z)))).
(*Definition Sub := fun (x y : V) => (Pi (bar x) (fun (z : (bar x)) => (El ((tilde x) z) y))).
*)
Definition Pair := fun (x y : V) => (sup Bool (fun (b : Bool) => (boolre b x y))).
(*Definition Sep := fun (x : V) (F : forall (_ : (bar x)), Type) => (sup (Sigma (bar x) (fun (y : (bar x)) => (F y))) (fun (H : (Sigma (bar x) (fun (y : (bar x)) => (F y)))) => ((tilde x) (sigmael H)))).
Definition Rep := fun (x : V) (f : forall (_ : (bar x)), V) => (sup (bar x) (fun (z : (bar x)) => (f z))).
Definition Full := fun (x y : V) => (sup (Impl (bar x) (bar y)) (fun (f : (Impl (bar x) (bar y))) => (sup (bar x) (fun (z : (bar x)) => ((tilde y) ((imple f) z)))))).
*)

Definition Singleton := fun (x : V) => (Pair x x).
Definition OPair := fun (x y : V) => (Pair (Singleton x) (Pair x y)).

Inductive Class :=
| classi : forall (_ : forall (_ : V), Type), Class.

Definition CEl := fun (x : V) (y : Class) => (match y with | (classi P) => (P x) end).

Definition Rel := fun (R : V) => (Pi (bar R) (fun (r : (bar R)) => (Sigma V (fun (x : V) => (Sigma V (fun (y : V) => (Eq ((tilde R) r) (OPair x y)))))))).
Definition Good := fun (phi : Class) (g : V) => (Product (Rel g) (Pi V (fun (x : V) => (Pi V (fun (y : V) => (Impl (El (OPair x y) g) (Sigma V (fun (A : V) => (Product (CEl (OPair y A) phi) (Pi (bar A) (fun (y' : (bar A)) => (Sigma (bar x) (fun (x' : (bar x)) => (El (OPair ((tilde x) x') ((tilde A) y'))) g))))))))))))).
Definition I := fun (phi : Class) => (classi (fun (x : V) => (Sigma V (fun (g : V) => (Product (Good phi g) (Sigma V (fun (y : V) => (El (OPair y x) g)))))))).

Axiom Omega : V.
Axiom S : forall (A : V) (F : forall (_ : (bar A)), V), V.
Axiom P : forall (A : V) (F : forall (_ : (bar A)), V), V.
Axiom W : forall (A : V) (F : forall (_ : (bar A)), V), V.

Definition PSW := (classi (fun (x : V) => (Sum (Eq x Omega) (Sum (Sigma V (fun (A : V) => (Sigma (Impl (bar A) V) (fun (F : (Impl (bar A) V)) => (Eq x (P A (imple F))))))) (Sum (Sigma V (fun (A : V) => (Sigma (Impl (bar A) V) (fun (F : (Impl (bar A) V)) => (Eq x (S A (imple F))))))) (Sigma V (fun (A : V) => (Sigma (Impl (bar A) V) (fun (F : (Impl (bar A) V)) => (Eq x (W A (imple F)))))))))))).

Definition Fun := fun (a f : V) => (Product (Rel f) (Product (Pi (bar a) (fun (x : (bar a)) => (Sigma V (fun (y : V) => (El (OPair ((tilde a) x) y) f))))) (Pi (bar a) (fun (x : (bar a)) => (Pi V (fun (y : V) => (Pi V (fun (z : V) => (Impl (Product (El (OPair ((tilde a) x) y) f) (El (OPair ((tilde a) x) z) f)) (Eq y z)))))))))).
Definition H := fun (A : Class) => (I (classi (fun (x : V) => (Sigma V (fun (a : V) => (Product (CEl a A) (Sigma V (fun (f : V) => (Product (Fun a f) (Sigma V (fun (y : V) => (Product (Pi V (fun (z : V) => (Product (Impl (El z y) (Sigma V (fun (w : V) => (El (OPair w z) f)))) (Impl (Sigma V (fun (w : V) => (El (OPair w z) f))) (El z y))))) (Eq x (OPair y y)))))))))))))).
Definition M := (H PSW).

Definition U := (Sigma V (fun (x : V) => (CEl x M))).

Inductive UClass :=
| uclassi : forall (_ : forall (_ : U), Type), UClass.

Structure ElOp2 (A : Type) (f : forall (_ : A) (_ : U), Type) (g : forall (_ : A) (_ : UClass), Type) := {
    elop2type : Type;
    #[canonical=no] elop2impl : forall (_ : A) (_ : elop2type), Type
}.

Canonical ElOp2U (A : Type) (f : forall (_ : A) (_ : U), Type) (g : forall (_ : A) (_ : UClass), Type) := (Build_ElOp2 A f g U (fun (x : A) (y : U) => (f x y))).
Canonical ElOp2C (A : Type) (f : forall (_ : A) (_ : U), Type) (g : forall (_ : A) (_ : UClass), Type) := (Build_ElOp2 A f g UClass (fun (x : A) (y : UClass) => (g x y))).

Structure ElOp := {
    eloptype : Type;
    #[canonical=no] elopf : forall (_ : eloptype) (_ : U), Type;
    #[canonical=no] elopg : forall (_ : eloptype) (_ : UClass), Type;
}.

Canonical ElOpU := (Build_ElOp U (fun (x y : U) => (El (sigmael x) (sigmael y))) (fun (x : U) (y : UClass) => (match y with | (uclassi f) => (f x) end))).

Definition Bi := fun (A B : Type) => (Product (Impl A B) (Impl B A)).

Definition UEl := fun {op1 : ElOp} {op2 : (ElOp2 (eloptype op1) (elopf op1) (elopg op1))} (x : (eloptype op1)) (y : (elop2type (eloptype op1) (elopf op1) (elopg op1) op2)) => (elop2impl (eloptype op1) (elopf op1) (elopg op1) op2 x y).
Definition UEq := fun (x y : UClass) => (Pi U (fun (z : U) => (Bi (UEl z x) (UEl z y)))).
Coercion promote := fun (x : U) => (uclassi (fun (z : U) => (UEl z x))).

Canonical ElOpC := (Build_ElOp UClass (fun (x : UClass) (y : U) => (Sigma U (fun (z : U) => (Product (UEq z x) (UEl z y))))) (fun (x y : UClass) => (Sigma U (fun (z : U) => (Product (UEq z x) (UEl z y)))))).

Theorem ext : forall (x y z : U), (Impl (Product (UEq x y) (UEl x z)) (UEl y z)).
Proof.
Admitted.

Theorem ind : forall (P : forall (_ : U), Type), (Impl (Pi U (fun (x : U) => (Impl (Pi U (fun (y : U) => (Impl (UEl y x) (P y)))) (P x)))) (Pi U (fun (x : U) => (P x)))).
Proof.
Admitted.

Theorem pair : (Pi U (fun (x : U) => (Pi U (fun (y : U) => (Sigma U (fun (z : U) => (Pi U (fun (w : U) => (Impl (Sum (UEq w x) (UEq w y)) (UEl w z)))))))))).
Proof.
Admitted.

Theorem uni : (Pi U (fun (x : U) => (Sigma U (fun (y : U) => (Pi U (fun (z : U) => (Bi (UEl z y) (Sigma U (fun (w : U) => (Product (UEl w x) (UEl z w))))))))))).
Proof.
Admitted.

Theorem nul : (Sigma U (fun (x : U) => (Pi U (fun (y : U) => (Not (UEl y x)))))).
Proof.
Admitted.

Theorem int : (Pi U (fun (x : U) => (Pi U (fun (y : U) => (Sigma U (fun (z : U) => (Pi U (fun (w : U) => (Bi (UEl w z) (Product (UEl w x) (UEl w y))))))))))).
Proof.
Admitted.

Theorem col : forall (P : forall (_ _ : U), Type), (Pi U (fun (x : U) => (Impl (Pi U (fun (y : U) => (Impl (UEl y x) (Sigma U (fun (z : U) => (P y z)))))) (Sigma U (fun (y : U) => (Product (Pi U (fun (z : U) => (Impl (UEl z x) (Sigma U (fun (w : U) => (Product (UEl w y) (P z w))))))) (Pi U (fun (w : U) => (Impl (UEl w y) (Sigma U (fun (z : U) => (Product (UEl z x) (P z w))))))))))))).
Proof.
Admitted.

Theorem rea : (Pi U (fun (x : U) => (Sigma U (fun (y : U) => (Product (Pi U (fun (z : U) => (Impl (UEl z x) (UEl z y)))) (Product (Pi U (fun (z : U) => (Impl (UEl z y) (Pi U (fun (w : U) => (Impl (UEl w z) (UEl w y))))))) (Pi U (fun (z : U) => (Impl (UEl z y) (Pi U (fun (w : U) => (Impl (Pi U (fun (v : U) => (Impl (UEl v w) (Sigma U (fun (u : U) => (Product (UEl u z) (Sigma U (fun (t : U) => (Product (UEl t y) (Pi U (fun (s : U) => (Bi (UEl s v) (Sum (UEq s u) (Pi U (fun (r : U) => (Bi (UEl r s) (Sum (UEq r u) (UEq r t)))))))))))))))))) (Impl (Pi U (fun (v : U) => (Impl (UEl v z) (Sigma U (fun (u : U) => (Sigma U (fun (t : U) => (Product (UEl t w) (Pi U (fun (s : U) => (Bi (UEl s t) (Sum (UEq s v) (Pi U (fun (r : U) => (Bi (UEl r s) (Sum (UEq r v) (UEq r u))))))))))))))))) (Sigma U (fun (v : U) => (Product (UEl v y) (Product (Pi U (fun (u : U) => (Impl (UEl u z) (Sigma U (fun (t : U) => (Product (UEl t v) (Sigma U (fun (s : U) => (Product (UEl s w) (Pi U (fun (r : U) => (Bi (UEl r s) (Sum (UEq r u) (Pi U (fun (q : U) => (Bi (UEl q r) (Sum (UEq q u) (UEq q t)))))))))))))))))) (Pi U (fun (u : U) => (Impl (UEl u v) (Sigma U (fun (t : U) => (Product (UEl t z) (Sigma U (fun (s : U) => (Product (UEl s w) (Pi U (fun (r : U) => (Bi (UEl r s) (Sum (UEq r t) (Pi U (fun (q : U) => (Bi (UEl q r) (Sum (UEq q t) (UEq q u))))))))))))))))))))))))))))))))))).
Proof.
Admitted.

Definition Subset := fun (x y : UClass) => (Pi U (fun (z : U) => (Impl (UEl z x) (UEl z y)))).
Definition UOPair := fun (x y : U) => (uclassi (fun (z : U) => (Product (UEl z x) (UEl z y)))).
Definition Func := fun (x y : UClass) => (uclassi (fun (z : U) => (Pi U (fun (w : U) => (Impl (UEl w z) (Sigma U (fun (u : U) => (Product (UEl u x) (Sigma U (fun (v : U) => (Product (UEl v y) (UEq w (UOPair u v))))))))))))).
Definition Onto := fun (x y : UClass) => (uclassi (fun (z : U) => (Product (UEl z (Func x y)) (Pi U (fun (w : U) => (Impl (UEl w y) (Sigma U (fun (v : U) => (Product (UEl v x) (UEl (UOPair v w) z)))))))))).
Definition Ran := fun (x : UClass) => (uclassi (fun (y : U) => (Sigma U (fun (z : U) => (UEl (UOPair z y) x))))).

Definition pie := fun {x : Type} {y : forall (_ : x), Type} (t : (Pi x y)) => match t with | (Pii _ _ f) => f end.
Definition sigmaer := fun {x : Type} {y : forall (_ : x), Type} (t : (Sigma x y)) => match t return (y (sigmael t)) with | (Sigmai _ _ _ f) => f end.
Definition productel := fun {x y : Type} (t : (Product x y)) => match t with | (Producti _ _ a _) => a end.
Definition producter := fun {x y : Type} (t : (Product x y)) => match t with | (Producti _ _ _ a) => a end.
Definition impli := fun {x y : Type} (a : forall (_ : x), y) => (Impli x y a).
Definition sigmai := fun {A : Type} (B : forall (_ : A), Type) (a : A) (H : (B a)) => (Sigmai A B a H).
Definition pii := fun {A : Type} {B : forall (_ : A), Type} (f : forall (a : A), (B a)) => (Pii A B f).
Definition producti := fun {A B : Type} (a : A) (b : B) => (Producti A B a b).

Axiom symi : forall {x y : UClass} (H : (UEq x y)), (UEq y x).
Axiom transi : forall {x y z : UClass} (H0 : (UEq x y)) (H1 : (UEq y z)), (UEq x z).
Axiom paireq : forall {x y z w : U} (H0 : (UEq x y)) (H1 : (UEq z w)), (UEq (UOPair x z) (UOPair y w)).
Axiom paireqer : forall {x y z w : U} (H0 : (UEq (UOPair x z) (UOPair y w))), (UEq z w).

Axiom exti : forall {x y z : U} (H0 : (UEq x y)) (H1 : (UEl x z)), (UEl y z).
Axiom extcui : forall {x : UClass} {y z : U} (H1 : (UEq x y)) (H1 : (UEl x z)), (UEl y z).
Axiom extci : forall {x y z : UClass} (H0 : (UEq x y)) (H1 : (UEl x z)), (UEl y z).

Theorem inf : (Sigma U (fun (x : U) => (Product (Product (Sigma U (fun (y : U) => (Product (UEl y x) (Pi U (fun (z : U) => (Not (UEl z y))))))) (Pi U (fun (y : U) => (Impl (UEl y x) (Sigma U (fun (z : U) => (Product (UEl z x) (Pi U (fun (w : U) => (Bi (UEl w z) (Sum (UEq w y) (UEl w y)))))))))))) (Pi U (fun (y : U) => (Impl (Product (Sigma U (fun (z : U) => (Product (UEl z y) (Pi U (fun (w : U) => (Not (UEl w z))))))) (Pi U (fun (z : U) => (Impl (UEl z y) (Sigma U (fun (w : U) => (Product (UEl w y) (Pi U (fun (v : U) => (Bi (UEl v w) (Sum (UEq v z) (UEl v z)))))))))))) (Pi U (fun (z : U) => (Impl (UEl z x) (UEl z y)))))))))).
Proof.
    assert (refl : forall (x : U), (UEq x x)).
    admit.
    assert (exp : forall (x y : U), (Sigma U (fun (z : U) => (UEq z (Func x y))))).
    admit.
    assert (pairex : forall (x y : U), (Sigma U (fun (z : U) => (UEq z (UOPair x y))))).
    admit.
    assert (ran : forall (x : U), (Sigma U (fun (y : U) => (UEq y (Ran x))))).
    admit.
    pose (Lambda := fun (phi : UClass) (x : U) => (uclassi (fun (y : U) => (Sigma U (fun (z : U) => (Product (Subset z x) (UEl (UOPair y z) phi))))))).
    pose (Phi := fun (phi : UClass) (x : U) => (uclassi (fun (y : U) => (UEl (UOPair y x) phi)))).
    pose (Bounded := fun (phi : UClass) => (Product (Pi U (fun (x : U) => (Sigma U (fun (y : U) => (UEq y (Phi phi x)))))) (Sigma U (fun (B : U) => (Pi U (fun (A : U) => (Impl (Sigma U (fun (a : U) => (UEl (UOPair a A) phi))) (Sigma U (fun (b : U) => (Product (UEl b B) (Sigma U (fun (f : U) => (UEl f (Onto b A)))))))))))))).
    assert (S1 : forall (phi : UClass) (x : U), (Impl (Bounded phi) (Sigma U (fun (y : U) => (UEq y (Lambda phi x)))))).
    intros.
    enough (S1 : forall (H0 : (Bounded phi)), (Sigma U (fun (y : U) => (UEq y (Lambda phi x))))).
    exact (impli S1).
    intros.
    pose (S1 := (pie (col (fun (y z : U) => (UEq z (Func y x)))) (sigmael (producter H0)))).
    enough (S2 : (Pi U (fun (y : U) => (Impl (UEl y (sigmael (producter H0))) (Sigma U (fun (z : U) => (UEq z (Func y x)))))))).
    pose (S3 := (imple S1 S2)).
    pose (S4 := (pie uni (sigmael S3))).
    pose (S6 := (pie (col (fun (y z : U) => (UEq z (Phi phi (sigmael (ran y)))))) (sigmael S4))).
    enough (S7 : (Pi U (fun (y : U) => (Impl (UEl y (sigmael S4)) (Sigma U (fun (z : U) => (UEq z (Phi phi (sigmael (ran y)))))))))).
    pose (S8 := (imple S6 S7)).
    pose (S9 := (pie uni (sigmael S8))).
    enough (S10 : forall (y : U), (Bi (UEl y (sigmael S9)) (UEl y (Lambda phi x)))).
    exact (sigmai (fun (y : U) => (UEq y (Lambda phi x))) (sigmael S9) (pii S10)).
    intros.
    enough (S10 : forall (H1 : (UEl y (sigmael S9))), (UEl y (Lambda phi x))).
    enough (S11 : forall (H1 : (UEl y (Lambda phi x))), (UEl y (sigmael S9))).
    exact (producti (impli S10) (impli S11)).
    intros.
    pose (A := (sigmael H1)).
    pose (S11 := (imple ((pie (sigmaer (producter H0))) A) (sigmai (fun (a : U) => (UEl (UOPair a A) phi)) y (producter (sigmaer H1))))).
    pose (b := (sigmael S11)).
    pose (S12 := (producter (sigmaer S11))).
    pose (f := (sigmael S12)).
    pose (S13 := ((imple (pie (productel (sigmaer S3)) b)) (productel (sigmaer S11)))).
    assert (S14 : forall (z : U) (H2 : (UEl z f)), (Sigma U (fun (w : U) => (Product (UEl w b) (Sigma U (fun (v : U) => (Product (UEl v x) (UEq z (UOPair w v))))))))).
    intros.
    pose (S14 := (imple ((pie (productel (sigmaer S12))) z) H2)).
    exact (sigmai (fun (w : U) => (Product (UEl w b) (Sigma U (fun (v : U) => (Product (UEl v x) (UEq z (UOPair w v))))))) (sigmael S14) (producti (productel (sigmaer S14)) (sigmai (fun (v : U) => (Product (UEl v x) (UEq z (UOPair (sigmael S14) v)))) (sigmael (producter (sigmaer S14))) (producti (imple (pie (productel (sigmaer H1)) (sigmael (producter (sigmaer S14)))) (productel (sigmaer (producter (sigmaer S14))))) (producter (sigmaer (producter (sigmaer S14)))))))).
    pose (S15 := (pii (fun (z : U) => (impli (S14 z))))).
    pose (S16 := (imple (producter (pie (sigmaer S4) f)) (sigmai (fun (w : U) => (Product (UEl w (sigmael S3)) (UEl f w))) (sigmael S13) (producti (productel (sigmaer S13)) (imple (producter (pie (producter (sigmaer S13)) f)) S15))))).
    pose (S17 := (imple (pie (productel (sigmaer S8)) f) S16)).
    assert (S18 : forall (z : U), (Bi (UEl z A) (UEl z (sigmael (ran f))))).
    intros.
    assert (S18 : forall (H2 : (UEl z A)), (UEl z (sigmael (ran f)))).
    intros.
    pose (S18 := (imple (pie (producter (sigmaer S12)) z) H2)).
    pose (S19 := (sigmai (fun (v : U) => (UEl (UOPair v z) f)) (sigmael S18) (producter (sigmaer S18)))).
    exact (imple (producter (pie (sigmaer (ran f)) z)) S19).
    assert (S19 : forall (H2 : (UEl z (sigmael (ran f)))), (UEl z A)).
    intros.
    pose (S19 := (imple (productel (pie (sigmaer (ran f)) z)) H2)).
    pose (sigmaer S19).
    pose (S20 := (sigmaer (producter (sigmaer (imple (pie (productel (sigmaer S12)) (sigmael (sigmaer S19))) (producter (sigmaer (sigmaer S19)))))))).
    pose (S21 := (paireqer (transi (symi (productel (sigmaer (sigmaer S19)))) (producter S20)))).
    exact (exti (symi S21) (productel S20)).
    exact (producti (impli S18) (impli S19)).
    pose (S19 := (pii S18)).
    pose (S20 := (paireq (refl y) S19)).
    pose (S21 := (extci S20 (producter (sigmaer H1)))).
    exact (imple (producter (pie (sigmaer S9) y)) (sigmai (fun (w : U) => (Product (UEl w (sigmael S8)) (UEl y w))) (sigmael S17) (producti (productel (sigmaer S17)) (imple (producter (pie (producter (sigmaer S17)) y)) S21)))).
    intros.
    pose (S11 := (imple (productel (pie (sigmaer S9) y)) H1)).
    pose (S12 := (imple (pie (producter (sigmaer S8)) (sigmael S11)) (productel (sigmaer S11)))).
    pose (S13 := (imple (productel (pie (producter (sigmaer S12)) y)) (producter (sigmaer S11)))).
    pose (S14 := (productel (sigmaer S12))).
    pose (S15 := (imple (productel (pie (sigmaer S4) (sigmael S12))) S14)).
    pose (S16 := (imple (pie (producter (sigmaer S3)) (sigmael S15)) (productel (sigmaer S15)))).
    pose (S17 := (imple (productel (pie (producter (sigmaer S16)) (sigmael S12))) (producter (sigmaer S15)))).
    assert (S18 : forall (z : U) (H2 : (UEl z (sigmael (ran (sigmael S12))))), (UEl z x)).
    intros.
    pose (S18 := (imple (productel (pie (sigmaer (ran (sigmael S12))) z)) H2)).
    pose (S19 := (producter (sigmaer (imple (pie S17 (sigmael (pairex (sigmael S18) z))) (extcui (symi (sigmaer (pairex (sigmael S18) z))) (sigmaer S18)))))).
    exact (exti (symi (paireqer (transi (symi (sigmaer (pairex (sigmael S18) z))) (producter (sigmaer S19))))) (productel (sigmaer S19))).
    pose (S19 := (pii (fun (z : U) => (impli (S18 z))))).
    exact (sigmai (fun (z : U) => (Product (Subset z x) (UEl (UOPair y z) phi))) (sigmael (ran (sigmael S12))) (producti S19 S13)).
    exact (pii (fun (y : U) => (impli (fun (H1 : (UEl y (sigmael S4))) => (pie (productel H0) (sigmael (ran y))))))).
    exact (pii (fun (y : U) => (impli (fun (H1 : (UEl y (sigmael (producter H0)))) => (exp y x))))).
    pose (S2 := (ind (fun (x : U) => (Sigma (fun (y : U) => (UEq y (uclassi (fun (z : U) => (Sigma U (fun (w : U) => (Product (UEl w ))))))))))))
Qed.

Theorem psw : False.
Admitted.


CZF_0 + REA -> Fullness
CZF_0 + REA + Strong Collect -> Subset Collect
CZF + PAx + Exponentiation -> Subset Collect

ext* + pair* + uni* + rsep* + rea* + col* + inf? + ind* + PSW-AC