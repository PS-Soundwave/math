Axiom stroke : forall (_ _ : Prop), Prop.

Axiom mp : forall {p q r : Prop} (min : p) (maj : (stroke p (stroke q r))), r.

Axiom scharle : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke s (stroke s s)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).
