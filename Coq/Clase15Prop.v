
Require Import Classical.

Section LogicaProposicional.

Theorem ModusTollens: forall p q: Prop,  (~p -> ~q) /\ q -> p.
Proof.
intros p q H.
destruct H.
destruct (classic p).
- assumption.
- absurd q.
  --  apply H. assumption.
  -- assumption.
Qed.



