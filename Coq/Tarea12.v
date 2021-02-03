Section Tarea12.

Inductive nat: Set :=
| O: nat
| S: nat -> nat.

Inductive suma (A B:Type) : Type :=
  | inl : A -> suma A B
  | inr : B -> suma A B.

Notation "x + y" := (suma x y) : type_scope.

Inductive multi (A B:Type) : Type :=
  pair : A -> B -> multi A B.

Notation "x * y" := (multi x y) : type_scope.

Theorem suma_conm : forall a b : nat, a + b = b + a.
Proof.
  induction a.
    (* Caso Z *)
      induction b.
        (* Caso Z *)   reflexivity.
        (* Caso S b *) simpl. rewrite <- IHb. reflexivity.
    (* Caso a = S a *)
      induction b.
        (* Caso Z  *)
          simpl. rewrite (IHa 0). reflexivity.
        (* Caso S b *)
          simpl. rewrite <- IHb.
          simpl. rewrite (IHa (S b)).
          simpl. rewrite (IHa b).
          reflexivity.
Qed.