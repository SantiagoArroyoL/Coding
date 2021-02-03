(** Archivo introductorio para Logica Computacional, Facultad de Ciencias, UNAM. 

Favio Miranda
Lourdes Glz Huesca

Enero 2021 *)

(* Logica proposicional en Coq *)
(* 
Prop es el tipo mas basico para describir proposiciones, 
tanto de logica proposicional como de proposiciones de objetos.
Se puede consultar una introduccion a Coq en:
https://coq.inria.fr/a-short-introduction-to-coq

*)

(* no confundir bool y Prop *)
Fixpoint even n : bool :=
  match n with
    | 0 => true
    | 1 => false
    | S (S n') => even n'
  end.

Definition odd n := negb (even n).

Compute (even 5).
Compute (negb(even 5)).



Section LogicaProposicional.
Variables P Q R T S : Prop.

(* se puede describir la logica proposicional con el tipo Prop *)
Check Prop.
Check True.
Check ((P -> (Q /\ P)) -> (Q -> P)).

(* se pueden describir propiedades sencillas *)
Check (forall x y : nat, x * y = 0 -> x = 0 \/ y = 0).
Definition divide (x y: nat) := exists z, x * z = y.
Check divide.

(* tambien se puede usar Coq como lenguaje de programacion funcional y 
Prop como el tipo de regreso de propiedades inductivas basicas *)
Inductive prop_even : nat -> Prop :=
  | even_0 : prop_even 0
  | even_S n : prop_odd n -> prop_even (n + 1)
  with prop_odd : nat -> Prop :=
  | odd_S n : prop_even n -> prop_odd (n + 1).

Check prop_even.

(* LogicaProposicional minimal *)

Lemma and_comm : P /\ Q -> Q /\ P.
Proof.
intro.
destruct H.
split.
- assumption.
- assumption.
Qed.

Lemma imp_dist : (P -> (Q -> R)) -> (P -> Q) -> P -> R.
Proof.
intros H1 H2 Hp.
apply H1.
- assumption.
- apply H2.
  assumption.
Qed.

Theorem Ex1: (P \/ (Q /\ R)) -> (P -> Q) -> ( Q <-> S ) -> Q /\ S.
Proof.
intros H1 H2 H3.
split.
- destruct H3.
  destruct H1.
  -- apply H2.
  assumption.
  -- destruct H1.
     assumption.
- destruct H3.
  destruct H1.
  -- apply H.
  apply H2.
  assumption.
  -- apply H.
  apply H1.
Qed.

End LogicaProposicional.
