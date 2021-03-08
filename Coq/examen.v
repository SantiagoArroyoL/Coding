Goal forall (X : Type) (P Q R S T : X->Prop), 
    (forall x : X, P x \/ Q x -> ~R x) -> (forall x : X, S x -> R x) -> (forall x : X, P x -> ~S x \/ T x).
Proof.
intros X P Q R S T.
intros H1 H2 x H3.
assert H2.
Qed. 
Section Examen.

(** Lo definimos como inductivo pero no usaremos así la definición, usaremos exclusivaente los axiomas*)

Inductive A: Set :=
| O: A
| S: A -> A.

Fixpoint suma (n:A) (m:A) : A :=
match n with
| O => m
| S(v) => S(suma v m)
end.

Notation "x + y" := (suma x y).

Fixpoint producto (n: A) (m:A) : A :=
match n with
| O => m 
| S(v) => S(producto v m)
end.

Notation "x * y" := (producto x y).


(* Axiomas:*)
Hypothesis (h:A -> A). (* Inverso *)
Hypothesis A1 : forall x:A, x+O = O.
Hypothesis A2 : forall x y:A, x+y = y+x.
Hypothesis A3 : forall x:A, x +(h x) = O.
Hypothesis A4 : forall x y z:A, (x+y)+z = x+(y+z).
Hypothesis A5 : forall x y z:A, (x*y)*z = x*(y*z).
Hypothesis A6 : forall x y z:A, x*(y+z) = x*y + x*z.
Hypothesis A7 : forall x y z:A, (x + y)* z = x * z + y * z.
Hypothesis A8 : forall x y z:A, x*O = O.


Theorem punto_extra_examen : forall x y:A, x*(h y) = h(x*y).
Proof.
intros.
rewrite <- A1 with (x*y).
Qed.

