Require Import Setoid.
Section Practica07.
(* ---------------------------------------------------------------------
   EQUIPO: EQUIPO ALFA DINAMITA BUENA ONDA ESCUADRON LOBO
   
   INTEGRANTES: Arévalo Gaytan Rodrigo
                Arroyo Lozano Santiago
   ------------------------------------------------------------------ *)

(* Definimos a los naturales y nuestras hipotesis primero:*)
Inductive nat: Set :=
| O: nat
| S: nat -> nat.

Fixpoint suma (n:nat) (m:nat) : nat :=
match n with
| O => m
| S(v) => S(suma v m)
end.

Notation "x + y" := (suma x y).

Fixpoint producto (n: nat) (m:nat) : nat :=
match n with
| O => m 
| S(v) => S(producto v m)
end.

Notation "x * y" := (producto x y).

Hypothesis suma_0_derecha: forall n : nat, n + O = n.
Hypothesis producto_0_derecha: forall n : nat, n * O = O.
Hypothesis producto_0_izquierda: forall n : nat, O * n = O.
Hypothesis producto_add_izquierda : forall a b : nat, a*S(b) = a*b+a.
Hypothesis producto_add_derecha : forall a b : nat, a*b+a = a*S(b).
Theorem suma_n_Sm: forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' IHn']. 
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.
Theorem suma_conmutativa: forall n m : nat,n + m = m + n.
Proof.
  intros  n m.
  induction n as [|n' IHn'].
  - simpl.
    rewrite suma_0_derecha.
    reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite <- suma_n_Sm.
    reflexivity.
Qed.
Theorem adicion : forall a b : nat, a+S(b) = S(a+b).
Proof.
  intros.
  rewrite suma_conmutativa.
  simpl.
  rewrite suma_conmutativa.
  reflexivity.
Qed.
Theorem suma_asociativa: forall n m r : nat, n + (m + r) = (n + m) + r.
Proof.
  intros.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.


(* ---------------------------------------------------------------------
   Ejercicio 1. Demostrar que 
      forall n m p : nat, (n + m) * p = (n * p) + (m * p).
   ------------------------------------------------------------------ *)
Theorem ejercicio_1: forall n m r : nat, n*(m+r) = (n * m) + (n * r).
Proof.
intros.
induction r as [|r' HIn']. 
- rewrite suma_0_derecha.
  rewrite producto_0_derecha.
  rewrite suma_0_derecha.
  reflexivity.
- rewrite adicion.  
  rewrite producto_add_izquierda.        
  rewrite HIn'.
  rewrite <- suma_asociativa.
  rewrite producto_add_derecha.  
  reflexivity.
Qed.

(***********************************************************************************************)

(* Definimos los grupos:*)

Variable G: Set.

Hypotheses (e:G)  (* Neutro *)
           (g:G -> G -> G) (* Operacion binaria*)
           (h:G -> G). (* Inverso *)

(* Las condiciones anteriores satisfacen las siguientes propiedades: *)
Hypothesis Asoc : forall x y z : G, g x (g y z) = g (g x y) z.
Hypothesis Inv : forall x:G, g (h x) x = e.
Hypothesis Inv_Der : forall x:G, g x (h x) = e.
Hypothesis Neut : forall x:G, g e x = x.
Hypothesis Neut_Der : forall x:G, g x e = x.
Theorem NeutIdem: forall x:G, g x x = x -> x = e. 
Proof.
  intros.
  rewrite <- Inv with x.
  rewrite <- H at 3.
  rewrite Asoc.
  rewrite Inv.
  rewrite Neut.
  trivial.
  (*reflexivity.*)
Qed.

Theorem Cancel: forall x y z:G, g x y = g x z -> y = z.
Proof.
  intros.
  rewrite <- Neut with y.
  rewrite <- Inv with x.
  rewrite <- Asoc.
  rewrite H.
  rewrite Asoc.
  rewrite Inv.
  rewrite Neut.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------
   Ejercicio 2. Demostrar que 
      forall x:G, h (h x) = x. 
   ------------------------------------------------------------------ *)
Theorem ejercicio_2: forall x:G, h (h x) = x. 
Proof.
  intros.
  apply (Cancel) with (h(x)).
  rewrite Inv_Der.
  rewrite Inv.
  reflexivity.
Qed.


(* ---------------------------------------------------------------------
   Ejercicio 3. Demostrar que 
      forall n m p : nat, (n + m) * p = (n * p) + (m * p).
   ------------------------------------------------------------------ *)
Theorem ejercicio_3 : forall x y:G, h (g x y) = g (h y) (h x). 
Proof.
  intros.
  apply (Cancel) with (g x y).
  rewrite Inv_Der with (g x y).
  rewrite Asoc.
  rewrite <- Asoc with x y (h y).
  rewrite Inv_Der.
  rewrite Neut_Der with x.
  rewrite Inv_Der.
  reflexivity.
Qed.


(************************************************************************************************)
(*Definimos nuestras variables proposicionales*)
Variables P Q R S T U : Prop.


(* ---------------------------------------------------------------------
   Ejercicio 4. Demostrar que 
      forall P Q R S T U : Prop, (P -> Q /\ R) -> (R \/ ~Q -> S /\ T) -> (T <-> U) -> (P -> U).
   ------------------------------------------------------------------ *)
Theorem ejercicio_4 : (P -> Q /\ R) -> (R \/ ~Q -> S /\ T) -> (T <-> U) -> (P -> U).
Proof.
  intuition.
  Show Proof.
Qed. 

(* ---------------------------------------------------------------------
   Ejercicio 5. Demostrar que 
      forall forall P Q R S T U : Prop, (P -> Q -> R) /\ (P \/ S) /\ (T -> Q) /\ (~S) -> ~R -> ~T.
   ------------------------------------------------------------------ *)

Theorem ejercicio_5 : (P -> Q -> R) /\ (P \/ S) /\ (T -> Q) /\ (~S) -> ~R -> ~T.
Proof.
  intuition.
  Show Proof.
Qed.

(* ---------------------------------------------------------------------
   Punto Extra. Demostrar que 
      forall forall P Q R S T U : Prop, (P /\ Q <-> P) -> (Q <-> P \/ Q).
   ------------------------------------------------------------------ *)

Theorem punto_extra_1 : (P /\ Q <-> P) -> (Q <-> P \/ Q).
Proof.
  intuition.
  Show Proof.
Qed.

