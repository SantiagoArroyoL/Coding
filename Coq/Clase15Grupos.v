Require Import Setoid.
Section Grupos.
(* Un grupo es un conjunto G junto con una operacion binaria sobre G que combina dos elementos en otro de G. Hay un elemento especial que es llamado el elemento identidad y para cada elemento en G existe uno inverso que bajo la operacion obtiene a la identidad *)

Variable G: Set.

Hypotheses (e:G)  (* Neutro *)
           (g:G -> G -> G) (* Operacion binaria*)
           (h:G -> G). (* Inverso *)

(* Las condiciones anteriores satisfacen las siguientes propiedades: *)
Hypothesis Asoc : forall x y z : G, g x (g y z) = g (g x y) z.

Hypothesis Inv : forall x:G, g (h x) x = e.

Hypothesis Neut : forall x:G, g e x = x.

(* notacion para hacer infija a la operacion binaria *)
Infix "<+>" := g (at level 50, left associativity).


(* Este puede ser ejercicio para lab *)
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


