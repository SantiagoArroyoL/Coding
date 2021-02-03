Require Import List.
Import ListNotations.

Section MyListSection.
Variable A : Type.
Print list.
(* Recordatorio de las definiciones como aparecen en las bibliotecas de Coq
Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.
Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.
Infix "++" := app (right associativity, at level 60) : list_scope.
*)

Definition l1 := 2::4::6::[].
Print nat.

(* Axiomas/Lemas que describen la conmutatividad de la concatenacion respecto a 
la lista vacia. *)
Lemma axapp_nil_l : forall l:list A, [] ++ l = l.
Proof.
induction l.
- simpl. reflexivity. 
- rewrite <- IHl. simpl. reflexivity.
(*unfold app. reflexivity.*)
Qed. 

Lemma axapp_nil_r : forall l:list A, l ++ [] = l.
Proof.
induction l.
- simpl. reflexivity.
- rewrite <- IHl. simpl. rewrite IHl. rewrite IHl. reflexivity.
Qed. 

(* Y un teorema auxiliar *)
Theorem aux_app_comm_cons : 
   forall (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof.
induction x. 
- intros y a.
  rewrite axapp_nil_l.
  simpl.
  reflexivity.
- intros y1 a0.
  rewrite <- IHx.
  simpl app. (* definicion de append *)
  reflexivity.
Qed. 
  

(* Demostrar que la concatenacion asociativa *)
Theorem app_assoc : 
   forall l m n:list A, l ++ (m ++ n) = (l ++ m) ++ n.
Proof.
induction l.
- intros m n.
  simpl app. 
  reflexivity.
- intros m n.
  simpl app.
  rewrite IHl.
  reflexivity.
Qed. 

(** 
Cualquier lista no vacía puede descomponerse en dos listas y un elemento
tal que ese elemento está en una posición intermedia en la lista original.
*)

(* Definicion de una funcion para obtener todas las particiones de una lista*)
(* Se usa el caso particular de listas de naturales *)
Fixpoint aux_partition (n: nat) (l:list nat) : list (list nat*nat*list nat) :=
   match n with 
   | 0 => nil
   | S m => ((firstn m l),(nth m l 0),(skipn (S m) l)) :: aux_partition m l
   end.

  
Print l1.
Compute (aux_partition 2 l1).
 
Definition l2 := [3;4;7;2;6;8;0;1;5].
Compute (length l2).
Compute (aux_partition 4 l2).

Definition mypartition (x:list nat) : list (list nat*nat*list nat) :=
   let l := length x 
   in aux_partition l x.
(* notacion similar a where de Haskell:
partition = aux_partition l x
where l = length x
*)


Compute (mypartition l2).
Compute (rev (mypartition l2)).
   
   
(* Teorema que establece la propiedad de particion*)
(* de la nota tenemos esta formula: 
forall x (L_{Nat}}(x) /\ x != nil -> 
exists y exists z exists w (Nat(w) /\ L_{Nat}(y) /\ L_{Nat}(z) 
/\ x = app(y,cons(w,z))) *)
Theorem prop_partition : 
forall (x:list nat), x <> [] -> exists n, exists l1, exists l2, x = l1 ++ (n::l2).
Proof.
intros lista suposicion.
destruct lista.  (*analizar la lista*)  (* induction lista *)
- contradiction. (* lista = [] y es contradiccion con la suposicion*)
- (* se proporciona la particion mas sencilla que es 
  donde n es la cabeza de la lista*)
exists n.
exists [].
exists lista.
simpl. (* simplificar ocupando la definicion de append *)
reflexivity.
Qed.

Compute (nth 4 (mypartition l2)).

End MyListSection.