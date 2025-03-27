Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Equivalence.
Require Import Setoid.
Require Import Morphisms.

Definition setEq {A : Type} (l1 l2 : list A) : Prop :=
  forall x, In x l1 <-> In x l2.

Instance setEqEquivalence {A : Type} : Equivalence (@setEq A).
Proof.
  split.
  - (* Reflexivity *)
    intros l1 x. reflexivity.
  - (* Symmetry *)
    intros l1 l2 H x.
    symmetry. apply H.
  - (* Transitivity *)
    intros l1 l2 l3 H12 H23 x.
    transitivity (In x l2); auto.
Qed.

Definition addElem {A : Type} (x : A) (l : list A) : list A :=
  x :: l.

Instance addElemProper {A : Type} (x : A) :
  Proper (setEq ==> setEq) (addElem x).
Proof.
  intros l1 l2 Heq y.
  simpl.
  split.
  - intros [H | H].
    + left; assumption.
    + right; apply Heq; assumption.
  - intros [H | H].
    + left; assumption.
    + right; apply Heq; assumption.
Qed.

Lemma rewriteExample :
  setEq [1;2;3] [3;2;1] -> setEq (addElem 4 [1;2;3]) (addElem 4 [3;2;1]).
Proof.
  intros H.
  rewrite H.
  apply addElemProper.
  reflexivity.
Qed.