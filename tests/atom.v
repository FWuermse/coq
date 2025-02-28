Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.
Set Debug "rewrite".

Parameter α β : Type.
Parameter A : Type.
Parameter Rα : relation A.
Parameter Rβ : relation β.
Parameter a a' : A.
Parameter x : A.
Parameter Pα : A -> Prop.

Goal Rα a a' -> Rα a x.
Proof.
  intros h.
  rewrite h.
Qed.