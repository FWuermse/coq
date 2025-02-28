Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.
Set Debug "rewrite".

Parameter A : Type.
Parameter α β : Type.
Parameter Rα : relation A.
Parameter Rβ : relation β.
Parameter a a' : A.
Parameter x : A.
Parameter Pα : A -> Prop.
Parameter Pα' : A -> Prop.
Parameter Raa : relation (Prop -> Prop).
Parameter Pa : Prop -> Prop.
Parameter not : Prop -> Prop.
Parameter p : Prop.

Goal (Raa not Pa) -> not (p /\ (not p)).
Proof.
  intros h.