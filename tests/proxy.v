Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.
Set Debug "rewrite".

Parameter r : relation Prop.

Goal forall P Q : Prop, r P Q -> (Q -> Q) /\ (Q -> P).
intros P Q H.
rewrite H.
