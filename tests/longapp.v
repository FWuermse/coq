Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.
Set Debug "rewrite".

Parameter A : Type.
Parameter B : Type.
Parameter C : Type.
Parameter c : C.
Parameter f : B -> B -> C -> A -> A -> A -> B -> Prop.
Parameter a x : A.
Parameter b : B.
Parameter r : relation A.
Parameter g : A -> A.

Goal r a x -> f b b c a (g a) a b b c.
intros h.
rewrite h.