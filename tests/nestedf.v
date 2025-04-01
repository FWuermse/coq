
Require Import Setoid.
Require Import Relation_Definitions.
Require Import Morphisms.
Set Debug "rewrite".

Parameter A : Type.
Parameter B : Type.
Parameter C : Type.
Parameter c : C.
Parameter f : A -> Prop -> A -> Prop.
Parameter x : A -> Prop -> A -> Prop.
Parameter a : A.
Parameter b : B.
Parameter r : relation (A -> Prop -> A -> Prop).
Parameter g : A -> A.
Parameter R : relation Prop.
Parameter sr : subrelation r (pointwise_relation A (pointwise_relation Prop (pointwise_relation A R))).
Parameter ssr : subrelation R
 (Basics.flip Basics.impl
).
Goal r f x -> subrelation r (pointwise_relation A (pointwise_relation Prop (pointwise_relation A R))) -> subrelation R
 (Basics.flip Basics.impl
) -> f a (f a True a) a.
intros h h1 h2.
rewrite h.
