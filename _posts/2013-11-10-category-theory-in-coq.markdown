---
layout: post
title:  "Welcome to Jekyll!"
date:   2013-11-10 14:42:00
categories: category theory, coq
---
As defined at http://www.cs.berkeley.edu/~megacz/coq-categories/ following Awodey's book

Generalizable All Variables.
Require Import Notations.

(* definition 1.1 *)
Class Category
( Ob               :  Type                    )
( Hom              :  Ob -> Ob -> Type        ) :=
{ hom              := Hom                                                          where "a ~> b" := (hom a b)
; ob               := Ob

; id               :  forall  a,                          a~>a
; comp             :  forall  a b c,                      a~>b -> b~>c -> a~>c     where "f >>> g" := (comp _ _ _ f g)

; eqv              :  forall  a b,   (a~>b) -> (a~>b) -> Prop                      where "f ~~ g" := (eqv _ _ f g)
; eqv_equivalence  :  forall  a b,   Equivalence (eqv a b)
; comp_respects    :  forall  a b c, Proper (eqv a b ==> eqv b c ==> eqv a c) (comp _ _ _)

; left_identity    :  forall `(f:a~>b),                       id a >>> f  ~~ f
; right_identity   :  forall `(f:a~>b),                       f  >>> id b ~~ f
; associativity    :  forall `(f:a~>b)`(g:b~>c)`(h:c~>d), (f >>> g) >>> h ~~ f >>> (g >>> h)
}.
Coercion ob      :      Category >-> Sortclass.

Notation "a ~> b"         := (@hom _ _ _ a b)                      :category_scope.
Notation "f ~~ g"         := (@eqv _ _ _ _ _ f g)                  :category_scope.
Notation "f >>> g"        := (comp _ _ _ f g)                      :category_scope.
Notation "a ~~{ C }~~> b" := (@hom _ _ C a b)       (at level 100) :category_scope.


As defined in math Classes https://github.com/math-classes/math-classes

Global Generalizable All Variables.
Global Set Automatic Introduction.
Global Set Automatic Coercions Import.

Require Import Streams.
Require Export Morphisms Setoid Program Unicode.Utf8 Utf8_core.

(* Equality *)
Class Equiv A := equiv: relation A.


(* Revert to transparency to allow conversions during unification. *)
Typeclasses Transparent Equiv.
Typeclasses Transparent compose flip.

(* We use this virtually everywhere, and so use "=" for it: *)
Infix "=" := equiv : type_scope.
Notation "(=)" := equiv (only parsing) : mc_scope.
Notation "( x =)" := (equiv x) (only parsing) : mc_scope.
Notation "(= x )" := (fun y => equiv y x) (only parsing) : mc_scope.
Notation "(<>)" := (fun x y => ~x = y) (only parsing) : mc_scope.
Notation "x <> y":= (~x = y): type_scope.
Notation "( x <>)" := (fun y => x <> y) (only parsing) : mc_scope.
Notation "(<> x )" := (fun y => y <> x) (only parsing) : mc_scope.

Delimit Scope mc_scope with mc. 
Global Open Scope mc_scope.

Class Arrows (O: Type): Type := Arrow: O -> O -> Type.
Typeclasses Transparent Arrows. (* Ideally this should be removed *)

Infix "[>]" := Arrow (at level 90, right associativity) : mc_scope.
Class CatId O `{Arrows O} := cat_id: forall x, x [>] x.
Class CatComp O `{Arrows O} := comp: forall x y z, (y [>] z) -> (x [>] y) -> (x [>] z).

Arguments cat_id {O arrows CatId x} : rename.
Arguments comp {O arrow CatComp} _ _ _ _ _ : rename.

Class Setoid A {Ae : Equiv A} : Prop := setoid_eq :> Equivalence (@equiv A Ae).

Infix "(o)" := (comp _ _ _) (at level 40, left associativity) : mc_scope.
  (* Taking over ∘ is just a little too zealous at this point. With our current
   approach, it would require changing all (nondependent) function types A -> B
   with A [>] B to make them use the canonical name for arrows, which is
   a tad extreme. *)
Notation "((o))" := (comp _ _ _) (only parsing) : mc_scope.
Notation "( f (o))" := (comp _ _ _ f) (only parsing) : mc_scope.
Notation "((o) f )" := (λ g, comp _ _ _ g f) (only parsing) : mc_scope.

Class HeteroAssociative {A B C AB BC} `{Equiv ABC}
     (fA_BC: A -> BC -> ABC) (fBC: B -> C -> BC) (fAB_C: AB -> C -> ABC) (fAB : A -> B -> AB): Prop
   := associativity : forall x y z, fA_BC x (fBC y z) = fAB_C (fAB x y) z.
Class Associative `{Equiv A} f := simple_associativity:> HeteroAssociative f f f f.
Notation ArrowsAssociative C := (forall {w x y z: C}, HeteroAssociative ((o)) (comp z _ _ ) ((o)) (comp y x w)).

Class LeftIdentity {A} `{Equiv B} (op : A -> B -> B) (x : A): Prop := left_identity: forall y, op x y = y.
Class RightIdentity `{Equiv A} {B} (op : A -> B -> A) (y : B): Prop := right_identity: forall x, op x y = x.

Class Category O `{!Arrows O} `{forall x y: O, Equiv (x [>] y)} `{!CatId O} `{!CatComp O}: Prop :=
  { arrow_equiv :> forall x y, Setoid (x [>] y)
  ; comp_proper :> forall x y z, Proper ((=) ==> (=) ==> (=)) (comp x y z)
  ; comp_assoc :> ArrowsAssociative O
  ; id_l :> forall x y, LeftIdentity (comp x y y) cat_id
  ; id_r :> forall x y, RightIdentity (comp x x y) cat_id }.
      (* note: no equality on objects. *)

(* todo: use my comp everywhere *)
Arguments comp_assoc {O arrows eq CatId CatComp Category w x y z} _ _ _ : rename.



As defined in Matthieu Sozeau page http://mattam.org/repos/coq/cat

As defined in paper on math classes




