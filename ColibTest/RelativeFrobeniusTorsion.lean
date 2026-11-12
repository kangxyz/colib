/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.RelativeFrobenius

/-! # Original smooth-site relative Frobenius and torsion inverse regression -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Frobenius
open AlgebraicGeometry.PresheafWithTransfers

universe v u

example {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Over S) [Smooth X.hom] : Flat (AlgebraicGeometry.relativeFrobenius S p hS X).left :=
  flat_relativeFrobenius_of_smooth S p hS X

example {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Scheme.SmoothSite S) :
    (Scheme.SmoothSite.frobeniusTwist p hS X).left =
      pullback X.hom (absoluteFrobenius S p hS) := rfl

example {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Scheme.SmoothSite S) :
    (Scheme.SmoothSite.relativeFrobenius p hS X).left =
      (AlgebraicGeometry.relativeFrobenius S p hS (Over.mk X.hom)).left := rfl

example {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : Scheme.SmoothSite S) :
    IsFinite (Scheme.SmoothSite.relativeFrobenius p hS X).left ∧
      Flat (Scheme.SmoothSite.relativeFrobenius p hS X).left ∧
      UniversallyInjective (Scheme.SmoothSite.relativeFrobenius p hS X).left :=
  ⟨inferInstance, inferInstance, inferInstance⟩

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
  (X : Scheme.SmoothSite (Spec (.of k))) [IsIntegral X.left]

example :
    IsIntegral (Scheme.SmoothSite.frobeniusTwist p (isInCharacteristic_spec k p) X).left :=
  inferInstance

example : ∃ r : ℕ,
    (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).left.residueDegree
      (genericPoint X.left) = p ^ r :=
  Scheme.Hom.residueDegree_eq_pow_of_expChar _
    (Scheme.SmoothSite.frobeniusTwist p (isInCharacteristic_spec k p) X).hom _ p

variable (P : PresheafWithTransfers.{v} k) (n : ℕ) (hn : IsUnit (n : k))
  (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
  (hT : Module.IsTorsionBy ℤ
    (sections P (Cor.mk (Scheme.SmoothSite.frobeniusTwist p (isInCharacteristic_spec k p) X)))
    (n : ℤ))

example : (relativeFrobeniusIso P p X n hn hX hT).hom =
    ((toPresheaf k).obj P).map
      (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).op := rfl

include hn hX hT in
example :
    ((toPresheaf k).obj P).map
        (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).op ≫
      (Nat.gcdA
          ((Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).left.residueDegree
            (genericPoint X.left)) n •
        transfer P (Cor.finiteFlatTranspose k
          (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X))) =
        𝟙 (sections P
          (Cor.mk (Scheme.SmoothSite.frobeniusTwist p (isInCharacteristic_spec k p) X))) :=
  (relativeFrobeniusIso P p X n hn hX hT).hom_inv_id

include hn hX hT in
example :
    (Nat.gcdA
        ((Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).left.residueDegree
          (genericPoint X.left)) n •
      transfer P (Cor.finiteFlatTranspose k
        (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X))) ≫
      ((toPresheaf k).obj P).map
        (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).op =
          𝟙 (sections P (Cor.mk X)) :=
  (relativeFrobeniusIso P p X n hn hX hT).inv_hom_id

include hn hX hT in
example : IsIso (((toPresheaf k).obj P).map
    (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).op) :=
  isIso_toPresheaf_map_relativeFrobenius P p X n hn hX hT

#print axioms AlgebraicGeometry.Smooth.exists_relativeDimension_neighborhood
#print axioms AlgebraicGeometry.flat_relativeFrobenius_of_smooth
#print axioms AlgebraicGeometry.Scheme.SmoothSite.relativeFrobenius
#print axioms AlgebraicGeometry.Scheme.SmoothSite.relativeFrobenius_isFinite
#print axioms AlgebraicGeometry.Scheme.SmoothSite.relativeFrobenius_flat
#print axioms AlgebraicGeometry.Scheme.SmoothSite.relativeFrobenius_universallyInjective
#print axioms AlgebraicGeometry.Scheme.SmoothSite.frobeniusTwist_isIntegral
#print axioms AlgebraicGeometry.PresheafWithTransfers.relativeFrobeniusIso
#print axioms AlgebraicGeometry.PresheafWithTransfers.isIso_toPresheaf_map_relativeFrobenius
