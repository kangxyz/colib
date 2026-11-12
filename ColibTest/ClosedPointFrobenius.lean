/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.IteratedFrobenius

/-! The closed point, residue scalar action, n-fold scheme pullback and original PST maps
remain literal. No perfectness, integrality, constant relative dimension, homotopy
invariance, geometric certificate or field-change equivalence is assumed. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers Stacks.Frobenius

universe v u

noncomputable section

variable {k : Type u} [Field k]

example [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := (fieldToResidue f x).hom.toAlgebra
    Module.Finite k (X.residueField x) ∧ Algebra.IsSeparable k (X.residueField x) :=
  finite_separable_residueField_of_isClosed_of_charZero f x hx

example (p : ℕ) [Fact p.Prime] [CharP k p] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ m : ℕ,
      let T := AlgebraicGeometry.nFoldFrobeniusTwist (Spec (.of k)) p
        (isInCharacteristic_spec k p) m (Over.mk f)
      let y := (AlgebraicGeometry.nFoldRelativeFrobenius (Spec (.of k)) p
        (isInCharacteristic_spec k p) m (Over.mk f)).left x
      IsClosed ({y} : Set T.left) ∧
        letI := (fieldToResidue T.hom y).hom.toAlgebra
        Algebra.IsSeparable k (T.left.residueField y) :=
  exists_isClosed_isSeparable_nFoldRelativeFrobenius_image p f x hx

variable (p : ℕ) [Fact p.Prime] (hk : IsInCharacteristic (Spec (.of k)) p)
  (m : ℕ) (X : SmoothSite (Spec (.of k)))

example : (SmoothSite.nFoldFrobeniusTwist p hk m X).left =
    pullback X.hom (absoluteFrobeniusPow (Spec (.of k)) p hk m) := rfl

example : (SmoothSite.nFoldRelativeFrobenius p hk m X).left =
    (AlgebraicGeometry.nFoldRelativeFrobenius (Spec (.of k)) p hk m
      ((SmoothSite.forget _).obj X)).left := rfl

example : IsFinite (SmoothSite.nFoldRelativeFrobenius p hk m X).left := inferInstance
example : Flat (SmoothSite.nFoldRelativeFrobenius p hk m X).left := inferInstance
example : UniversalHomeomorphism (SmoothSite.nFoldRelativeFrobenius p hk m X).left :=
  inferInstance

variable (P : PresheafWithTransfers.{v} k) (n : ℕ) (hn : IsUnit (n : k))
  (hP : ∀ W : SmoothSite (Spec (.of k)),
    Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ))

example : (nFoldRelativeFrobeniusIso P p hk m X n hn hP).hom =
    ((toPresheaf k).obj P).map (SmoothSite.nFoldRelativeFrobenius p hk m X).op := rfl

example : ((toPresheaf k).obj P).map (SmoothSite.nFoldRelativeFrobenius p hk m X).op ≫
    (nFoldRelativeFrobeniusIso P p hk m X n hn hP).inv =
      𝟙 (sections P (Cor.mk (SmoothSite.nFoldFrobeniusTwist p hk m X))) :=
  (nFoldRelativeFrobeniusIso P p hk m X n hn hP).hom_inv_id

example : (nFoldRelativeFrobeniusIso P p hk m X n hn hP).inv ≫
    ((toPresheaf k).obj P).map (SmoothSite.nFoldRelativeFrobenius p hk m X).op =
      𝟙 (sections P (Cor.mk X)) :=
  (nFoldRelativeFrobeniusIso P p hk m X n hn hP).inv_hom_id

example : (nFoldRelativeFrobeniusPresheafIso P p hk m n hn hP).hom.app (op X) =
    ((toPresheaf k).obj P).map (SmoothSite.nFoldRelativeFrobenius p hk m X).op := rfl

#print axioms finite_residueField_overField_of_isClosed
#print axioms finite_separable_residueField_of_isClosed_of_charZero
#print axioms isClosed_image_of_finite_fieldPoint
#print axioms isSeparable_residueField_of_fieldPoint
#print axioms absoluteFrobeniusPow_spec
#print axioms nFoldRelativeFrobenius_comp_natural
#print axioms exists_separableFieldPoint_nFoldRelativeFrobenius
#print axioms exists_isClosed_isSeparable_nFoldRelativeFrobenius_image
#print axioms SmoothSite.nFoldRelativeFrobenius_properties
#print axioms nFoldRelativeFrobeniusIso
#print axioms nFoldRelativeFrobeniusPresheafIso
#print axioms exists_separable_closedPoint_iteratedFrobenius_iso
