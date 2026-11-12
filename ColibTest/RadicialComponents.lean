/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.RadicialComponents

/-! Tests retain the original smooth schemes, maps, section groups and naturality squares.
No integrality, connectedness, homotopy-invariance or sheaf hypothesis is available below. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers

universe v u

noncomputable section

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  {X Y : SmoothSite (Spec (.of k))} (q : X ⟶ Y)
  [IsFinite q.left] [Flat q.left] [UniversalHomeomorphism q.left]
  (n : ℕ) (hn : IsUnit (n : k))
  (hP : ∀ W : SmoothSite (Spec (.of k)),
    Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ))

example : (radicialGraphIsoOfComponents P q n hn hP).hom =
    ((toPresheaf k).obj P).map q.op := rfl

example : ((toPresheaf k).obj P).map q.op ≫
    (radicialGraphIsoOfComponents P q n hn hP).inv = 𝟙 (sections P (Cor.mk Y)) :=
  (radicialGraphIsoOfComponents P q n hn hP).hom_inv_id

example : (radicialGraphIsoOfComponents P q n hn hP).inv ≫
    ((toPresheaf k).obj P).map q.op = 𝟙 (sections P (Cor.mk X)) :=
  (radicialGraphIsoOfComponents P q n hn hP).inv_hom_id

example : IsIso (((toPresheaf k).obj P).map q.op) :=
  isIso_toPresheaf_map_of_universalHomeomorphism P q n hn hP

example (Z : irreducibleComponents Y.left) :
    (integralComponentMap k q Z).left =
      pullback.fst (integralComponentι k Y Z).left q.left := rfl

example (Z : irreducibleComponents Y.left) :
    IsIntegral (integralComponentPullback k q Z).left := inferInstance

example (Z : irreducibleComponents Y.left) :
    Flat (integralComponentMap k q Z).left := inferInstance

example (p : ℕ) [Fact p.Prime]
    (hk : Stacks.Frobenius.IsInCharacteristic (Spec (.of k)) p) :
    (relativeFrobeniusPresheafIso P p hk n hn hP).hom.app (op X) =
      ((toPresheaf k).obj P).map (SmoothSite.relativeFrobenius p hk X).op := rfl

example (p : ℕ) [Fact p.Prime]
    (hk : Stacks.Frobenius.IsInCharacteristic (Spec (.of k)) p) (f : X ⟶ Y) :
    SmoothSite.relativeFrobenius p hk X ≫ (frobeniusTwistFunctor p hk).map f =
      f ≫ SmoothSite.relativeFrobenius p hk Y :=
  SmoothSite.relativeFrobenius_naturality p hk f

#print axioms Cor.sum_partialIdentity_eq_id
#print axioms Cor.exists_clopenFamily_projections
#print axioms SmoothSite.isIntegral_of_universalHomeomorphism
#print axioms SmoothSite.integralComponentMap_comm
#print axioms clopenFamily_sections_jointly_monic
#print axioms clopenFamilyGraphIso
#print axioms radicialGraphIsoOfComponents
#print axioms radicialGraphIsoOfComponents_inv
#print axioms relativeFrobeniusPresheafIso
