/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineFrameParameterAction
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineSpaceThom
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.TrivialThomOrientation

/-!
# The normalized Thom class under a change of frame

The two specializations of the universal determinant open induce the
same restriction on the supported class after cancellation. The
literal matrix-coordinate maps identify the two specialized actions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private theorem comp_eq_of_parallel_sections {C : Type*} [Category* C] {A B K : C}
    (a : A ⟶ A) (u : B ⟶ B) (s t : A ⟶ B) (τ : B ⟶ K) (ξ : A ⟶ K)
    (hs : a ≫ s = s ≫ u) (ht : t ≫ u = t)
    (hₛ : s ≫ τ = ξ) (hₜ : t ≫ τ = ξ)
    (he : s ≫ u ≫ τ = t ≫ u ≫ τ) : a ≫ ξ = ξ := by
  have hs' : a ≫ ξ = s ≫ u ≫ τ :=
    (congrArg (a ≫ ·) hₛ.symm).trans ((Category.assoc a s τ).symm.trans
      ((congrArg (· ≫ τ) hs).trans (Category.assoc s u τ)))
  have ht' : t ≫ u ≫ τ = ξ :=
    (Category.assoc t u τ).symm.trans ((congrArg (· ≫ τ) ht).trans hₜ)
  exact hs'.trans (he.trans ht')

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "M" => effectiveSmoothMotive k
local notation "Φ" => effectivePairMotiveFunctor k
local notation "F(" n ")" => Stabilization.iterate (effectiveLefschetzTwistFunctor k) n

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable
  effectiveAffineSpaceThomIso

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 850000 in
-- Use the actual affine Thom maps to transport equality of the parameter restrictions.
private theorem effectiveAffineSpaceThomClass_parallel_restrictions
    {X Y : Sm} [IsAffine X.left] [IsAffine Y.left] [IsIntegral Y.left]
    (s t : X ⟶ Y) (n : ℕ)
    (c : effectiveMotiveWithSupport k (relativeAffineSpaceZeroSection Y n) ⟶
      (F(n)).obj ((M).obj (base (Spec (CommRingCat.of k))))) :
    let s₀ := closedSupportArrowMap
      (i := relativeAffineSpaceZeroSection X n) (j := relativeAffineSpaceZeroSection Y n)
      (f := affineSpaceObjectMap s n) (g := s) (affineSpaceOrigin_isPullback s n)
    let t₀ := closedSupportArrowMap
      (i := relativeAffineSpaceZeroSection X n) (j := relativeAffineSpaceZeroSection Y n)
      (f := affineSpaceObjectMap t n) (g := t) (affineSpaceOrigin_isPullback t n)
    (Φ).map s₀ ≫ c = (Φ).map t₀ ≫ c := by
  intro s₀ t₀
  let e := effectiveAffineSpaceThomIso k X n
  let e' := effectiveAffineSpaceThomIso k Y n
  have hₛ : (Φ).map s₀ ≫ e'.hom = e.hom ≫ (F(n)).map ((M).map s) :=
    effectiveAffineSpaceThomIso_naturality k s n
  have hₜ : (Φ).map t₀ ≫ e'.hom = e.hom ≫ (F(n)).map ((M).map t) :=
    effectiveAffineSpaceThomIso_naturality k t n
  exact iterateLefschetz_baseHom_precomp_eq_of_iso k n s t e.hom e' ((Φ).map s₀) ((Φ).map t₀)
    hₛ hₜ c

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1200000 in
-- The literal matrix action and its two graph restrictions determine the supported class.
/-- The normalized Thom class of a trivial bundle is invariant under every
invertible linear change of its affine coordinates. -/
theorem effectiveAffineSpaceThomClass_matrixMap (X : Sm) [IsAffine X.left] [IsIntegral X.left]
    (n : ℕ) (A : (Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) Γ(X.left, ⊤))ˣ) :
    effectiveMotiveWithSupportMap k
        (i := relativeAffineSpaceZeroSection X n) (j := relativeAffineSpaceZeroSection X n)
        (f := affineSpaceObjectMatrixMap X n A.val) (g := 𝟙 X)
        (affineSpaceOrigin_matrixMap_isPullback X n A) ≫
      effectiveAffineSpaceThomClass k X n = effectiveAffineSpaceThomClass k X n := by
  let I := ULift.{u} (Fin n)
  let R := Γ(X.left, ⊤)
  let Y : Sm := frameParameterObject I X
  let : IsAffine Y.left := frameParameterObject_isAffine I X
  let : IsIntegral Y.left := frameParameterObject_isIntegral I X
  let s : X ⟶ Y := frameParameterSmoothSection I X A
  let t : X ⟶ Y := frameParameterSmoothSection I X (1 : (Matrix I I R)ˣ)
  let s₀ := closedSupportArrowMap
    (i := relativeAffineSpaceZeroSection X n) (j := relativeAffineSpaceZeroSection Y n)
    (f := affineSpaceObjectMap s n) (g := s) (affineSpaceOrigin_isPullback s n)
  let t₀ := closedSupportArrowMap
    (i := relativeAffineSpaceZeroSection X n) (j := relativeAffineSpaceZeroSection Y n)
    (f := affineSpaceObjectMap t n) (g := t) (affineSpaceOrigin_isPullback t n)
  let u₀ := affineSpaceFrameParameterMap X n
  let a₀ := affineSpaceMatrixSupportArrowMap X n A
  have hs : s₀ ≫ u₀ = a₀ ≫ s₀ := affineSpaceFrameParameterMap_specialize X n A
  have ht : t₀ ≫ u₀ = t₀ := affineSpaceFrameParameterMap_specialize_one X n
  let τ := effectiveAffineSpaceThomClass k Y n
  let q := (Φ).map u₀ ≫ τ
  have hsection : (Φ).map s₀ ≫ q = (Φ).map t₀ ≫ q :=
    effectiveAffineSpaceThomClass_parallel_restrictions k s t n q
  have hrestrict : (Φ).map s₀ ≫ τ = effectiveAffineSpaceThomClass k X n :=
    effectiveAffineSpaceThomClass_naturality k s n
  have hrestrict' : (Φ).map t₀ ≫ τ = effectiveAffineSpaceThomClass k X n :=
    effectiveAffineSpaceThomClass_naturality k t n
  have hmapₛ : (Φ).map a₀ ≫ (Φ).map s₀ = (Φ).map s₀ ≫ (Φ).map u₀ :=
    ((Φ).map_comp a₀ s₀).symm.trans
      ((congrArg (Φ).map hs.symm).trans ((Φ).map_comp s₀ u₀))
  have hmapₜ : (Φ).map t₀ ≫ (Φ).map u₀ = (Φ).map t₀ :=
    ((Φ).map_comp t₀ u₀).symm.trans (congrArg (Φ).map ht)
  exact comp_eq_of_parallel_sections ((Φ).map a₀) ((Φ).map u₀) ((Φ).map s₀) ((Φ).map t₀)
    τ (effectiveAffineSpaceThomClass k X n) hmapₛ hmapₜ hrestrict hrestrict' hsection

end AlgebraicGeometry.MotivicHomotopy
