/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.FramedPowerCorrection

/-! The exact root correction uses the original canonical target frame on arbitrary full B. -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules (schemeTensorPower)

universe u

noncomputable section

attribute [local instance] AlgebraicGeometry.framedCorrectionInvertible
  AlgebraicGeometry.framedCorrectionQuasicoherent
  AlgebraicGeometry.framedCorrectionDifferenceAGInvertible
  AlgebraicGeometry.framedCorrectionPullbackInvertible
  AlgebraicGeometry.framedCorrectionPullbackAGInvertible
  AlgebraicGeometry.framedCorrectionMulCommutative
  AlgebraicGeometry.framedCorrectionTensorEquivalence

example {X B : Scheme.{u}} [IsIntegral X] (i : B ⟶ X)
    (D E : X.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    (L : X.Modules) [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (k : ℕ) (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf D E)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (ringSheaf B))
    (hcompat : tensorPowerMap B e (k + 1) ≪≫ structureSheafTensorPowerIso B (k + 1) =
      (pullbackIntegerTensorPowerIso i L hL (k + 1)).symm ≪≫ (pullback i).mapIso α ≪≫
        differenceSheafBoundaryIso i D E hD hE)
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    (U : X.Opens) (hη : genericPoint X ∈ U) (hB : i ⁻¹ᵁ U = ⊤) (m : Γ(L, U))
    (hm : meromorphicGenericValue X L s = L.presheaf.germ U (genericPoint X) hη m)
    (hmB : Hom.app e.hom ⊤ (pullbackSectionHom i L U ⊤ hB.ge m) = (1 : Γ(B, ⊤))) :
    ∃ (W : Stacks.Chow.DenseOpen X) (u : Γ(X, W.val)ˣ)
      (hBW : (⊤ : B.Opens) ≤ i ⁻¹ᵁ W.val),
      Units.map (Stacks.Chow.ofSectionRingHom X W).toMonoidHom u =
        tensorPowerCorrectionRatio X L (differenceSheaf D E) s hs k α
          (canonicalDifferenceMeromorphicSection D E)
          (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E) ∧
      i.appLE W.val ⊤ hBW u.val = (1 : Γ(B, ⊤)) :=
  exists_denseOpen_unit_tensorPowerCorrectionRatio_boundary_one i D E L hD hE k α e
    hcompat s hs U hη hB m hm hmB

#print axioms AlgebraicGeometry.exists_denseOpen_unit_tensorPowerCorrectionRatio_boundary_one
