/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.FramedTensorQuotientCorrection
public import Colib.AlgebraicGeometry.Divisors.WeilOpenRestriction

/-!
# The produced framed correction on the retained open

The literal signed identity is produced from the original tensor root and the two original
sections by COL-1066, then restricted along the actual open immersion. Its four Cartier
ideals are the full scheme-theoretic inverse images, not reduced supports. The rational
function is the native restriction of the same original correcting function. Its full-boundary
ordinary unit certificate remains on the compactification, since the boundary is disjoint
from the retained curve open rather than a subscheme of it.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules (schemeTensorPower)

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry

attribute [local instance] framedCorrectionInvertible framedCorrectionQuasicoherent
  framedCorrectionDifferenceInvertible framedCorrectionDifferenceAGInvertible
  framedCorrectionPullbackInvertible framedCorrectionPullbackAGInvertible
  framedCorrectionMulCommutative framedCorrectionTensorEquivalence framedCorrectionPowerInvertible

variable {X B : Scheme.{u}} [IsIntegral X] (i : B ⟶ X)
  (D E : X.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
  (L N : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
  [hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N]

local instance retainedTensorQuotientSecondInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N := hN.toAlgebraicGeometry

local instance retainedTensorQuotientTensorInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorObj L N) :=
  (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    L N).toAlgebraicGeometry

/-- The original framed quotient produces a literal signed Weil identity on the actual
retained open. No divisor or correspondence identity is assumed. -/
@[colib_tag "COL-1072"]
theorem exists_signedCartierDifference_tensorQuotientPower_on_open [IsNoetherian X]
    {U : Scheme.{u}} [IsNoetherian U] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (k : ℕ) (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf D E)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (ringSheaf B))
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (hcompat : tensorPowerMap B e (k + 1) ≪≫ structureSheafTensorPowerIso B (k + 1) =
      (pullbackIntegerTensorPowerIso i L hL (k + 1)).symm ≪≫ (pullback i).mapIso α ≪≫
        differenceSheafBoundaryIso i D E hD hE)
    (a : Γ(tensorObj L N, ⊤)) (b : N.sections) (ha0 : a ≠ 0) (hb0 : b.eval (op ⊤) ≠ 0)
    (haB : Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i (tensorObj L N) a) = (1 : Γ(B, ⊤)))
    (hbB : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) =
      (1 : Γ(B, ⊤))) :
    let aM := meromorphicSectionOfGlobalSection (tensorObj L N) a
    let bM := meromorphicSectionOfGlobalSection N (b.eval (op ⊤))
    let haM := isRegularMeromorphicSection_meromorphicSectionOfGlobalSection (tensorObj L N) a ha0
    let hbM := isRegularMeromorphicSection_meromorphicSectionOfGlobalSection N _ hb0
    let m := quotientTensorMeromorphicSection X L N aM bM hbM
    let hm := isRegularMeromorphicSection_quotientTensorMeromorphicSection X L N aM bM haM hbM
    let f := tensorPowerCorrectionRatio X L (differenceSheaf D E) m hm k α
      (canonicalDifferenceMeromorphicSection D E)
      (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E)
    effectiveCartierWeilDivisor (D.comap j) (isPullbackDefined_of_flat j D inferInstance) -
      effectiveCartierWeilDivisor (E.comap j) (isPullbackDefined_of_flat j E inferInstance) =
      (k + 1) • (effectiveCartierWeilDivisor ((zeroScheme X (tensorObj L N) a).comap j)
          (isPullbackDefined_of_flat j _
            (isEffectiveCartierDivisor_zeroScheme_of_ne_zero (tensorObj L N) a ha0)) -
        effectiveCartierWeilDivisor ((zeroScheme X N (b.eval (op ⊤))).comap j)
          (isPullbackDefined_of_flat j _
            (isEffectiveCartierDivisor_zeroScheme_of_ne_zero N _ hb0))) +
        principalDivisor U (Stacks.Chow.rationalFunctionsUnitsMulEquivOfOpenImmersion j f) ∧
    ∃ (W : Stacks.Chow.DenseOpen X) (u : Γ(X, W.val)ˣ)
      (hBW : (⊤ : B.Opens) ≤ i ⁻¹ᵁ W.val),
      Units.map (Stacks.Chow.ofSectionRingHom X W).toMonoidHom u = f ∧
      i.appLE W.val ⊤ hBW u.val = (1 : Γ(B, ⊤)) := by
  have h := exists_signedCartierDifference_tensorQuotientPower_boundary_one i D E L N
    hD hE k α e eN hcompat a b ha0 hb0 haB hbB
  dsimp only at h ⊢
  refine ⟨?_, h.2⟩
  have hdiv := congrArg (OpenWeilRestriction.restrictWeil j) h.1
  simpa only [map_sub, map_add, map_nsmul,
    OpenWeilRestriction.restrictWeil_effectiveCartierWeilDivisor,
    OpenWeilRestriction.restrictWeil_principalDivisor] using hdiv

end AlgebraicGeometry
