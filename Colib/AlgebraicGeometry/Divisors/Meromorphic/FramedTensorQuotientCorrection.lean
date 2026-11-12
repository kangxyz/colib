/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.FramedPowerCorrection
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.GlobalSectionWeilDivisor
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotientGeneric

/-!
# A framed tensor root gives the actual signed Cartier-divisor correction

The quotient is formed from the original numerator and denominator. The correcting rational
function is the frozen native ratio of the original canonical section by its root power.
An actual ordinary unit on a produced dense open represents this same function and has
literal value one on the entire, possibly nonreduced boundary.
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

local instance framedTensorQuotientSecondInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N := hN.toAlgebraicGeometry

local instance framedTensorQuotientTensorInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorObj L N) :=
  (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    L N).toAlgebraicGeometry

/-- The correcting function for the literal quotient of the original two global sections
has an actual unit representative normalized on the full original boundary. -/
@[colib_tag "COL-1066"]
theorem exists_denseOpen_unit_tensorQuotientPowerCorrection_boundary_one
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
    ∃ (W : Stacks.Chow.DenseOpen X) (u : Γ(X, W.val)ˣ)
      (hBW : (⊤ : B.Opens) ≤ i ⁻¹ᵁ W.val),
      Units.map (Stacks.Chow.ofSectionRingHom X W).toMonoidHom u =
        tensorPowerCorrectionRatio X L (differenceSheaf D E) m hm k α
          (canonicalDifferenceMeromorphicSection D E)
          (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E) ∧
      i.appLE W.val ⊤ hBW u.val = (1 : Γ(B, ⊤)) := by
  dsimp only
  let V := Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b
  let := Stacks.SheafOfModules.Scheme.isIso_over_nonvanishingOpen X N b
  apply exists_denseOpen_unit_tensorPowerCorrectionRatio_boundary_one i D E L hD hE k α e
    hcompat _ _ V (genericPoint_mem_nonvanishingOpen_of_eval_top_ne_zero N b hb0)
    (preimage_nonvanishingOpen_eq_top_of_boundary_frame i N b eN hbB)
    (regularTensorQuotientOnNonvanishingOpen X L N b a)
  · exact meromorphicGenericValue_quotient_eq_germ_regularTensorQuotient X L N b hb0 V
      (genericPoint_mem_nonvanishingOpen_of_eval_top_ne_zero N b hb0) a
  · exact frame_boundaryRegularTensorQuotient_eq_one i L N b e eN a haB hbB

/-- The literal signed Weil-divisor equality uses the actual original Cartier zero schemes
of `a` and `b`, with the correcting principal divisor having the positive sign. That same
correcting function is represented by an ordinary unit equal to one on the full boundary. -/
@[colib_tag "COL-1066",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/Meromorphic/SectionRatio.lean:242-252"
    "ingredient" "The literal native ratio divisor has numerator c and the positive principal sign",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/RegularSectionIntegral.lean:171-184"
    "ingredient" "The unchanged global sections produce their actual Cartier zero schemes"]
theorem exists_signedCartierDifference_tensorQuotientPower_boundary_one [IsNoetherian X]
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
    effectiveCartierWeilDivisor D inferInstance - effectiveCartierWeilDivisor E inferInstance =
      (k + 1) • (effectiveCartierWeilDivisor (zeroScheme X (tensorObj L N) a)
          (isEffectiveCartierDivisor_zeroScheme_of_ne_zero (tensorObj L N) a ha0) -
        effectiveCartierWeilDivisor (zeroScheme X N (b.eval (op ⊤)))
          (isEffectiveCartierDivisor_zeroScheme_of_ne_zero N _ hb0)) + principalDivisor X f ∧
    ∃ (W : Stacks.Chow.DenseOpen X) (u : Γ(X, W.val)ˣ)
      (hBW : (⊤ : B.Opens) ≤ i ⁻¹ᵁ W.val),
      Units.map (Stacks.Chow.ofSectionRingHom X W).toMonoidHom u = f ∧
      i.appLE W.val ⊤ hBW u.val = (1 : Γ(B, ⊤)) := by
  dsimp only
  constructor
  · have h := weilDivisor_eq_smul_sub_add_principal_tensorQuotientPower X L
      (differenceSheaf D E) N
      (meromorphicSectionOfGlobalSection (tensorObj L N) a)
      (meromorphicSectionOfGlobalSection N (b.eval (op ⊤)))
      (isRegularMeromorphicSection_meromorphicSectionOfGlobalSection (tensorObj L N) a ha0)
      (isRegularMeromorphicSection_meromorphicSectionOfGlobalSection N _ hb0) k α
      (canonicalDifferenceMeromorphicSection D E)
      (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E)
    dsimp only at h
    refine (weilDivisorOfMeromorphicSection_canonicalDifference D E).symm.trans (h.trans ?_)
    exact congrArg (fun z : WeilDivisor X => (k + 1) • z + _)
      (congrArg₂ (fun A B : WeilDivisor X => A - B)
        (weilDivisorOfMeromorphicSection_globalSection_eq_zeroScheme (tensorObj L N) a ha0)
        (weilDivisorOfMeromorphicSection_globalSection_eq_zeroScheme N
          (show Γ(N, ⊤) from b.eval (op ⊤)) hb0))
  · exact exists_denseOpen_unit_tensorQuotientPowerCorrection_boundary_one i D E L N
      hD hE k α e eN hcompat a b ha0 hb0 haB hbB

end AlgebraicGeometry
