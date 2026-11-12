/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.FramedRetainedOpen
public import Colib.AlgebraicGeometry.Correspondences.Divisors.RetainedFiniteFlat
public import Colib.AlgebraicGeometry.Correspondences.Divisors.WeilIdentity

/-!
# The framed-root moving identity in native finite correspondences

The compactification's actual two zero schemes and two original divisors are finite locally
free and lie in the retained open, as supplied by the geometric divisor producer. Their full
scheme-theoretic restrictions define unchanged native correspondences. COL-1066 produces the
signed identity; native Weil restriction and the whole Cartier fundamental-cycle comparison
transport it to the original source-target product. No signed identity is an input. The
principal term is the actual pushforward of the same restricted rational function's divisor;
its identification with a polynomial-family endpoint remains a separate theorem.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Chow
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules (schemeTensorPower)

universe u

attribute [local instance] Stacks.Morphisms.IsFiniteLocallyFree.isFinite
  Stacks.Morphisms.IsFiniteLocallyFree.flat
  Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation

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

local instance movingTensorQuotientSecondInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N := hN.toAlgebraicGeometry

local instance movingTensorQuotientTensorInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorObj L N) :=
  (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    L N).toAlgebraicGeometry

/-- The actual framed quotient produces the signed identity in native finite correspondences
on the retained open, with the original full-boundary normalization certificate. -/
@[colib_tag "COL-1072"]
theorem exists_retainedFiniteCorrespondence_tensorQuotientPower [IsNoetherian X]
    {U : Scheme.{u}} [IsNoetherian U] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    {V Y S : Scheme.{u}} (p : V ⟶ S) (t : Y ⟶ S)
    [IsSeparated t] [LocallyOfFiniteType t]
    (q : X ⟶ V) (r : U ⟶ Limits.pullback p t)
    (hr : r ≫ Limits.pullback.fst p t = j ≫ q)
    (hDU : Set.range D.subschemeι ⊆ Set.range j)
    (hEU : Set.range E.subschemeι ⊆ Set.range j)
    [Stacks.Morphisms.IsFiniteLocallyFree (D.subschemeι ≫ q)]
    [Stacks.Morphisms.IsFiniteLocallyFree (E.subschemeι ≫ q)]
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
      (1 : Γ(B, ⊤)))
    (haU : Set.range (zeroScheme X (tensorObj L N) a).subschemeι ⊆ Set.range j)
    (hbU : Set.range (zeroScheme X N (b.eval (op ⊤))).subschemeι ⊆ Set.range j)
    [Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme X (tensorObj L N) a).subschemeι ≫ q)]
    [Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme X N (b.eval (op ⊤))).subschemeι ≫ q)] :
    let aM := meromorphicSectionOfGlobalSection (tensorObj L N) a
    let bM := meromorphicSectionOfGlobalSection N (b.eval (op ⊤))
    let haM := isRegularMeromorphicSection_meromorphicSectionOfGlobalSection (tensorObj L N) a ha0
    let hbM := isRegularMeromorphicSection_meromorphicSectionOfGlobalSection N _ hb0
    let m := quotientTensorMeromorphicSection X L N aM bM hbM
    let hm := isRegularMeromorphicSection_quotientTensorMeromorphicSection X L N aM bM haM hbM
    let f := tensorPowerCorrectionRatio X L (differenceSheaf D E) m hm k α
      (canonicalDifferenceMeromorphicSection D E)
      (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E)
    ∃ K : finiteCorrespondences p t,
      retainedFiniteFlatDivisorCorrespondence p t q j r hr D hDU -
        retainedFiniteFlatDivisorCorrespondence p t q j r hr E hEU =
          (k + 1) • (retainedFiniteFlatDivisorCorrespondence p t q j r hr
              (zeroScheme X (tensorObj L N) a) haU -
            retainedFiniteFlatDivisorCorrespondence p t q j r hr
              (zeroScheme X N (b.eval (op ⊤))) hbU) + K ∧
      K.val = WeilDivisor.pushforwardCycle r
        (principalDivisor U (rationalFunctionsUnitsMulEquivOfOpenImmersion j f)) ∧
    ∃ (W : Stacks.Chow.DenseOpen X) (u : Γ(X, W.val)ˣ)
      (hBW : (⊤ : B.Opens) ≤ i ⁻¹ᵁ W.val),
      Units.map (Stacks.Chow.ofSectionRingHom X W).toMonoidHom u = f ∧
      i.appLE W.val ⊤ hBW u.val = (1 : Γ(B, ⊤)) := by
  have h := exists_signedCartierDifference_tensorQuotientPower_on_open i D E L N j
    hD hE k α e eN hcompat a b ha0 hb0 haB hbB
  dsimp only at h ⊢
  have := retainedDivisor_firstProjection_finiteLocallyFree p t q j r hr D hDU
  have := retainedDivisor_firstProjection_finiteLocallyFree p t q j r hr E hEU
  have := retainedDivisor_firstProjection_finiteLocallyFree p t q j r hr
    (zeroScheme X (tensorObj L N) a) haU
  have := retainedDivisor_firstProjection_finiteLocallyFree p t q j r hr
    (zeroScheme X N (b.eval (op ⊤))) hbU
  refine ⟨principalCorrespondenceOfWeilIdentity p t r (D.comap j) (E.comap j)
      ((zeroScheme X (tensorObj L N) a).comap j)
      ((zeroScheme X N (b.eval (op ⊤))).comap j)
      (isPullbackDefined_of_flat j D inferInstance)
      (isPullbackDefined_of_flat j E inferInstance)
      (isPullbackDefined_of_flat j _
        (isEffectiveCartierDivisor_zeroScheme_of_ne_zero (tensorObj L N) a ha0))
      (isPullbackDefined_of_flat j _
        (isEffectiveCartierDivisor_zeroScheme_of_ne_zero N _ hb0))
      (k + 1) _ h.1, ?_, rfl, h.2⟩
  exact finiteFlatDivisorCorrespondence_sub_eq_of_weilIdentity p t r _ _ _ _
    (isPullbackDefined_of_flat j D inferInstance)
    (isPullbackDefined_of_flat j E inferInstance)
    (isPullbackDefined_of_flat j _
      (isEffectiveCartierDivisor_zeroScheme_of_ne_zero (tensorObj L N) a ha0))
    (isPullbackDefined_of_flat j _
      (isEffectiveCartierDivisor_zeroScheme_of_ne_zero N _ hb0))
    (k + 1) _ h.1

end AlgebraicGeometry
