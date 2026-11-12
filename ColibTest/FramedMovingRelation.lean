/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Divisors.FramedMovingRelation

noncomputable section

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

namespace ColibTest

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

example [IsNoetherian X]
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
    (haU : Set.range (AlgebraicGeometry.zeroScheme X (tensorObj L N) a).subschemeι ⊆ Set.range j)
    (hbU : Set.range (AlgebraicGeometry.zeroScheme X N (b.eval (op ⊤))).subschemeι ⊆ Set.range j)
    [Stacks.Morphisms.IsFiniteLocallyFree
      ((AlgebraicGeometry.zeroScheme X (tensorObj L N) a).subschemeι ≫ q)]
    [Stacks.Morphisms.IsFiniteLocallyFree
      ((AlgebraicGeometry.zeroScheme X N (b.eval (op ⊤))).subschemeι ≫ q)] :
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
              (AlgebraicGeometry.zeroScheme X (tensorObj L N) a) haU -
            retainedFiniteFlatDivisorCorrespondence p t q j r hr
              (AlgebraicGeometry.zeroScheme X N (b.eval (op ⊤))) hbU) + K ∧
      K.val = WeilDivisor.pushforwardCycle r
        (principalDivisor U (rationalFunctionsUnitsMulEquivOfOpenImmersion j f)) ∧
    ∃ (W : Stacks.Chow.DenseOpen X) (u : Γ(X, W.val)ˣ)
      (hBW : (⊤ : B.Opens) ≤ i ⁻¹ᵁ W.val),
      Units.map (Stacks.Chow.ofSectionRingHom X W).toMonoidHom u = f ∧
      i.appLE W.val ⊤ hBW u.val = (1 : Γ(B, ⊤)) :=
  exists_retainedFiniteCorrespondence_tensorQuotientPower i D E L N j p t q r hr
    hDU hEU hD hE k α e eN hcompat a b ha0 hb0 haB hbB haU hbU

end ColibTest

#print axioms AlgebraicGeometry.exists_retainedFiniteCorrespondence_tensorQuotientPower
