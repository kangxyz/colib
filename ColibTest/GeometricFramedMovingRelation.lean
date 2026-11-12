/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Divisors.GeometricFramedMovingRelation

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.ProjectiveCohomology
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors Stacks.Chow
open Stacks.SheafOfModules (schemeTensorPower)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace ColibTest

attribute [local instance] framedCorrectionInvertible framedCorrectionQuasicoherent
  framedCorrectionDifferenceInvertible framedCorrectionDifferenceAGInvertible
  framedCorrectionPullbackInvertible framedCorrectionPullbackAGInvertible
  framedCorrectionMulCommutative framedCorrectionTensorEquivalence framedCorrectionPowerInvertible
  movingTensorQuotientSecondInvertible movingTensorQuotientTensorInvertible

attribute [local instance] AlgebraicGeometry.geometricMovingTwistNativeInvertible

example
    (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] (n : ℕ)
    {X U V Y S : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [IsIntegral U] [IsNoetherian U] [U.IsQuasiAffine]
    [IsAffine V] [IsNoetherian V] [IsReduced V]
    (g : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion g]
    (q : X ⟶ V) [IsProper q] (i : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (p : V ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
    (r : U ⟶ Limits.pullback p t) (hr : r ≫ Limits.pullback.fst p t = j ≫ q)
    (σ τ : V ⟶ X) (hσ : σ ≫ q = 𝟙 V) (hτ : τ ≫ q = 𝟙 V)
    (σU τU : V ⟶ U) (hσU : σU ≫ j = σ) (hτU : τU ≫ j = τ)
    (hD : ∀ y : Spec (CommRingCat.of B), i y ∉ σ.ker.support)
    (hE : ∀ y : Spec (CommRingCat.of B), i y ∉ τ.ker.support)
    (L : X.Modules) [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
    (k : ℕ) (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf σ.ker τ.ker)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :
    let := sectionKernel_cartier_of_factor q j σ hσ σU hσU
    let := sectionKernel_cartier_of_factor q j τ hτ τU hτU
    ∀ (_hcompat : tensorPowerMap _ e (k + 1) ≪≫ structureSheafTensorPowerIso _ (k + 1) =
      (pullbackIntegerTensorPowerIso i L hL (k + 1)).symm ≪≫ (pullback i).mapIso α ≪≫
        differenceSheafBoundaryIso i σ.ker τ.ker hD hE),
    ∃ C : ℤ, ∀ d : ℤ, C ≤ d →
      let H := (pullback g).obj (twistingSheaf (polyGrading R n) d)
      ∃ eH : (pullback i).obj H ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf,
      ∃ (a : Γ(tensorObj L H, ⊤)) (b : H.sections) (ha0 : a ≠ 0)
        (hb0 : b.eval (op ⊤) ≠ 0),
      ∃ (hAfin : Stacks.Morphisms.IsFiniteLocallyFree
          ((AlgebraicGeometry.zeroScheme X (tensorObj L H) a).subschemeι ≫ q))
        (hBfin : Stacks.Morphisms.IsFiniteLocallyFree
          ((AlgebraicGeometry.zeroScheme X H (b.eval (op ⊤))).subschemeι ≫ q))
        (haU : Set.range (AlgebraicGeometry.zeroScheme X (tensorObj L H) a).subschemeι ⊆
          Set.range j)
        (hbU : Set.range (AlgebraicGeometry.zeroScheme X H (b.eval (op ⊤))).subschemeι ⊆
          Set.range j),
      let := hAfin
      let := hBfin
      let aM := meromorphicSectionOfGlobalSection (tensorObj L H) a
      let bM := meromorphicSectionOfGlobalSection H (b.eval (op ⊤))
      let haM := isRegularMeromorphicSection_meromorphicSectionOfGlobalSection _ a ha0
      let hbM := isRegularMeromorphicSection_meromorphicSectionOfGlobalSection H _ hb0
      let m := quotientTensorMeromorphicSection X L H aM bM hbM
      let hm := isRegularMeromorphicSection_quotientTensorMeromorphicSection X L H aM bM haM hbM
      let f := tensorPowerCorrectionRatio X L (differenceSheaf σ.ker τ.ker) m hm k α
        (canonicalDifferenceMeromorphicSection σ.ker τ.ker)
        (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection σ.ker τ.ker)
      Hom.app (pullbackTensorFrame i L H e eH).hom ⊤ (pullbackGlobalSections i _ a) =
        (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
      Hom.app eH.hom ⊤ (pullbackGlobalSections i H (b.eval (op ⊤))) =
        (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
      ∃ K : finiteCorrespondences p t,
        graphCorrespondenceOfComponents p t (σU ≫ r ≫ Limits.pullback.snd p t)
            (sectionTarget_base p t r σU
              (retainedSection_firstProjection p t q j r hr σ hσ σU hσU))
            (AlgebraicCycle.fundamentalCycle_genericPoints_finite V) -
          graphCorrespondenceOfComponents p t (τU ≫ r ≫ Limits.pullback.snd p t)
            (sectionTarget_base p t r τU
              (retainedSection_firstProjection p t q j r hr τ hτ τU hτU))
            (AlgebraicCycle.fundamentalCycle_genericPoints_finite V) =
          (k + 1) • (retainedFiniteFlatDivisorCorrespondence p t q j r hr
              (AlgebraicGeometry.zeroScheme X (tensorObj L H) a) haU -
            retainedFiniteFlatDivisorCorrespondence p t q j r hr
              (AlgebraicGeometry.zeroScheme X H (b.eval (op ⊤))) hbU) + K ∧
        K.val = WeilDivisor.pushforwardCycle r
          (principalDivisor U (rationalFunctionsUnitsMulEquivOfOpenImmersion j f)) ∧
        ∃ (W : DenseOpen X) (u : Γ(X, W.val)ˣ)
          (hBW : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ i ⁻¹ᵁ W.val),
          Units.map (ofSectionRingHom X W).toMonoidHom u = f ∧
          i.appLE W.val ⊤ hBW u.val = (1 : Γ(Spec (CommRingCat.of B), ⊤)) :=
  exists_geometric_framed_graph_moving_relation R B n g q i j hcover p t r hr
    σ τ hσ hτ σU τU hσU hτU hD hE L k α e

end ColibTest

#print axioms AlgebraicGeometry.sectionKernel_finiteLocallyFree
#print axioms AlgebraicGeometry.sectionKernel_cartier_of_factor
#print axioms AlgebraicGeometry.exists_geometric_framed_graph_moving_relation
