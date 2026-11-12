/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.NonzeroCompatiblePair
public import Colib.AlgebraicGeometry.Correspondences.Divisors.FramedMovingRelation
public import Colib.AlgebraicGeometry.Correspondences.Divisors.RetainedSectionGraph

/-!
# A geometric framed root produces the original graph moving relation

The two original sections supply their actual Cartier kernels and rank-one whole finite
locally free schemes. COL-1048 chooses the auxiliary twist, its frame and the actual nonzero
numerator and denominator. COL-1072 then produces the native signed finite-correspondence
identity and the same correction function normalized on the entire boundary. No divisor pair,
finite-locally-free certificates for it, or final signed identity is an input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.ProjectiveCohomology
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors Stacks.Chow
open Stacks.SheafOfModules (schemeTensorPower)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry

attribute [local instance] framedCorrectionInvertible framedCorrectionQuasicoherent
  framedCorrectionDifferenceInvertible framedCorrectionDifferenceAGInvertible
  framedCorrectionPullbackInvertible framedCorrectionPullbackAGInvertible
  framedCorrectionMulCommutative framedCorrectionTensorEquivalence framedCorrectionPowerInvertible
  movingTensorQuotientSecondInvertible movingTensorQuotientTensorInvertible

/-- The whole image scheme of an original section is finite locally free over the source. -/
theorem sectionKernel_finiteLocallyFree {X V : Scheme.{u}}
    (q : X ⟶ V) [IsSeparated q] (s : V ⟶ X) (hs : s ≫ q = 𝟙 V) :
    Stacks.Morphisms.IsFiniteLocallyFree (s.ker.subschemeι ≫ q) := by
  have := sectionKernelStructureMap_isIso q s hs
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- The full section-kernel scheme lies in the open through which the original section factors. -/
theorem sectionKernel_range_subset_of_factor {X U V : Scheme.{u}}
    (q : X ⟶ V) [IsSeparated q] (j : U ⟶ X)
    (s : V ⟶ X) (hs : s ≫ q = 𝟙 V) (sU : V ⟶ U) (hsU : sU ≫ j = s) :
    Set.range s.ker.subschemeι ⊆ Set.range j := by
  have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    s.isClosedEmbedding.isClosed_range.closure_eq, ← hsU]
  rintro _ ⟨v, rfl⟩
  exact ⟨sU v, rfl⟩

/-- Smoothness only on the retained open produces the original compactified Cartier kernel. -/
theorem sectionKernel_cartier_of_factor {X U V : Scheme.{u}}
    (q : X ⟶ V) [IsSeparated q] (j : U ⟶ X) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s : V ⟶ X) (hs : s ≫ q = 𝟙 V) (sU : V ⟶ U) (hsU : sU ≫ j = s) :
    IsEffectiveCartierDivisor s.ker := by
  apply isEffectiveCartierDivisor_sectionKernel_of_range_subset q j s hs
  rw [← hsU]
  rintro _ ⟨v, rfl⟩
  exact ⟨sU v, rfl⟩

local instance geometricMovingTwistNativeInvertible
    (R : Type u) [CommRing R] (n : ℕ) {X : Scheme.{u}}
    (g : X ⟶ Proj (polyGrading R n)) (d : ℤ) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      ((pullback g).obj (twistingSheaf (polyGrading R n) d)) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance

/-- The complete lower S1 construction: select the actual geometric pair internally and produce
its native relation between the two original graphs, with the unchanged root and full boundary. -/
@[colib_tag "COL-1079"]
theorem exists_geometric_framed_graph_moving_relation
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
          ((zeroScheme X (tensorObj L H) a).subschemeι ≫ q))
        (hBfin : Stacks.Morphisms.IsFiniteLocallyFree
          ((zeroScheme X H (b.eval (op ⊤))).subschemeι ≫ q))
        (haU : Set.range (zeroScheme X (tensorObj L H) a).subschemeι ⊆ Set.range j)
        (hbU : Set.range (zeroScheme X H (b.eval (op ⊤))).subschemeι ⊆ Set.range j),
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
              (zeroScheme X (tensorObj L H) a) haU -
            retainedFiniteFlatDivisorCorrespondence p t q j r hr
              (zeroScheme X H (b.eval (op ⊤))) hbU) + K ∧
        K.val = WeilDivisor.pushforwardCycle r
          (principalDivisor U (rationalFunctionsUnitsMulEquivOfOpenImmersion j f)) ∧
        ∃ (W : DenseOpen X) (u : Γ(X, W.val)ˣ)
          (hBW : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ i ⁻¹ᵁ W.val),
          Units.map (ofSectionRingHom X W).toMonoidHom u = f ∧
          i.appLE W.val ⊤ hBW u.val = (1 : Γ(Spec (CommRingCat.of B), ⊤)) := by
  dsimp only
  intro hcompat
  have := sectionKernel_cartier_of_factor q j σ hσ σU hσU
  have := sectionKernel_cartier_of_factor q j τ hτ τU hτU
  have := sectionKernel_finiteLocallyFree q σ hσ
  have := sectionKernel_finiteLocallyFree q τ hτ
  have hDU := sectionKernel_range_subset_of_factor q j σ hσ σU hσU
  have hEU := sectionKernel_range_subset_of_factor q j τ hτ τU hτU
  obtain ⟨C, hC⟩ := exists_nonzero_compatible_boundary_framed_divisor_pair
    R B n g q i j hcover L e
  refine ⟨C, fun d hd => ?_⟩
  let H := (pullback g).obj (twistingSheaf (polyGrading R n) d)
  obtain ⟨eH, a, b, ha0, hb0, haB, hbB, -, hAfin, haU, -, hBfin, hbU⟩ := hC d hd
  have : Stacks.Morphisms.IsFiniteLocallyFree
      ((zeroScheme X (tensorObj L H) a).subschemeι ≫ q) := hAfin
  have : Stacks.Morphisms.IsFiniteLocallyFree
      ((zeroScheme X H (b.eval (op ⊤))).subschemeι ≫ q) := hBfin
  refine ⟨eH, a, b, ha0, hb0, hAfin, hBfin, haU, hbU, haB, hbB, ?_⟩
  obtain ⟨K, hrel, hK, hbound⟩ := exists_retainedFiniteCorrespondence_tensorQuotientPower
    i σ.ker τ.ker L H j p t q r hr hDU hEU hD hE k α e eH hcompat
    a b ha0 hb0 haB hbB haU hbU
  refine ⟨K, ?_, hK, hbound⟩
  rw [retainedFiniteFlatDivisorCorrespondence_sectionKernel p t q j r hr σ hσ σU hσU hDU,
    retainedFiniteFlatDivisorCorrespondence_sectionKernel p t q j r hr τ hτ τU hτU hEU] at hrel
  exact hrel

end AlgebraicGeometry
