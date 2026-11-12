/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSectionKernels
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryDiagram
public import Colib.AlgebraicGeometry.Divisors.SectionKernelSmoothOpen
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-! # Cartier original sections and the entire boundary on component stages

The only smoothness and disjointness inputs belong to the fixed original stage.
Actual etale transitions transport the full section kernels and full boundary.
This candidate has not yet been compiled.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Stacks.Divisors
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
  (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
  [IsClosedImmersion σ]

/-- The fixed original kernel, not a substituted divisor, pulls back to every stage. -/
theorem etaleStageOpenSection_ker_fixed (a : Over i) :
    (etaleStageOpenSection X s p i U σ hσ a).ker =
      σ.ker.comap (pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι) := by
  exact Scheme.ker_eq_comap_of_isPullback _ _ _ _
    (Scheme.isPullback_section_of_isPullback _ _ _ _
      (etaleStageOpenStructure_isPullback X s p i U a)
      (etaleStageOpenSection X s p i U σ hσ a) σ
      (etaleStageOpenSection_structure X s p i U σ hσ a) hσ
      (etaleStageOpenSection_snd X s p i U σ hσ a))

/-- Smoothness is used only on the fixed retained open containing the original section. -/
theorem etaleStageOpenSection_isEffectiveCartierDivisor
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    {V : Scheme.{u}} (j : V ⟶ U.toScheme) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))]
    (hσj : Set.range σ ⊆ Set.range j) (a : Over i) :
    IsEffectiveCartierDivisor (etaleStageOpenSection X s p i U σ hσ a).ker := by
  have hc := isEffectiveCartierDivisor_sectionKernel_of_range_subset
    (U.ι ≫ (etaleCurveStructure X s p).app i) j σ hσ hσj
  have hb : Etale ((smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom) := by
    change Etale (((AffineEtale.Spec X.left).map
      (((smallEtaleNeighborhoodInclusion X s).map a.hom).hom)).left)
    infer_instance
  have hf : Etale (pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι) :=
    MorphismProperty.of_isPullback (P := @Etale)
      (etaleStageOpenStructure_isPullback X s p i U a).flip hb
  have : Flat (pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι) := inferInstance
  rw [etaleStageOpenSection_ker_fixed X s p i U σ hσ a]
  exact isPullbackDefined_of_flat _ σ.ker hc

/-- Geometric disjointness at the fixed stage excludes the entire boundary from
all actual section-kernel supports; neither boundary nor ideal is reduced. -/
theorem etaleStageOpenSection_boundary_avoids
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    (hdisj : ∀ z : Z, d z ∉ Set.range σ) (a : Over i) :
    ∀ z : (etaleStageOpenBoundaryDiagram X s p i U d).obj a,
      (etaleStageOpenBoundaryMap X s p i U d).app a z ∉
        (etaleStageOpenSection X s p i U σ hσ a).ker.support := by
  intro z
  rw [etaleStageOpenSection_ker_fixed X s p i U σ hσ a,
    Scheme.IdealSheafData.support_comap]
  have hw := congrArg (fun f => f z)
    (etaleStageOpenBoundaryMap_isPullback X s p i U d a).w
  change (pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι)
    ((etaleStageOpenBoundaryMap X s p i U d).app a z) ∉ σ.ker.support
  rw [hw, Scheme.Hom.support_ker,
    σ.isClosedEmbedding.isClosed_range.closure_eq]
  exact hdisj _

end AlgebraicGeometry.Scheme.SmoothSite
