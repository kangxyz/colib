/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSections

/-! # Original section kernels through the four descent refinements

All kernels are those of the constructed original sections. The iterated comaps
retain the exact nested order of original-root and auxiliary descent.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
  (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _) [IsClosedImmersion σ]

/-- The actual lifted section is closed by its Cartesian square with the original section. -/
instance etaleStageOpenSection_isClosedImmersion (a : Over i) :
    IsClosedImmersion (etaleStageOpenSection X s p i U σ hσ a) := by
  have h := Scheme.isPullback_section_of_isPullback
    (pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι)
    ((etaleStageOpenStructure X s p i U).app a)
    (U.ι ≫ (etaleCurveStructure X s p).app i)
    ((smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom)
    (etaleStageOpenStructure_isPullback X s p i U a)
    (etaleStageOpenSection X s p i U σ hσ a) σ
    (etaleStageOpenSection_structure X s p i U σ hσ a) hσ
    (etaleStageOpenSection_snd X s p i U σ hσ a)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance

/-- Exact full-kernel base change for an actual component-stage section transition. -/
theorem etaleStageOpenSection_ker {a b : Over i} (v : a ⟶ b) :
    (etaleStageOpenSection X s p i U σ hσ a).ker =
      (etaleStageOpenSection X s p i U σ hσ b).ker.comap
        ((etaleStageOpenDiagram X s p i U).map v) :=
  Scheme.ker_eq_comap_of_isPullback _ _ _ _
    (etaleStageOpenSection_isPullback X s p i U σ hσ v)

/-- The four native descent refinements give the actual final section kernel,
without identifying an iterated pullback functor with a composite functor. -/
theorem etaleStageOpenSection_ker_four
    {a₀ a₁ a₂ a₃ a₄ : Over i}
    (e : a₁ ⟶ a₀) (f : a₂ ⟶ a₁) (g : a₃ ⟶ a₂) (h : a₄ ⟶ a₃) :
    (etaleStageOpenSection X s p i U σ hσ a₄).ker =
      ((((etaleStageOpenSection X s p i U σ hσ a₀).ker.comap
        ((etaleStageOpenDiagram X s p i U).map e)).comap
        ((etaleStageOpenDiagram X s p i U).map f)).comap
        ((etaleStageOpenDiagram X s p i U).map g)).comap
        ((etaleStageOpenDiagram X s p i U).map h) := by
  rw [etaleStageOpenSection_ker X s p i U σ hσ h,
    etaleStageOpenSection_ker X s p i U σ hσ g,
    etaleStageOpenSection_ker X s p i U σ hσ f,
    etaleStageOpenSection_ker X s p i U σ hσ e]

end AlgebraicGeometry.Scheme.SmoothSite
