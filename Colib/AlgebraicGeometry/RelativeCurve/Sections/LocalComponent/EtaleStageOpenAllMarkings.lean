/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitSameClosedFibre

/-! # The original pair agrees at every actual finite-stage marking -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
  (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
  (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
  (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)

include B hX

/-- Agreement at one original stage propagates through the actual limit to every stage.
This includes the final stage selected by the same-root descent. -/
theorem etaleStageOpenSection_same_marking_of_one (a0 a : Over i)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U σ hσ a0 =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U τ hτ a0) :
    etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫
          etaleStageOpenSection X s p i U σ hσ a =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫
          etaleStageOpenSection X s p i U τ hτ a := by
  have h := congrArg (fun t => t ≫ (etaleStageOpenCone X s p i U B hX).π.app a)
    (etaleStageOpenLimitSection_same_geometric_mark X s p i U B hX σ τ hσ hτ a0 hmark)
  simp only [Category.assoc, etaleStageOpenLimitSection_comp] at h
  simpa only [← Category.assoc,
    geometricPointToStrictHenselization_comp_smallEtaleNeighborhoodCone_π] using h

end AlgebraicGeometry.Scheme.SmoothSite
