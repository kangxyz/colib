/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryDiagram
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitSections
public import Colib.AlgebraicGeometry.Scheme.FiniteAffinePresentation

/-! # Actual finite boundaries on component stages and their limit

Finiteness is transported from the same complete finite-stage boundary through
literal Cartesian squares. No nonemptiness is inferred from finiteness.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
  [IsFinite (d ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]

/-- The original full finite boundary stays finite on every actual component stage. -/
instance etaleStageOpenBoundary_stage_isFinite (a : Over i) :
    IsFinite ((etaleStageOpenBoundaryMap X s p i U d).app a ≫
      (etaleStageOpenStructure X s p i U).app a) := by
  exact MorphismProperty.of_isPullback (P := @IsFinite)
    ((etaleStageOpenBoundaryMap_isPullback X s p i U d a).flip.paste_vert
      (etaleStageOpenStructure_isPullback X s p i U a)) inferInstance

variable (B : BigEtaleSite.{u}) (hX : B.Contains X.left)

/-- The boundary at the actual component-model limit remains the full finite boundary. -/
instance etaleStageOpenBoundary_limit_isFinite :
    IsFinite (etaleStageOpenBoundaryLimitMap X s p i U d B hX ≫
      etaleStageOpenLimitStructure X s p i U B hX) := by
  exact MorphismProperty.of_isPullback (P := @IsFinite)
    ((etaleStageOpenBoundaryLimitMap_isPullback X s p i U d B hX).flip.paste_vert
      (etaleStageOpenLimitStructure_isPullback X s p i U B hX)) inferInstance

/-- The actual full boundary on the component-model limit has a finite algebra
presentation over the original strict-local ring, preserving the structure map. -/
theorem etaleStageOpenBoundary_limit_finiteAlgebra :
    ∃ (C : CommRingCat.{u}) (f : (etaleLocalRing B X.left hX s) →+* C)
      (e : (etaleStageOpenBoundaryCone X s p i U d B hX).pt ≅ Spec C),
      letI := f.toAlgebra
      Module.Finite (etaleLocalRing B X.left hX s) C ∧
        e.inv ≫ etaleStageOpenBoundaryLimitMap X s p i U d B hX ≫
          etaleStageOpenLimitStructure X s p i U B hX = Spec.map (CommRingCat.ofHom f) := by
  let := etaleStageOpenBoundary_limit_isFinite X s p i U d B hX
  exact Scheme.exists_finiteAlgebra_presentation (etaleLocalRing B X.left hX s)
    (etaleStageOpenBoundaryLimitMap X s p i U d B hX ≫
      etaleStageOpenLimitStructure X s p i U B hX)

end AlgebraicGeometry.Scheme.SmoothSite
