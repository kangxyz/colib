/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitSections
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleRetainedGeometry

/-! # Proper and projective geometry of the actual component limit

The chosen closed stage open is pulled back as a closed subscheme of the original
proper or projective strict-local curve. No projectivity certificate is added for
the new cone vertex.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  (B : BigEtaleSite.{u}) (hX : B.Contains X.left) [IsClosedImmersion U.ι]

/-- The actual component-model structure is proper over the original strict-local base. -/
instance etaleStageOpenLimitStructure_isProper [IsProper p] :
    IsProper (etaleStageOpenLimitStructure X s p i U B hX) := by
  change IsProper (pullback.fst ((etaleCurveCone X B hX s p).π.app i) U.ι ≫
    pullback.fst (strictHenselizationToBase B X.left hX s) p)
  infer_instance

/-- The same projective embedding restricts along the actual closed component model. -/
theorem etaleStageOpenLimitStructure_isProjective (hp : IsProjectiveMorphism p) :
    IsProjectiveMorphism (etaleStageOpenLimitStructure X s p i U B hX) := by
  obtain ⟨n, j, hj, hcomp⟩ :=
    isProjectiveMorphism_pullback_fst p (strictHenselizationToBase B X.left hX s) hp
  have := hj
  refine ⟨n, pullback.fst ((etaleCurveCone X B hX s p).π.app i) U.ι ≫ j,
    inferInstance, ?_⟩
  rw [Category.assoc]
  exact congrArg (fun g =>
    pullback.fst ((etaleCurveCone X B hX s p).π.app i) U.ι ≫ g) hcomp

end AlgebraicGeometry.Scheme.SmoothSite
