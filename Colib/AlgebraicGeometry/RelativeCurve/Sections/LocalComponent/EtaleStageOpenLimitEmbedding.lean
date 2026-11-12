/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitProjective
public import StacksFrontier.AlgebraicGeometry.ClosedSubschemeProjectiveSpace.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison

/-! # An actual polynomial projective embedding of the component limit

The original projectivity gives the same closed embedding after the native
coordinate-preserving projective-space comparison, as needed by the auxiliary
section construction over the original etale local ring.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open Stacks.ProjectiveCohomology
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Produce the actual closed embedding required by the same-root auxiliary supplier. -/
theorem etaleStageOpenLimit_exists_projective_embedding
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left) [IsClosedImmersion U.ι]
    (hp : IsProjectiveMorphism p) :
    ∃ (m : ℕ) (embedding : (etaleStageOpenCone X s p i U B hX).pt ⟶
      Proj (polyGrading ↥(etaleLocalRing B X.left hX s) m)), IsClosedImmersion embedding := by
  obtain ⟨m, j, hj, _hcomp⟩ :=
    etaleStageOpenLimitStructure_isProjective X s p i U B hX hp
  have := hj
  exact ⟨m, j ≫ (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso
    ↥(etaleLocalRing B X.left hX s) m).hom, inferInstance⟩

end AlgebraicGeometry.Scheme.SmoothSite
