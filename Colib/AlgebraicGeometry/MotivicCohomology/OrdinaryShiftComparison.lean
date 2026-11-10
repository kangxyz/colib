/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Hypercohomology
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# The canonical motivic complex as signed ordinary singular chains

Adapted from SuslinVoevodsky/OrdinaryShiftComparison.lean at motivic revision
a6805c4a87cdfd7717dd7a94039246a167f15380. The already accepted canonical
complex is preserved. Native Stacks extension comparison and Mathlib shift
comparison commute the actual functors; the existing literal-product ordinary
singular comparison is reused without a second complex or product adapter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSimplex

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- Forgetting transfers and extension commute with the defining signed shift. -/
def motivicSheafComplexOrdinaryShiftIso (q : ℕ) :
    motivicSheafComplex k q ≅
      (((sheafifiedSingularChainsFunctor k (SmoothSite.nisnevichTopology (Spec (.of k)))).obj
        ((toPresheaf k).obj (reducedTorus k q))).extend
          (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧ := by
  let F := SheafWithTransfers.toSheaf k
  let G := nisnevichSheafify k
  let e := ComplexShape.embeddingUpIntLE 0
  let K := singularComplex (reducedTorus k q)
  exact (F.mapCochainComplexShiftIso (-(q : ℤ))).app
      ((G.mapHomologicalComplex (.up ℤ)).obj (K.extend e)) ≪≫
    (shiftFunctor _ (-(q : ℤ))).mapIso
      ((Stacks.DerivedIndexing.mapExtendIso (G ⋙ F) e K).symm ≪≫
        (e.extendFunctor _).mapIso (singularSheafOrdinaryIso k (reducedTorus k q)))

end AlgebraicGeometry.PresheafWithTransfers
