/-
Copyright (c) 2026 Colib contributors and Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.Algebra.Homology.RightDerivedEdgePostcompose
import all StacksFrontier.Algebra.Homology.RightDerivedEdgePostcompose

/-!
# Exact postcomposition of the edge between distinct abelian categories

Adapted from `Stacks@c496df0d9beea9deaeabcea8492605f9a0a2313b`,
`StacksFrontier/Algebra/Homology/RightDerivedEdgePostcompose.lean`, using the
same resolution computation and the original composition lemma.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.RightDerivedEdge

variable {A : Type*} {B : Type*} {D : Type*} {E : Type*}
  [Category* A] [Category* B] [Category* D] [Category* E]
  [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (P : A ⥤ B) [P.Additive] [P.PreservesInjectiveObjects]
  (Γ : B ⥤ D) [Γ.Additive] (U : D ⥤ E) [U.Additive] [U.PreservesHomology]

/-- Evaluating an edge through exact postcomposition gives the edge for the composed functor. -/
theorem map_edge_comp_exactPostcomposition (n : ℕ) (M : A) :
    U.map ((edge P Γ n).app M) ≫
        (ModuleComparison.rightDerivedCompIso (P ⋙ Γ) U ((P ⋙ Γ) ⋙ U)
          (Iso.refl _) n).hom.app M =
      (ModuleComparison.rightDerivedCompIso Γ U (Γ ⋙ U)
          (Iso.refl _) n).hom.app (P.obj M) ≫ (edge P (Γ ⋙ U) n).app M := by
  rw [DerivedCompTransport.rightDerivedCompIso_hom_app,
    DerivedCompTransport.rightDerivedCompIso_hom_app]
  have hnat := (ModuleComparison.mapComplexHomologyIso Γ U (Γ ⋙ U)
    (Iso.refl _) n).hom.naturality (resolutionComparison P M)
  dsimp only [edge]
  exact postcomp_aux U (Iso.inv_hom_id _) (Iso.inv_hom_id _) hnat

end Stacks.Cohomology.RightDerivedEdge
