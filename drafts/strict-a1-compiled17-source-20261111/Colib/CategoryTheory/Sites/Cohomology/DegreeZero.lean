/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

/-!
# Invertibility of ordinary degree-zero restriction

Uses the existing Stacks section equivalence with an independent Ext universe.
Adapted from `Motivic/Cohomology/A1/StrictInvariance/DegreeZero.lean:33-47`
at motivic@a6805c4a87cdfd7717dd7a94039246a167f15380.
-/
@[expose] public noncomputable section
open CategoryTheory Opposite
universe w t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Ordinary degree-zero restriction is invertible exactly when section restriction is. -/
theorem zero_isIso_restriction_iff (F : Sheaf J AddCommGrpCat.{max v t})
    {X Y : C} (f : X ⟶ Y) :
    IsIso ((cohomologyPresheaf.{w, t} F 0).map f.op) ↔ IsIso (F.obj.map f.op) := by
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  have h : ⇑((cohomologyPresheaf.{w, t} F 0).map f.op) =
      (extSectionsAddEquiv X F).symm ∘ F.obj.map f.op ∘ extSectionsAddEquiv Y F := by
    funext x
    apply (extSectionsAddEquiv X F).injective
    exact (extSectionsAddEquiv_naturality_left f F x).trans
      ((extSectionsAddEquiv X F).apply_symm_apply _).symm
  rw [h]
  exact (Equiv.comp_bijective _ (extSectionsAddEquiv X F).symm.toEquiv).trans
    ((extSectionsAddEquiv Y F).toEquiv.bijective_comp _)

end Stacks.Cohomology.FreeYonedaUnivLE

