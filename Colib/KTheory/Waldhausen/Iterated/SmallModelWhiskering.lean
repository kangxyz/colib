/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Category

/-!
# Explicit underlying functors of strict small-model arrows

These projection formulas allow geometric clients to expose composition without
unfolding the concrete Waldhausen categories or their chosen-zero structures.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
universe u v u₁ v₁
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

/-- Strict model composition retains the actual composite functor. -/
theorem smallModel_comp_toFunctor {V W T : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (G : W ⟶ T) :
    (F ≫ G).hom.toFunctor = F.hom.toFunctor ⋙ G.hom.toFunctor := rfl

/-- Strict model identity retains the actual identity functor. -/
theorem smallModel_id_toFunctor (V : WideSubcategory preservesZero.{u}) :
    (𝟙 V : V ⟶ V).hom.toFunctor = 𝟭 V.obj.Obj := rfl

/-- Lift a mixed-universe evaluation square into actual AsSmall target functors.

The only cancellation is the actual `AsSmall.up` followed by `AsSmall.down`.
The original comparison is not normalized a second time.
-/
def asSmallEvaluationWhiskerIso
    {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    {E F : Type u} [Category.{v} E] [Category.{v} F]
    (r : C ⥤ D) (eS : D ⥤ E) (eR : C ⥤ F) (p : F ⥤ E)
    (i : r ⋙ eS ≅ eR ⋙ p) :
    r ⋙ (eS ⋙ AsSmall.up) ≅ (eR ⋙ AsSmall.up) ⋙ asSmallFunctor p :=
  isoWhiskerRight i AsSmall.up

end CategoryTheory.Waldhausen.IteratedS
