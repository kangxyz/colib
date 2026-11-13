/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Large/RestrictionSource.lean`,
blob `eaa5eeb7994561c0bef22b8398a55df532b52c21`.

 The actual free abelian representing source under a continuous-site adjunction.
No exactness of restriction or of its left adjoint is assumed here. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u u'

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasSheafify K AddCommGrpCat.{max v t}]
  (G : C ⥤ D) [G.IsContinuous J K]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max v t} J K).IsRightAdjoint]

/-- Evaluation at `X` after literal restriction is represented by the left adjoint
applied to the original free abelian source at `X`. -/
def restrictedSectionsCorepresentable (X : C) :
    (sheafToPresheaf K AddCommGrpCat.{max v t} ⋙
      (CategoryTheory.evaluation Dᵒᵖ AddCommGrpCat).obj (op (G.obj X)) ⋙
      forget AddCommGrpCat).CorepresentableBy
        ((G.sheafPullback AddCommGrpCat J K).obj (((freeYoneda.{t} J).obj X))) where
  homEquiv := ((G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _).trans
    (sectionsEquiv.{t} X _)
  homEquiv_comp g f := by
    change sectionsEquiv.{t} X _
      (((G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _) (f ≫ g)) = _
    rw [Adjunction.homEquiv_naturality_right, sectionsEquiv_naturality]
    rfl

/-- The original representing sheaf at `G(X)`, not a replacement cohomology source. -/
def sectionsCorepresentable (Y : D) :
    (sheafToPresheaf K AddCommGrpCat.{max v t} ⋙
      (CategoryTheory.evaluation Dᵒᵖ AddCommGrpCat).obj (op Y) ⋙
      forget AddCommGrpCat).CorepresentableBy
        (((freeYoneda.{t} K).obj Y)) where
  homEquiv := sectionsEquiv.{t} Y _
  homEquiv_comp g f := sectionsEquiv_naturality Y f g

/-- A continuous-site left adjoint carries the actual free abelian representable
source to the actual source at the image object. This is independent of exactness. -/
def restrictionSourceIso (X : C) :
    (G.sheafPullback AddCommGrpCat.{max v t} J K).obj (((freeYoneda.{t} J).obj X)) ≅
      ((freeYoneda.{t} K).obj (G.obj X)) :=
  (restrictedSectionsCorepresentable J K G X).uniqueUpToIso (sectionsCorepresentable K (G.obj X))

end Stacks.Cohomology.FreeYonedaUnivLE
