/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.StrictDiagramCofiberDescent
public import Colib.KTheory.Bass.DiagramConeInclusion

/-! # Positive cofiber comparison on the original inclusion and whole cylinder

These six original declarations identify the actual comparison with prescribed cone descent.
Independent cylinder time is preserved. No inverse or stable equivalence is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.PushoutCofiberSquare
variable {C : Type u} [Category.{v} C]
  {F₀ F₁ : C ⥤ LoopPrespectrum.{w}} (f : F₀ ⟶ F₁)
/-- The original entire cone null track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutCofiberSquare.lean:39"
  "adaptation" "Original whole-null descent and positive cofiber comparison."]
def coneNull (X : C) :
    Homotopy ((f ≫ coneInclusion f).app X)
      ((diagramZeroMap F₀ (mappingConeDiagram f)).app X) :=
  mappingConeHomotopy (f.app X)

/-- Original cone maps retain the independent null coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutCofiberSquare.lean:45"
  "adaptation" "Original whole-null descent and positive cofiber comparison."]
theorem coneNull_naturality {X Y : C} (k : X ⟶ Y) n r x :
    ((mappingConeDiagram f).map k).map n ((coneNull f X).level n (r, x)) =
      (coneNull f Y).level n (r, (F₀.map k).map n x) := rfl

/-- Descent of the original inclusion and original null is the identity. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutCofiberSquare.lean:50"
  "adaptation" "Original whole-null descent and positive cofiber comparison."]
theorem coneDesc_self :
    mappingConeDescTransformation f (coneInclusion f) (coneNull f)
      (coneNull_naturality f) = 𝟙 (mappingConeDiagram f) := by
  apply NatTrans.ext
  funext X
  apply mappingCone_hom_ext
  · apply Hom.ext; funext n; ext x; rfl
  · intro n r x
    rfl


variable (Q : C ⥤ Arrow (Arrow C))

/-- The positive cofiber comparison is the original descent of the Bass cone null. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutCofiberSquare.lean:106"
  "adaptation" "Original whole-null descent and positive cofiber comparison."]
theorem cofiberComparison_desc (X : C) :
    (strictDiagramCofiberComparison Q f).app X =
      mappingConeDesc (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map (coneInclusion f)).app X)
        (strictDiagramNullHomotopy f (coneInclusion f) (coneNull f)
          (coneNull_naturality f) Q X) := by
  have h := strictDiagramCofiberComparison_desc Q f (coneInclusion f)
    (coneNull f) (coneNull_naturality f) X
  rw [coneDesc_self, CategoryTheory.Functor.map_id] at h
  simpa only [NatTrans.id_app, Category.comp_id] using h

/-- The cofiber comparison retains the original inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutCofiberSquare.lean:119"
  "adaptation" "Original whole-null descent and positive cofiber comparison.", reassoc]
theorem cofiberComparison_inclusion (X : C) :
    mappingConeInclusion (((strictDiagramFunctor Q).map f).app X) ≫
      (strictDiagramCofiberComparison Q f).app X =
        (((strictDiagramFunctor Q).map (coneInclusion f)).app X) := by
  rw [cofiberComparison_desc]
  exact mappingConeInclusion_desc _ _ _

/-- The cofiber comparison's cylinder is the Bass image of the same original time slice. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/PushoutCofiberSquare.lean:127"
  "adaptation" "Original whole-null descent and positive cofiber comparison."]
theorem cofiberComparison_cylinder (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F₀).obj X).space n) :
    ((strictDiagramCofiberComparison Q f).app X).map n
      ((mappingConeHomotopy (((strictDiagramFunctor Q).map f).app X)).level n (r, x)) =
        (((strictDiagramFunctor Q).map
          (diagramHomotopyAt (coneNull f) (coneNull_naturality f) r)).app X).map n x := by
  rw [cofiberComparison_desc]
  change ((strictDiagramMapHomotopy (coneNull f) (coneNull_naturality f) Q X).at r).map n x = _
  rw [strictDiagramMapHomotopy_at]

end KTheory.Bass.PushoutCofiberSquare
