/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.ModelUnitRowCellIteration

/-!
# Strict row cells constructed from a specified returned action

The transformation is defined by the actual return isomorphism and returned action.
Its equality with the original unit is proved afterwards. The resulting independently
realized cell enters the unchanged cone/loop iteration, with its index and time laws
proved from the original unit preservation. Raw coefficient provenance of the supplied
return isomorphism remains an application obligation.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.ModelUnitRowStrictification
open ModelDiagramRowInterchange NaturalTrack
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (c : 𝟭 C ⟶ L)
  (F : C ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)).obj.Obj ≅ 𝟭 (F.obj (L.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    (∀ A, (F.map (L.map g)).hom.toFunctor.map ((unit X).hom.app A) =
      (unit Y).hom.app ((F.map (L.map g)).hom.toFunctor.obj A)))
  (R : ∀ X, F.obj X ⟶ F.obj (L.obj X))
  (e : ∀ X, (F.map (c.app X)).hom.toFunctor ≅ (R X).hom.toFunctor)
  (μ : ∀ X, (R X).hom.toFunctor ⟶ (R X).hom.toFunctor)
  (he : ∀ X, (onFunctor (F.map (c.app X)).hom.toFunctor (unit X)).hom ≫ (e X).hom =
    (e X).hom ≫ μ X)

/-- Conjugate the specified actual returned action before identifying it with the original unit. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:41"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def transformation (X : C) : (F.map (c.app X)).hom.toFunctor ⟶ (F.map (c.app X)).hom.toFunctor :=
  ((e X).hom ≫ μ X) ≫ (e X).inv

include he in
/-- The proved original intertwining identifies this independently constructed transformation. -/
@[colib_tag "COL-0531", colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:46"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem transformation_eq (X : C) :
    transformation L c F R e μ X =
      (onFunctor (F.map (c.app X)).hom.toFunctor (unit X)).hom := by
  unfold transformation
  rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

include he in
/-- The actual conjugated action is weak at every original object. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:54"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem transformation_weak (X : C) (A : (F.obj X).obj.Obj) :
    (F.obj (L.obj X)).obj.waldhausen.weq ((transformation L c F R e μ X).app A) := by
  rw [transformation_eq L c F unit R e μ he X]
  exact (F.obj (L.obj X)).obj.waldhausen.weq_iso _ inferInstance

/-- Realize the actual conjugated transformation as the independent whole first-row cell. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:60"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def cell (X : C) :=
  rowTransformationSpectrumHomotopy (F := F.map (c.app X)) (G := F.map (c.app X))
    (transformation L c F R e μ X) (transformation_weak L c F unit R e μ he X)

/-- The entire realized cell agrees only after the actual intertwining has been used. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:65"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem cell_eq (X : C) :
    cell L c F unit R e μ he X = initialCell L c F unit X := by
  unfold cell
  simp only [transformation_eq L c F unit R e μ he X]
  rfl

/-- The independently realized cell has its proved strict index and whole-track laws. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:72"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def family :
    DiagramRowCell.Family L c (F ⋙ prespectrumFunctor)
      (initial F) (initial_point F) (initial_naturality F) (initial_structure F)
      (ofModelUnits L c F unit hunit) := by
  refine ⟨cell L c F unit R e μ he, ?_⟩
  have hc : cell L c F unit R e μ he = (initialCellFamily L c F unit hunit).val := by
    funext X
    exact cell_eq L c F unit R e μ he X
  exact hc.symm ▸ (initialCellFamily L c F unit hunit).property

/-- Equality of families is a proved consequence, not the definition of the returned family. -/
@[colib_tag "COL-0531", colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:83"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem family_eq :
    family L c F unit hunit R e μ he = initialCellFamily L c F unit hunit := by
  apply Subtype.ext
  funext X
  exact cell_eq L c F unit R e μ he X

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- Apply the unchanged raw cone, loop and row-strength recursion to the returned family. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:95"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def iteratedFamily (i : ℕ) :=
  DiagramRowCell.iterateFamily L c Q χ hχ i (F ⋙ prespectrumFunctor)
    (initial F) (initial_point F) (initial_naturality F) (initial_structure F)
    (ofModelUnits L c F unit hunit) (family L c F unit hunit R e μ he)

/-- The full recursive family agrees after construction at every independent Bass stage. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:101"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem iteratedFamily_eq (i : ℕ) :
    iteratedFamily L c F unit hunit R e μ he Q χ hχ i =
      ModelDiagramRowInterchange.iteratedCellFamily L c F unit hunit Q χ hχ i := by
  unfold iteratedFamily ModelDiagramRowInterchange.iteratedCellFamily
  rw [family_eq]

/-- Every original time slice and spectrum coordinate is preserved by the all-stage comparison. -/
@[colib_tag "COL-0531", colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelUnitRowCellStrictification.lean:108"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem iteratedCell_eq (i : ℕ) (X : C) :
    (iteratedFamily L c F unit hunit R e μ he Q χ hχ i).val X =
      ModelDiagramRowInterchange.iteratedCell L c F unit hunit Q χ hχ i X := by
  rw [iteratedFamily_eq]
  rfl

end KTheory.Bass.ModelUnitRowStrictification

