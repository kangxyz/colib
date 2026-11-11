/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.KTheory.Bass.ModelUnitRowCell
import Colib.KTheory.Bass.ModelUnitRowCellNaturality
import Colib.KTheory.Bass.ModelUnitRowCellStrictification
import Colib.KTheory.Bass.ModelUnitRowCellIteration

/-! # Reconstructed original proof consumers
These checks retain the original hypotheses and coordinate equations.
-/
noncomputable section
open KTheory.Bass
section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v w
open KTheory.Bass.ModelDiagramRowInterchange
namespace ReconstructedConsumer0531N0
open NaturalTrack
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (c : 𝟭 C ⟶ L)
  (F : C ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)).obj.Obj ≅ 𝟭 (F.obj (L.obj X)).obj.Obj)

/-- The two positive-level cell coordinates keep their original order. -/
example (X : C) (k : ℕ) (t s : unitInterval)
    (x : stageSpace k (F.obj X)) :
    Path.toContinuousMap ((initialCell L c F unit X).level (k + 1) (t, x)) s =
      rowTransformationRealization (onFunctor (F.map (c.app X)).hom.toFunctor (unit X)).hom
        (fun _ => (F.obj (L.obj X)).obj.waldhausen.weq_iso _ inferInstance) k (s, (t, x)) :=
  rowTransformationSpectrumHomotopy_succ _ _ k t s x

/-- Degree zero preserves the additional original input-loop coordinate. -/
example (X : C) (t a s : unitInterval)
    (γ : Path (stagePoint 0 (F.obj X)) (stagePoint 0 (F.obj X))) :
    Path.toContinuousMap
      (Path.toContinuousMap ((initialCell L c F unit X).level 0 (t, γ)) a) s =
      rowTransformationRealization (onFunctor (F.map (c.app X)).hom.toFunctor (unit X)).hom
        (fun _ => (F.obj (L.obj X)).obj.waldhausen.weq_iso _ inferInstance) 0 (s, (t, γ a)) :=
  rowTransformationSpectrumHomotopy_zero _ _ t a s γ

/-- The whole cell is the original unit track after the genuine row comparison. -/
example
    (hunit : ∀ {X Y} (g : X ⟶ Y),
      (∀ A, (F.map (L.map g)).hom.toFunctor.map ((unit X).hom.app A) =
      (unit Y).hom.app ((F.map (L.map g)).hom.toFunctor.obj A))) (X : C) :
    initialCell L c F unit X =
      ((ofModelUnits L c F unit hunit).homotopy X).postcomp
        (Topology.LoopPrespectrum.RowRefinement.comparison (prespectrum (F.obj (L.obj X)))
          (initial F (L.obj X)) (initial_point F (L.obj X)) (initial_structure F (L.obj X))) := rfl

end ReconstructedConsumer0531N0


end

section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v w
open KTheory.Bass.ModelDiagramRowInterchange
namespace ReconstructedConsumer0531N1
open NaturalTrack
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (c : 𝟭 C ⟶ L)
  (F : C ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)).obj.Obj ≅ 𝟭 (F.obj (L.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    (∀ A, (F.map (L.map g)).hom.toFunctor.map ((unit X).hom.app A) =
      (unit Y).hom.app ((F.map (L.map g)).hom.toFunctor.obj A)))

include hunit in
/-- Genuine exact row transport preserves every original cell level and transformation time. -/
example {X Y : C} (g : X ⟶ Y) (n : ℕ) (t : unitInterval)
    (x : (prespectrum (F.obj X)).space n) :
    (rowLoopMap (F.map (L.map g))).map n ((initialCell L c F unit X).level n (t, x)) =
      (initialCell L c F unit Y).level n (t, (prespectrumMap (F.map g)).map n x) := by
  let A := ofModelUnits L c F unit hunit
  change (rowLoopMap (F.map (L.map g))).map n
      ((rowStabilizationMap (F.obj (L.obj X))).map n ((A.homotopy X).level n (t, x))) =
    (rowStabilizationMap (F.obj (L.obj Y))).map n
      ((A.homotopy Y).level n (t, (prespectrumMap (F.map g)).map n x))
  have hr := congrArg (fun f => f.map n ((A.homotopy X).level n (t, x)))
    (rowStabilizationMap_naturality (F.map (L.map g))).symm
  change (rowLoopMap (F.map (L.map g))).map n
      ((rowStabilizationMap (F.obj (L.obj X))).map n ((A.homotopy X).level n (t, x))) =
    (rowStabilizationMap (F.obj (L.obj Y))).map n
      ((prespectrumMap (F.map (L.map g))).map n ((A.homotopy X).level n (t, x))) at hr
  exact hr.trans (congrArg ((rowStabilizationMap (F.obj (L.obj Y))).map n)
    (A.naturality g n t x))

end ReconstructedConsumer0531N1


end

section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v w
open KTheory.Bass.ModelUnitRowStrictification
namespace ReconstructedConsumer0531N2
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

/-- The proved original intertwining identifies this independently constructed transformation. -/
example (X : C) :
    transformation L c F R e μ X =
      (onFunctor (F.map (c.app X)).hom.toFunctor (unit X)).hom := by
  unfold transformation
  rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

include he in
/-- The actual conjugated action is weak at every original object. -/
example (X : C) (A : (F.obj X).obj.Obj) :
    (F.obj (L.obj X)).obj.waldhausen.weq ((transformation L c F R e μ X).app A) := by
  rw [transformation_eq L c F unit R e μ he X]
  exact (F.obj (L.obj X)).obj.waldhausen.weq_iso _ inferInstance

/-- The entire realized cell agrees only after the actual intertwining has been used. -/
example (X : C) :
    cell L c F unit R e μ he X = initialCell L c F unit X := by
  unfold cell
  simp only [transformation_eq L c F unit R e μ he X]
  rfl

/-- Equality of families is a proved consequence, not the definition of the returned family. -/
example :
    family L c F unit hunit R e μ he = initialCellFamily L c F unit hunit := by
  apply Subtype.ext
  funext X
  exact cell_eq L c F unit R e μ he X

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- The full recursive family agrees after construction at every independent Bass stage. -/
example (i : ℕ) :
    iteratedFamily L c F unit hunit R e μ he Q χ hχ i =
      ModelDiagramRowInterchange.iteratedCellFamily L c F unit hunit Q χ hχ i := by
  unfold iteratedFamily ModelDiagramRowInterchange.iteratedCellFamily
  rw [family_eq]

/-- Every original time slice and spectrum coordinate is preserved by the all-stage comparison. -/
example (i : ℕ) (X : C) :
    (iteratedFamily L c F unit hunit R e μ he Q χ hχ i).val X =
      ModelDiagramRowInterchange.iteratedCell L c F unit hunit Q χ hχ i X := by
  rw [iteratedFamily_eq]
  rfl

end ReconstructedConsumer0531N2


end

section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v w
open KTheory.Bass.ModelDiagramRowInterchange
namespace ReconstructedConsumer0531N3
open NaturalTrack
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)).obj.Obj ≅ 𝟭 (F.obj (L.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    (∀ A, (F.map (L.map g)).hom.toFunctor.map ((unit X).hom.app A) =
      (unit Y).hom.app ((F.map (L.map g)).hom.toFunctor.obj A)))

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

/-- Every original time slice recovers the original current-stage action through its row map. -/
example (i : ℕ) (X : C) (t : unitInterval) :
    (iteratedCell L c F unit hunit Q χ hχ i X).at t =
      (((ofModelUnits L c F unit hunit).stages Q χ hχ i).homotopy X).at t ≫
        (DiagramRowRefinement.comparison ((strictDiagramIterate Q i).obj
          (F ⋙ prespectrumFunctor)) (stage Q F i) (stage_point Q F i)
          (stage_naturality Q F i) (stage_structure Q F i)).app (L.obj X) :=
  (iteratedCellFamily L c F unit hunit Q χ hχ i).property.2 X t

/-- The actual finite cell is natural at its unchanged unit time and every spectrum level. -/
example (i : ℕ) {X Y : C} (g : X ⟶ Y) (n : ℕ)
    (t : unitInterval)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space n) :
    ((DiagramRowRefinement.diagram ((strictDiagramIterate Q i).obj
      (F ⋙ prespectrumFunctor)) (stage Q F i) (stage_point Q F i)
      (stage_naturality Q F i)).map (L.map g)).map n
        ((iteratedCell L c F unit hunit Q χ hχ i X).level n (t, x)) =
      (iteratedCell L c F unit hunit Q χ hχ i Y).level n
        (t, (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).map g).map n x) :=
  (iteratedCellFamily L c F unit hunit Q χ hχ i).property.1 g n t x

end ReconstructedConsumer0531N3


end

