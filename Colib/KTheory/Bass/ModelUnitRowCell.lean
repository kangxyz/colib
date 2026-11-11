/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.ModelDiagramRowInterchange
public import Colib.Topology.Prespectrum.RowRefinement
public import Colib.KTheory.Bass.NaturalModelUnitTrack
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationSpectrum

/-! # The independent first-row cell for an actual Model identity unit

The two-cylinder realization supplies the finite cell before its comparison with the original
unit track. Positive levels and degree zero retain every independent interval coordinate.
A geometric tensor qualification is a separate actual row comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.ModelDiagramRowInterchange
open NaturalTrack
variable {C : Type u} [Category.{v} C] (L : C ⥤ C) (c : 𝟭 C ⟶ L)
  (F : C ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (F.obj (L.obj X)).obj.Obj ≅ 𝟭 (F.obj (L.obj X)).obj.Obj)

/-- The actual first-row spectrum homotopy of the original forward unit. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCell.lean:34"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def initialCell (X : C) :
    Homotopy
      (prespectrumMap (F.map (c.app X)) ≫
        Topology.LoopPrespectrum.RowRefinement.comparison (prespectrum (F.obj (L.obj X)))
          (initial F (L.obj X)) (initial_point F (L.obj X)) (initial_structure F (L.obj X)))
      (prespectrumMap (F.map (c.app X)) ≫
        Topology.LoopPrespectrum.RowRefinement.comparison (prespectrum (F.obj (L.obj X)))
          (initial F (L.obj X)) (initial_point F (L.obj X)) (initial_structure F (L.obj X))) :=
  rowTransformationSpectrumHomotopy
    (onFunctor (F.map (c.app X)).hom.toFunctor (unit X)).hom
    (fun _ => (F.obj (L.obj X)).obj.waldhausen.weq_iso _ inferInstance)

/-- The two positive-level cell coordinates keep their original order. -/
@[colib_tag "COL-0531", colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCell.lean:47"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem initialCell_succ (X : C) (k : ℕ) (t s : unitInterval)
    (x : stageSpace k (F.obj X)) :
    Path.toContinuousMap ((initialCell L c F unit X).level (k + 1) (t, x)) s =
      rowTransformationRealization (onFunctor (F.map (c.app X)).hom.toFunctor (unit X)).hom
        (fun _ => (F.obj (L.obj X)).obj.waldhausen.weq_iso _ inferInstance) k (s, (t, x)) :=
  rowTransformationSpectrumHomotopy_succ _ _ k t s x

/-- Degree zero preserves the additional original input-loop coordinate. -/
@[colib_tag "COL-0531", colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCell.lean:55"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem initialCell_zero (X : C) (t a s : unitInterval)
    (γ : Path (stagePoint 0 (F.obj X)) (stagePoint 0 (F.obj X))) :
    Path.toContinuousMap
      (Path.toContinuousMap ((initialCell L c F unit X).level 0 (t, γ)) a) s =
      rowTransformationRealization (onFunctor (F.map (c.app X)).hom.toFunctor (unit X)).hom
        (fun _ => (F.obj (L.obj X)).obj.waldhausen.weq_iso _ inferInstance) 0 (s, (t, γ a)) :=
  rowTransformationSpectrumHomotopy_zero _ _ t a s γ

/-- The whole cell is the original unit track after the genuine row comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelUnitRowCell.lean:64"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem initialCell_eq
    (hunit : ∀ {X Y} (g : X ⟶ Y),
      (∀ A, (F.map (L.map g)).hom.toFunctor.map ((unit X).hom.app A) =
      (unit Y).hom.app ((F.map (L.map g)).hom.toFunctor.obj A))) (X : C) :
    initialCell L c F unit X =
      ((ofModelUnits L c F unit hunit).homotopy X).postcomp
        (Topology.LoopPrespectrum.RowRefinement.comparison (prespectrum (F.obj (L.obj X)))
          (initial F (L.obj X)) (initial_point F (L.obj X)) (initial_structure F (L.obj X))) := rfl

end KTheory.Bass.ModelDiagramRowInterchange

