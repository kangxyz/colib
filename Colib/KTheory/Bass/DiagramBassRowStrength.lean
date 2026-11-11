/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramConeRowStrength
public import Colib.KTheory.Bass.DiagramRowLooping
public import Colib.Topology.Prespectrum.RowRefinementParameterLooping

/-!
# Forward row strength for the actual first Bass step

Parameter-loop the original cone-row strength, then move the old loop inside the actual
row refinement by the explicit coordinate isomorphism. This gives a whole natural map from
Bass of the row diagram to the row diagram of Bass. Its target interchange is the computed
original Bass interchange. The construction does not assert that the strength is stable.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramBassRowStrength
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))

/-- The actual Bass source applies the unchanged Bass functor to the refined corners. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramBassRowStrength.lean:34-37"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
abbrev source : C ⥤ LoopPrespectrum.{w} :=
  (strictDiagramFunctor Q).obj (DiagramRowRefinement.diagram F q hp hn)

/-- The target uses the genuine cone-and-old-loop interchange computed from the original data. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramBassRowStrength.lean:38-43"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
abbrev target : C ⥤ LoopPrespectrum.{w} :=
  DiagramRowRefinement.diagram ((strictDiagramFunctor Q).obj F)
    (DiagramRowInterchange.bass Q F q hp hn) (DiagramRowInterchange.bass_point Q F q hp hn)
    (DiagramRowInterchange.bass_naturality Q F q hp hn)

/-- Loop the forward cone strength and retain the explicit old-loop/row-coordinate comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramBassRowStrength.lean:44-49"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def strength (X : C) : (source Q F q hp hn).obj X ⟶ (target Q F q hp hn).obj X :=
  parameterLoopingMap (DiagramConeRowStrength.strength Q F q hp hn X) ≫
    RowRefinement.parameterLoopingInverse ((ConeTrack.diagram Q F).obj X)
      (DiagramRowInterchange.cone Q F q hp hn X) (DiagramRowInterchange.cone_point Q F q hp hn X)

/-- Positive levels keep the independent row and old-loop coordinates in their actual order. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramBassRowStrength.lean:50-58"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_succ (X : C) (k : ℕ)
    (γ : Path ((DiagramConeRowStrength.source Q F q hp hn X).point (k + 1))
      ((DiagramConeRowStrength.source Q F q hp hn X).point (k + 1))) (s t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((strength Q F q hp hn X).map (k + 1) γ) s) t =
      Path.toContinuousMap ((DiagramConeRowStrength.strength Q F q hp hn X).map (k + 1)
        (γ t)) s := rfl

/-- Degree zero keeps both row parameters, independently of the original old-loop time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramBassRowStrength.lean:59-67"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_zero (X : C)
    (γ : Path ((DiagramConeRowStrength.source Q F q hp hn X).point 0)
      ((DiagramConeRowStrength.source Q F q hp hn X).point 0)) (r s t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((strength Q F q hp hn X).map 0 γ) r) s) t =
      Path.toContinuousMap (Path.toContinuousMap
        ((DiagramConeRowStrength.strength Q F q hp hn X).map 0 (γ t)) r) s := rfl

/-- Every original coefficient arrow preserves all old-loop and row coordinates. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramBassRowStrength.lean:68-84"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_naturality {X Y : C} (g : X ⟶ Y) :
    (source Q F q hp hn).map g ≫ strength Q F q hp hn Y =
      strength Q F q hp hn X ≫ (target Q F q hp hn).map g := by
  apply Hom.ext; funext n; apply ContinuousMap.ext; intro γ
  change Path (((ConeTrack.diagram Q (DiagramRowRefinement.diagram F q hp hn)).obj X).point n)
    (((ConeTrack.diagram Q (DiagramRowRefinement.diagram F q hp hn)).obj X).point n) at γ
  cases n with
  | zero =>
    apply Path.ext; funext r; apply Path.ext; funext s; apply Path.ext; funext t
    exact congrArg (fun a => Path.toContinuousMap (Path.toContinuousMap (a.map 0 (γ t)) r) s)
      (DiagramConeRowStrength.strength_naturality Q F q hp hn g)
  | succ k =>
    apply Path.ext; funext s; apply Path.ext; funext t
    exact congrArg (fun a => Path.toContinuousMap (a.map (k + 1) (γ t)) s)
      (DiagramConeRowStrength.strength_naturality Q F q hp hn g)

/-- The genuine first-Bass row strength is a natural transformation of whole diagrams. -/
@[colib_tag "COL-0521", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramBassRowStrength.lean:85-90"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def strengthNatTrans : source Q F q hp hn ⟶ target Q F q hp hn where
  app := strength Q F q hp hn
  naturality _ _ := strength_naturality Q F q hp hn

/-- The original Bass image of the structure comparison agrees as an entire map with its row.
-/
@[colib_tag "COL-0521", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramBassRowStrength.lean:91-114"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_comparison
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (X : C) :
    (((strictDiagramFunctor Q).map (DiagramRowRefinement.comparison F q hp hn hs)).app X) ≫
        strength Q F q hp hn X =
      (DiagramRowRefinement.comparison ((strictDiagramFunctor Q).obj F)
        (DiagramRowInterchange.bass Q F q hp hn) (DiagramRowInterchange.bass_point Q F q hp hn)
        (DiagramRowInterchange.bass_naturality Q F q hp hn)
        (DiagramRowInterchange.bass_structure Q F q hp hn hs)).app X := by
  apply Hom.ext; funext n; apply ContinuousMap.ext; intro γ
  change Path (((ConeTrack.diagram Q F).obj X).point n)
    (((ConeTrack.diagram Q F).obj X).point n) at γ
  cases n with
  | zero =>
    apply Path.ext; funext r; apply Path.ext; funext s; apply Path.ext; funext t
    exact congrArg (fun a => Path.toContinuousMap (Path.toContinuousMap (a.map 0 (γ t)) r) s)
      (DiagramConeRowStrength.strength_comparison Q F q hp hn hs X)
  | succ k =>
    apply Path.ext; funext s; apply Path.ext; funext t
    exact congrArg (fun a => Path.toContinuousMap (a.map (k + 1) (γ t)) s)
      (DiagramConeRowStrength.strength_comparison Q F q hp hn hs X)

end KTheory.Bass.DiagramBassRowStrength
