/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.StrictDiagramHomotopy
public import Colib.Topology.Prespectrum.StrictSquareSeedHomotopy

/-!
# Original cone tracks from coefficient-index interchange

The original coefficient-natural corner tracks descend through the existing reduced span
and cone. A specified natural index interchange and its coefficient factorization identify
the endpoint with the original cone coefficient map. All four moving edge squares come
from the given track's ordinary coefficient naturality, rather than being extra homotopy
hypotheses. The original source-null cylinder retains both independent times.

The index interchange and its coefficient-arrow factorization are explicit inputs. Concrete
scheme interchanges may supply them; no scalar two-time interchange or seed identity is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.ConeTrack
variable {C : Type u} [Category.{v} C]

/-- The unlooped cone of the original square diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrack.lean:32-36"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
def diagram (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) :
    C ⥤ LoopPrespectrum.{w} :=
  Q ⋙ F.mapArrow.mapArrow ⋙ strictSquareComparisonFunctor ⋙ mappingConeFunctor

/-- An original transformation acts on the actual unlooped cone diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrack.lean:37-51"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
def map (Q : C ⥤ Arrow (Arrow C)) {F G : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    diagram Q F ⟶ diagram Q G :=
  Functor.whiskerLeft Q (Functor.whiskerRight
    ((Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum.{w})).map
      ((Functor.mapArrowFunctor C LoopPrespectrum.{w}).map η))
    (strictSquareComparisonFunctor ⋙ mappingConeFunctor))

variable (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
    (F : C ⥤ LoopPrespectrum.{w})

/-- Use the inverse of the specified index interchange on the entire original cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrack.lean:52-57"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
def indexMap : diagram Q (L ⋙ F) ⟶ L ⋙ diagram Q F :=
  Functor.whiskerRight χ.inv
    (F.mapArrow.mapArrow ⋙ strictSquareComparisonFunctor ⋙ mappingConeFunctor)

include hχ in
/-- The original coefficient factorization gives precisely the original cone coefficient map. -/
@[colib_tag "COL-0516", colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrack.lean:58-81"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem coefficient (X : C) :
    (map Q (Functor.whiskerRight c F)).app X ≫ (indexMap Q L χ F).app X =
      (diagram Q F).map (c.app X) := by
  have hi :
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X) ≫ χ.inv.app X =
      Q.map (c.app X) := by
    have hc : (Q.map (c.app X) ≫ χ.hom.app X) ≫ χ.inv.app X =
        Q.map (c.app X) := by
      rw [Category.assoc]
      simp
    exact (congrArg (fun k => k ≫ χ.inv.app X) (hχ X).symm).trans hc
  have hm := congrArg
    (F.mapArrow.mapArrow ⋙ strictSquareComparisonFunctor ⋙ mappingConeFunctor).map hi
  rw [Functor.map_comp] at hm
  exact hm

variable
    (H : ∀ X, Homotopy (F.map (c.app X)) (F.map (c.app X)))
    (hH : ∀ {X Y} (g : X ⟶ Y) n r x,
      (F.map (L.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

/-- Descend the actual four moving corner tracks, then apply the fixed whole index map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrack.lean:82-89"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
def action (X : C) :
    Homotopy ((diagram Q F).map (c.app X)) ((diagram Q F).map (c.app X)) :=
  ((diagramSquareMapHomotopy
    (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH (Q.obj X)).cone.postcomp
      ((indexMap Q L χ F).app X)).cast
    (coefficient Q L c χ hχ F X) (coefficient Q L c χ hχ F X)

/-- Each time slice is the actual cone image of the original natural time slice. -/
@[colib_tag "COL-0516", colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrack.lean:90-104"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem action_at (X : C) (r : unitInterval) :
    (action Q L c χ hχ F H hH X).at r =
      ((map Q (diagramHomotopyAt
        (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH r)) ≫
        indexMap Q L χ F).app X := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun z => ((indexMap Q L χ F).app X).map n z)
    (congrArg (fun f => f.map n x)
      ((diagramSquareMapHomotopy
        (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH (Q.obj X)).cone_at r))

/-- Original coefficient maps commute with the derived track at the identical time. -/
@[colib_tag "COL-0516", colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrack.lean:105-119"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem action_naturality {X Y : C} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : ((diagram Q F).obj X).space n) :
    ((diagram Q F).map (L.map g)).map n
        ((action Q L c χ hχ F H hH X).level n (r, x)) =
      (action Q L c χ hχ F H hH Y).level n (r, ((diagram Q F).map g).map n x) := by
  have hn := ((map Q (diagramHomotopyAt
    (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH r)) ≫
      indexMap Q L χ F).naturality g
  have hx := congrArg (fun f => f.map n x) hn.symm
  have hX := congrArg (fun f => f.map n x) (action_at Q L c χ hχ F H hH X r)
  have hY := congrArg (fun f => f.map n (((diagram Q F).map g).map n x))
    (action_at Q L c χ hχ F H hH Y r)
  exact (congrArg (((diagram Q F).map (L.map g)).map n) hX).trans (hx.trans hY.symm)

/-- The complete original null cylinder keeps both track and cone times under the action. -/
@[colib_tag "COL-0516", colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrack.lean:120-137"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem action_sourceNull (X : C) (n : ℕ) (r s : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space n) :
    (action Q L c χ hχ F H hH X).level n
        (r, (StrictSquare.sourceNullHomotopy
          (F.mapArrow.mapArrow.obj (Q.obj X))).level n (s, x)) =
      (StrictSquare.sourceNullHomotopy
        (F.mapArrow.mapArrow.obj (Q.obj (L.obj X)))).level n
          (s, (F.map (χ.inv.app X).left.left).map n
            ((H (Q.obj X).left.left).level n (r, x))) := by
  have h := (diagramSquareMapHomotopy
    (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F)
    H hH (Q.obj X)).sourceNull_apply n r s x
  have hm := congrArg (fun z => ((indexMap Q L χ F).app X).map n z) h
  exact hm.trans (StrictSquare.sourceNullHomotopy_naturality_apply
    (F.mapArrow.mapArrow.map (χ.inv.app X)) n s
      ((H (Q.obj X).left.left).level n (r, x)))

end KTheory.Bass.ConeTrack
