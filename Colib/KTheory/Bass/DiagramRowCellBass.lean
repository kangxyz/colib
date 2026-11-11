/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowCellConeComparison
public import Colib.KTheory.Bass.DiagramBassRowStrength

/-! # Independent cone descent of a natural cell into a genuine row refinement

The input is a whole cross-diagram cell, not a Model structure on the later spectrum.
Its four actual corners descend through the original square cone, inverse geometric index,
and forward row strength. The source-null height remains independent of the cell time.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowCell
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)


variable
  (H : ∀ X, Homotopy ((input L c F q hp hn hs).app X)
    ((input L c F q hp hn hs).app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) (n : ℕ) (t : unitInterval) (x : (F.obj X).space n),
    ((DiagramRowRefinement.diagram F q hp hn).map (L.map g)).map n
      ((H X).level n (t, x)) = (H Y).level n (t, (F.map g).map n x))

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)

/-- The actual inverse interchanges old looping with the computed distinguished row. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellBass.lean:46-51"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def loopRowInverse (X : C) :=
  RowRefinement.parameterLoopingInverse ((ConeTrack.diagram Q F).obj X)
    (DiagramRowInterchange.cone Q F q hp hn X)
    (DiagramRowInterchange.cone_point Q F q hp hn X)

/-- Loop the independent whole cone cell before comparing it with any scalar action. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellBass.lean:52-56"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def rawBass (X : C) :=
  ((cone L c F q hp hn hs H hH Q χ X).parameterLooping).postcomp
    (loopRowInverse F q hp hn Q (L.obj X))

/-- The original row comparison on the actual next Bass diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellBass.lean:57-69"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def bassComparison :
    (strictDiagramFunctor Q).obj F ⟶
      DiagramRowRefinement.diagram ((strictDiagramFunctor Q).obj F)
        (DiagramRowInterchange.bass Q F q hp hn)
        (DiagramRowInterchange.bass_point Q F q hp hn)
        (DiagramRowInterchange.bass_naturality Q F q hp hn) :=
  DiagramRowRefinement.comparison ((strictDiagramFunctor Q).obj F)
    (DiagramRowInterchange.bass Q F q hp hn)
    (DiagramRowInterchange.bass_point Q F q hp hn)
    (DiagramRowInterchange.bass_naturality Q F q hp hn)
    (DiagramRowInterchange.bass_structure Q F q hp hn hs)

/-- The explicit loop/row map preserves the whole genuine comparison, also in degree zero. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellBass.lean:70-88"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
theorem loopRow_comparison (X : C) :
    parameterLoopingMap (coneComparison F q hp hn hs Q X) ≫
        loopRowInverse F q hp hn Q X =
      (bassComparison F q hp hn hs Q).app X := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  cases n with
  | zero =>
    apply Path.ext; funext r
    apply Path.ext; funext s
    apply Path.ext; funext t
    rfl
  | succ k =>
    apply Path.ext; funext s
    apply Path.ext; funext t
    rfl

@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellBass.lean:89-102"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
private theorem loopMap_comp {E E' E'' : LoopPrespectrum.{w}}
    (f : E ⟶ E') (g : E' ⟶ E'') :
    parameterLoopingMap (f ≫ g) = parameterLoopingMap f ≫ parameterLoopingMap g :=
  parameterLoopingFunctor.map_comp f g

variable (A : NaturalTrack.Track L c F)
  (hcell : ∀ X t, (H X).at t = (A.homotopy X).at t ≫
    (DiagramRowRefinement.comparison F q hp hn hs).app (L.obj X))
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

include hcell in
/-- The independently constructed next cell preserves the proved whole action comparison. -/
@[colib_tag "COL-0525", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellBass.lean:103-112"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
theorem rawBass_at_eq (X : C) (t : unitInterval) :
    (rawBass L c F q hp hn hs H hH Q χ X).at t =
      ((A.bass Q χ hχ).homotopy X).at t ≫
        (bassComparison F q hp hn hs Q).app (L.obj X) := by
  change ((cone L c F q hp hn hs H hH Q χ X).parameterLooping).at t ≫
      loopRowInverse F q hp hn Q (L.obj X) = _
  change parameterLoopingMap ((cone L c F q hp hn hs H hH Q χ X).at t) ≫
      loopRowInverse F q hp hn Q (L.obj X) = _
  let a := ((A.cone Q χ hχ).homotopy X).at t
  let b := coneComparison F q hp hn hs Q (L.obj X)
  let d := loopRowInverse F q hp hn Q (L.obj X)
  have hcone := cone_at_eq L c F q hp hn hs H hH A hcell Q χ hχ X t
  have hmap := congrArg (fun f => parameterLoopingMap f ≫ d) hcone
  have hcomp := loopMap_comp a b
  have hrow := loopRow_comparison F q hp hn hs Q (L.obj X)
  exact hmap.trans ((congrArg (fun f => f ≫ d) hcomp).trans
    ((Category.assoc (parameterLoopingMap a) (parameterLoopingMap b) d).trans
      (congrArg (fun f => parameterLoopingMap a ≫ f) hrow)))

end KTheory.Bass.DiagramRowCell
