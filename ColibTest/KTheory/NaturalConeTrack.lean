/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Bass.ConeTrack

open CategoryTheory Topology Topology.LoopPrespectrum KTheory.Bass
open scoped Topology unitInterval

noncomputable section
universe u v w

section Zero
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (F G : C ⥤ LoopPrespectrum.{w})

example : (strictDiagramFunctor Q).map (diagramZeroMap F G) =
    diagramZeroMap ((strictDiagramFunctor Q).obj F) ((strictDiagramFunctor Q).obj G) :=
  strictDiagramFunctor_map_zero Q F G

example (X : C) (x : (((strictDiagramFunctor Q).obj F).obj X).space 0) :
    (((strictDiagramFunctor Q).map (diagramZeroMap F G)).app X).map 0 x =
      (((strictDiagramFunctor Q).obj G).obj X).point 0 :=
  congrArg (fun f => f.map 0 x) (strictDiagramFunctor_map_zero_app Q F G X)
end Zero

section Square
variable {S T : Arrow (Arrow LoopPrespectrum.{w})} {a b : S ⟶ T}
  (H : StrictSquare.MapHomotopy a b)

example (n : ℕ) (r s : unitInterval) (x : S.left.left.space n) :
    H.cone.level n (r, (StrictSquare.sourceNullHomotopy S).level n (s, x)) =
      (StrictSquare.sourceNullHomotopy T).level n (s, H.source.level n (r, x)) :=
  H.sourceNull_apply n r s x

example (r s : unitInterval) (x : S.left.left.space 0) :
    H.cone.level 0 (r, (StrictSquare.sourceNullHomotopy S).level 0 (s, x)) =
      (StrictSquare.sourceNullHomotopy T).level 0 (s, H.source.level 0 (r, x)) :=
  H.sourceNull_apply 0 r s x

variable
  (U : Homotopy (S.left.hom ≫ S.hom.right) (S.left.hom ≫ S.hom.right))
  (V : Homotopy (T.left.hom ≫ T.hom.right) (T.left.hom ≫ T.hom.right))
  (hU : ∀ n r s x, H.target.level n (r, U.level n (s, x)) =
    V.level n (s, H.source.level n (r, x)))

example (r : unitInterval) :
    (U.postcomp (mappingConeInclusion (StrictSquare.comparison S))).nullLoopMap
        (StrictSquare.sourceNullHomotopy S) ≫ H.looped.at r =
      H.source.at r ≫
        (V.postcomp (mappingConeInclusion (StrictSquare.comparison T))).nullLoopMap
          (StrictSquare.sourceNullHomotopy T) := H.sourceSeed_at U V hU r

example (n : ℕ) (r t : unitInterval) (x : S.left.left.space n) :
    Path.toContinuousMap
        (H.looped.level n (r,
          ((U.postcomp (mappingConeInclusion (StrictSquare.comparison S))).nullLoopMap
            (StrictSquare.sourceNullHomotopy S)).map n x)) t =
      Path.toContinuousMap
        (((V.postcomp (mappingConeInclusion (StrictSquare.comparison T))).nullLoopMap
          (StrictSquare.sourceNullHomotopy T)).map n (H.source.level n (r, x))) t :=
  H.sourceSeed_apply U V hU n r t x
end Square

section Null
variable {C : Type u} [Category.{v} C] {F G K : C ⥤ LoopPrespectrum.{w}}
  (i : F ⟶ G) (c : G ⟶ K)
  (N : ∀ X, Homotopy ((i ≫ c).app X) ((diagramZeroMap F K).app X))
  (hN : ∀ {X Y} (f : X ⟶ Y) n r x,
    (K.map f).map n ((N X).level n (r, x)) =
      (N Y).level n (r, (F.map f).map n x))
  (Q : C ⥤ Arrow (Arrow C)) (X : C)

example : Homotopy ((((strictDiagramFunctor Q).map i).app X) ≫
    (((strictDiagramFunctor Q).map c).app X))
    (zeroHom (((strictDiagramFunctor Q).obj F).obj X)
      (((strictDiagramFunctor Q).obj K).obj X)) :=
  strictDiagramNullHomotopy i c N hN Q X

example (n : ℕ) : (strictDiagramNullHomotopy i c N hN Q X).level n =
    (strictDiagramMapHomotopy N hN Q X).level n :=
  strictDiagramNullHomotopy_level i c N hN Q X n
end Null

section Coefficient
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C) (c : 𝟭 C ⟶ L)
  (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
  (F : C ⥤ LoopPrespectrum.{w})
  (H : ∀ X, Homotopy (F.map (c.app X)) (F.map (c.app X)))
  (hH : ∀ {X Y} (g : X ⟶ Y) n r x,
    (F.map (L.map g)).map n ((H X).level n (r, x)) =
      (H Y).level n (r, (F.map g).map n x))

example (X : C) :
    (ConeTrack.map Q (Functor.whiskerRight c F)).app X ≫
        (ConeTrack.indexMap Q L χ F).app X = (ConeTrack.diagram Q F).map (c.app X) :=
  ConeTrack.coefficient Q L c χ hχ F X

example (X : C) (r : unitInterval) :
    (ConeTrack.action Q L c χ hχ F H hH X).at r =
      ((ConeTrack.map Q (diagramHomotopyAt
        (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH r)) ≫
        ConeTrack.indexMap Q L χ F).app X :=
  ConeTrack.action_at Q L c χ hχ F H hH X r

example {X Y : C} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : ((ConeTrack.diagram Q F).obj X).space n) :
    ((ConeTrack.diagram Q F).map (L.map g)).map n
        ((ConeTrack.action Q L c χ hχ F H hH X).level n (r, x)) =
      (ConeTrack.action Q L c χ hχ F H hH Y).level n
        (r, ((ConeTrack.diagram Q F).map g).map n x) :=
  ConeTrack.action_naturality Q L c χ hχ F H hH g n r x

example (X : C) (n : ℕ) (r s : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space n) :
    (ConeTrack.action Q L c χ hχ F H hH X).level n
        (r, (StrictSquare.sourceNullHomotopy
          (F.mapArrow.mapArrow.obj (Q.obj X))).level n (s, x)) =
      (StrictSquare.sourceNullHomotopy
        (F.mapArrow.mapArrow.obj (Q.obj (L.obj X)))).level n
          (s, (F.map (χ.inv.app X).left.left).map n
            ((H (Q.obj X).left.left).level n (r, x))) :=
  ConeTrack.action_sourceNull Q L c χ hχ F H hH X n r s x
end Coefficient
