/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.Topology.Prespectrum.StrictSquareSeedNaturality
import Colib.KTheory.Bass.StrictDiagramMap

/-! Full-signature consumers for the quotient, strict-square null, scalar seed and finite tower. -/

open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
noncomputable section
universe u v w

section Pushout
variable {A B C : LoopPrespectrum.{w}} (f : A ⟶ B) (g : A ⟶ C)

example (n : ℕ) (x : A.space n) :
    HomotopyPushout.cylinder f g n (0, x) = HomotopyPushout.left f g n (f.map n x) :=
  HomotopyPushout.cylinder_zero f g n x

example (n : ℕ) (x : A.space n) :
    HomotopyPushout.cylinder f g n (1, x) = HomotopyPushout.right f g n (g.map n x) :=
  HomotopyPushout.cylinder_one f g n x

example (n : ℕ) (s : unitInterval) :
    HomotopyPushout.cylinder f g n (s, A.point n) = HomotopyPushout.point f g n :=
  HomotopyPushout.cylinder_point f g n s

example (n : ℕ) : Continuous (HomotopyPushout.structureMap f g n) :=
  (HomotopyPushout.structureMap f g n).continuous

example (n : ℕ) (s t : unitInterval) (x : A.space n) :
    (HomotopyPushout.prespectrum f g).structureMap n
      (HomotopyPushout.cylinder f g n (s, x)) t =
    HomotopyPushout.cylinder f g (n + 1) (s, A.structureMap n x t) := rfl

example (n : ℕ) (s t : unitInterval) (x : A.space n) :
    (HomotopyPushout.glue f g).level (n + 1) (s, A.structureMap n x t) =
      (HomotopyPushout.prespectrum f g).structureMap n
        ((HomotopyPushout.glue f g).level n (s, x)) t :=
  (HomotopyPushout.glue f g).comm n s x t
end Pushout

section Square
open StrictSquare
variable {S T U : Arrow (Arrow LoopPrespectrum.{w})} (e : S ⟶ T) (e' : T ⟶ U)

example : spanMap e ≫ comparison T = comparison S ≫ e.right.right :=
  comparison_naturality e

example : strictSquareLoopedConeFunctor.map (e ≫ e') =
    strictSquareLoopedConeFunctor.map e ≫ strictSquareLoopedConeFunctor.map e' :=
  strictSquareLoopedConeFunctor.map_comp e e'

example : strictSquareLoopedConeFunctor.map (𝟙 S) =
    𝟙 (strictSquareLoopedConeFunctor.obj S) := strictSquareLoopedConeFunctor.map_id S

example :
    ((sourceNullHomotopy S).postcomp
      (mappingConeMap (strictSquareComparisonFunctor.map e))).cast
      (sourceNullHomotopy_start_naturality e) (sourceNullHomotopy_end_naturality e) =
    (sourceNullHomotopy T).precomp e.left.left := sourceNullHomotopy_naturality e

example (n : ℕ) (s t : unitInterval) (x : S.left.left.space n) :
    (sourceNullHomotopy S).level (n + 1) (s, S.left.left.structureMap n x t) =
      (mappingCone (comparison S)).structureMap n ((sourceNullHomotopy S).level n (s, x)) t :=
  (sourceNullHomotopy S).comm n s x t

example (s : unitInterval) (x : S.left.left.space 0) :
    (mappingConeMap (strictSquareComparisonFunctor.map e)).map 0
      ((sourceNullHomotopy S).level 0 (s, x)) =
    (sourceNullHomotopy T).level 0 (s, e.left.left.map 0 x) :=
  sourceNullHomotopy_naturality_apply e 0 s x

variable (H : Homotopy (S.left.hom ≫ S.hom.right) (S.left.hom ≫ S.hom.right))
    (K : Homotopy (T.left.hom ≫ T.hom.right) (T.left.hom ≫ T.hom.right))
    (h : ∀ n r x, e.right.right.map n (H.level n (r, x)) =
      K.level n (r, e.left.left.map n x))

example :
    (H.postcomp (mappingConeInclusion (comparison S))).nullLoopMap
      (sourceNullHomotopy S) ≫ strictSquareLoopedConeFunctor.map e =
    e.left.left ≫ (K.postcomp (mappingConeInclusion (comparison T))).nullLoopMap
      (sourceNullHomotopy T) := sourceSeed_naturality e H K h

example (n : ℕ) (t : unitInterval) (x : S.left.left.space n) :
    Path.toContinuousMap ((strictSquareLoopedConeFunctor.map e).map n
      (((H.postcomp (mappingConeInclusion (comparison S))).nullLoopMap
        (sourceNullHomotopy S)).map n x)) t =
    Path.toContinuousMap (((K.postcomp (mappingConeInclusion (comparison T))).nullLoopMap
      (sourceNullHomotopy T)).map n (e.left.left.map n x)) t :=
  sourceSeed_naturality_apply e H K h n t x
end Square

section Diagram
open KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G : C ⥤ LoopPrespectrum.{w}}
    (seedF : F ⟶ (strictDiagramFunctor Q).obj F) (seedG : G ⟶ (strictDiagramFunctor Q).obj G)
    (a : F ⟶ G) (h : seedF ≫ (strictDiagramFunctor Q).map a = a ≫ seedG)

example (X : C) : ((strictDiagramFunctor Q).obj F).obj X =
    parameterLooping (mappingCone (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))) :=
  strictDiagramFunctor_obj Q F X

example (n : ℕ) :
    strictDiagramTransition Q seedF n ≫ (strictDiagramIterate Q (n + 1)).map a =
    (strictDiagramIterate Q n).map a ≫ strictDiagramTransition Q seedG n :=
  strictDiagramTransition_map Q seedF seedG a h n

example : strictDiagramTransition Q seedF 0 = seedF := strictDiagramTransition_zero Q seedF

example : strictDiagramTransition Q seedF 0 ≫ (strictDiagramIterate Q 1).map a =
    (strictDiagramIterate Q 0).map a ≫ strictDiagramTransition Q seedG 0 :=
  strictDiagramTransition_map Q seedF seedG a h 0
end Diagram
