/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.HomotopyWordMap
public import Colib.KTheory.Bass.WholeSeedWord
public import Colib.KTheory.Bass.SquareConeStrength
public import Colib.KTheory.Bass.LoopStrength

/-!
# The original whole seed word under a finite square interchange

An actual map of strict natural squares and an explicit same-time unit-track
square preserve the original null/unit/null word and give the common-target
seed equation with the original Bass loop strength. The unit-track equation is
an input still to be instantiated geometrically; no whole-seed compatibility
or tower coherence is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.WholeSeedCospan
open PushoutCofiberSquare SquareConeStrength HomotopyWord
variable {C : Type u} [Category.{v} C]

/-- The genuine cone functor applied to all original component square maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/WholeSeedCospan.lean:32"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
def squareConeMap {S T : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))} (e : S ⟶ T) :
    mappingConeDiagram (comparison S) ⟶ mappingConeDiagram (comparison T) :=
  Functor.whiskerRight
    ((ArrowDiagrams.toDiagram.mapArrow ⋙ ArrowDiagrams.toDiagram).map e)
    (strictSquareComparisonFunctor ⋙ mappingConeFunctor)

/-- The original inclusion is retained by the literal square cone map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/WholeSeedCospan.lean:39"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
theorem squareConeMap_inclusion {S T : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))}
    (e : S ⟶ T) (X : C) :
    mappingConeInclusion ((comparison S).app X) ≫ (squareConeMap e).app X =
      e.right.right.app X ≫ mappingConeInclusion ((comparison T).app X) := by
  apply Hom.ext
  funext n
  ext x
  rfl

variable (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})))
  (A : ∀ X, Homotopy ((S.left.hom ≫ S.hom.right).app X)
    ((S.left.hom ≫ S.hom.right).app X)) (hA : Natural A)


variable (Q : C ⥤ Arrow (Arrow C))
  {T : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))} (e : T ⟶ bassSquare S Q)

/-- The original square cone map followed by the checked positive-direction chi. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/WholeSeedCospan.lean:83"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
def chiAlong : mappingConeDiagram (comparison T) ⟶
    (strictDiagramFunctor Q).obj (mappingConeDiagram (comparison S)) :=
  squareConeMap e ≫ chi S Q

/-- Original inclusion compatibility of the actual composite cone map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/WholeSeedCospan.lean:88"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
theorem chiAlong_inclusion (X : C) :
    mappingConeInclusion ((comparison T).app X) ≫ (chiAlong S Q e).app X =
      e.right.right.app X ≫
        (((strictDiagramFunctor Q).map (coneInclusion (comparison S))).app X) := by
  change (mappingConeInclusion ((comparison T).app X) ≫ (squareConeMap e).app X) ≫
    (chi S Q).app X = _
  rw [squareConeMap_inclusion, Category.assoc, chi_inclusion]

/-- The composite retains the original whole source null, without choosing another contraction. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/WholeSeedCospan.lean:97"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
theorem chiAlong_sourceNull (X : C) (n : ℕ) (r : unitInterval)
    (x : (T.left.left.obj X).space n) :
    ((chiAlong S Q e).app X).map n ((sourceNull T X).level n (r,x)) =
      (strictDiagramMapHomotopy (sourceNull S) (sourceNull_naturality S) Q X).level n
        (r, (e.left.left.app X).map n x) := by
  have hn : ((squareConeMap e).app X).map n ((sourceNull T X).level n (r,x)) =
      (sourceNull (bassSquare S Q) X).level n (r, (e.left.left.app X).map n x) :=
    StrictSquare.sourceNullHomotopy_naturality_apply
      (((ArrowDiagrams.toDiagram.mapArrow ⋙ ArrowDiagrams.toDiagram).map e).app X) n r x
  exact (congrArg (((chi S Q).app X).map n) hn).trans
    (chi_sourceNull S Q X n r ((e.left.left.app X).map n x))

variable (A' : ∀ X, Homotopy ((T.left.hom ≫ T.hom.right).app X)
    ((T.left.hom ≫ T.hom.right).app X)) (hA' : Natural A')
  (hunit : ∀ X r,
    (A' X).at r ≫ e.right.right.app X =
      e.left.left.app X ≫ (strictDiagramMapHomotopy A hA Q X).at r)

include hunit in
/-- The explicit unit-track square gives the full original cone-action square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/WholeSeedCospan.lean:117"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
theorem chiAlong_coneAction (X : C) (n : ℕ) :
    ((coneAction T A' X).postcomp ((chiAlong S Q e).app X)).level n =
      ((strictDiagramMapHomotopy (coneAction S A) (coneAction_naturality S A hA) Q X).precomp
        (e.left.left.app X)).level n := by
  apply ContinuousMap.ext
  rintro ⟨r,x⟩
  have hm := DFunLike.congr_fun
    (map_postcomp A hA (coneInclusion (comparison S)) Q X n)
    (r, (e.left.left.app X).map n x)
  have hc : (A' X).at r ≫ mappingConeInclusion ((comparison T).app X) ≫
      (chiAlong S Q e).app X =
      e.left.left.app X ≫ (strictDiagramMapHomotopy A hA Q X).at r ≫
        (((strictDiagramFunctor Q).map (coneInclusion (comparison S))).app X) := by
    rw [chiAlong_inclusion, ← Category.assoc, hunit, Category.assoc]
  exact (congrArg (fun k => k.map n x) hc).trans hm.symm

include hunit in
/-- The entire prescribed original word is preserved, including both original concatenations. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/WholeSeedCospan.lean:135"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
theorem chiAlong_word (X : C) (n : ℕ) :
    ((word T A' X).postcomp ((chiAlong S Q e).app X)).level n =
      ((strictDiagramMapHomotopy (word S A) (word_naturality S A hA) Q X).precomp
        (e.left.left.app X)).level n := by
  have hn : ((sourceNull T X).postcomp ((chiAlong S Q e).app X)).level n =
      ((strictDiagramMapHomotopy (sourceNull S) (sourceNull_naturality S) Q X).precomp
        (e.left.left.app X)).level n := by
    apply ContinuousMap.ext
    rintro ⟨r,x⟩
    exact chiAlong_sourceNull S Q e X n r x
  unfold word
  rw [map_trans (fun Y => (sourceNull S Y).symm)
      (fun Y => (coneAction S A Y).trans (sourceNull S Y))
      (natural_symm _ (sourceNull_naturality S))
      (natural_trans _ _ (coneAction_naturality S A hA) (sourceNull_naturality S)),
    map_symm (sourceNull S) (sourceNull_naturality S),
    map_trans (coneAction S A) (sourceNull S)
      (coneAction_naturality S A hA) (sourceNull_naturality S)]
  rw [Homotopy.postcomp_trans, Homotopy.postcomp_symm, Homotopy.postcomp_trans,
    Homotopy.precomp_trans, Homotopy.precomp_symm, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr
  · exact Homotopy.symm_level_congr _ _ n hn
  · exact Homotopy.trans_level_congr _ _ _ _ n
      (chiAlong_coneAction S A hA Q e A' hunit X n) hn

include hunit in
/-- The actual seed common-target equality follows from the original whole unit square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/WholeSeedCospan.lean:162"
  "adaptation" "Original whole null/unit/null word under the actual forward comparison."]
theorem seed_cospan (X : C) :
    (seed T A' hA').app X ≫ parameterLoopingMap ((chiAlong S Q e).app X) =
      e.left.left.app X ≫ (((strictDiagramFunctor Q).map (seed S A hA)).app X) ≫
        LoopStrength.strength Q (mappingConeDiagram (comparison S)) X := by
  have hs := LoopStrength.strength_square (word S A) (word_naturality S A hA) Q X
  have hw : (seed T A' hA').app X ≫ parameterLoopingMap ((chiAlong S Q e).app X) =
      e.left.left.app X ≫ (LoopStrength.bassHomotopy
        (word S A) (word_naturality S A hA) Q X).zeroLoopMap := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    apply Path.ext
    funext r
    exact DFunLike.congr_fun (chiAlong_word S A hA Q e A' hunit X n) (r,x)
  exact hw.trans (congrArg (fun k => e.left.left.app X ≫ k) hs.symm)

end KTheory.Bass.WholeSeedCospan
