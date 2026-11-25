/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationChart
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareTrackCompatibility
public import Colib.Topology.Prespectrum.RelativeHomotopyCommonPrefixSquare
public import Colib.Topology.Prespectrum.RelativeHomotopyPrefixTransport
/-!
# Original evaluation along an arbitrary commuting geometric square
Both original split composition comparisons are retained. Their common total evaluation is
cancelled by explicit relative path contractions, yielding the whole moving projection square.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCommutingSquare
open GlobalSectionChangeIndex
/-- The original first evaluation leg with only strict source association transported. -/
def firstLeg {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (sectionMap (f ≫ g) ≫ evaluation X)
      ((sectionMap g ≫ evaluation Y) ≫ boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  (Homotopy.precomp (sectionMap g) (evaluationComparison f)).cast
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ evaluation X)
        ((sectionDiagram.map_comp g.op f.op).symm)))
    (Category.assoc _ _ _).symm

/-- The unchanged split raw composition after actual evaluation. -/
def totalLeg {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (evaluation Z ≫ boundedAboveFlatPerfectPullbackPrespectrumMap (f ≫ g))
      ((evaluation Z ≫ boundedAboveFlatPerfectPullbackPrespectrumMap g) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  (Homotopy.precomp (evaluation Z)
    (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g)).cast
    rfl (Category.assoc _ _ _).symm

/-- Both selected original evaluation routes, without changing any path coordinate. -/
def compositionLegs {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((evaluationComparison (f ≫ g)).trans (totalLeg f g)).RelHomotopy
      ((firstLeg f g).trans
        ((evaluationComparison g).postcomp (boundedAboveFlatPerfectPullbackPrespectrumMap f))) :=
  (evaluationCompositionRelHomotopy f g).ofLevels _ _ (fun _ => rfl) (fun _ => rfl)

variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
  (h : p ≫ v = q ≫ w)

include h in
/-- The source transport uses only the stated equality of actual scheme composites. -/
theorem source_eq :
    sectionMap (p ≫ v) ≫ evaluation A = sectionMap (q ≫ w) ≫ evaluation A :=
  congrArg (fun f => sectionMap f ≫ evaluation A) h

/-- The second original evaluation leg, at the unchanged common total source. -/
def sourceTrack := (firstLeg q w).cast (source_eq p v q w h).symm rfl

/-- The second original total track, with only its source endpoint transported. -/
def secondTotal := (totalLeg q w).cast
  (congrArg (fun f => evaluation C ≫ boundedAboveFlatPerfectPullbackPrespectrumMap f) h).symm rfl

/-- The original second composition comparison at the actual common total source. -/
def secondComparison :
    ((evaluationComparison (p ≫ v)).trans (secondTotal p v q w h)).RelHomotopy
      ((sourceTrack p v q w h).trans
        ((evaluationComparison w).postcomp (boundedAboveFlatPerfectPullbackPrespectrumMap q))) :=
  Homotopy.RelHomotopy.transportPrefix
    (fun r : A ⟶ C => sectionMap r ≫ evaluation A)
    (fun r : A ⟶ C => evaluation C ≫ boundedAboveFlatPerfectPullbackPrespectrumMap r)
    (fun r => evaluationComparison r) h (compositionLegs q w)

/-- The whole original raw square after evaluation, with its original reverse-forward clock. -/
def rawTrack : Homotopy
    ((evaluation C ≫ boundedAboveFlatPerfectPullbackPrespectrumMap v) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap p)
    ((evaluation C ≫ boundedAboveFlatPerfectPullbackPrespectrumMap w) ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap q) :=
  (Homotopy.precomp (evaluation C)
    (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p v q w h)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- The first original evaluation followed by the unchanged raw commuting-square track. -/
def targetTrack :=
  ((evaluationComparison v).postcomp (boundedAboveFlatPerfectPullbackPrespectrumMap p)).trans
    (rawTrack p v q w h)

/-- The four original moving legs form an actual whole evaluation square. -/
def square : (sourceTrack p v q w h).Square (targetTrack p v q w h)
    (firstLeg p v)
    ((evaluationComparison w).postcomp (boundedAboveFlatPerfectPullbackPrespectrumMap q)) := by
  let Q := Homotopy.RelHomotopy.commonPrefixSquare
    (compositionLegs p v) (secondComparison p v q w h)
  apply Q.ofBoundaryLevels _ _ _ _ (fun _ => rfl) ?_ (fun _ => rfl) (fun _ => rfl)
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · unfold rawTrack
    rw [Homotopy.cast_level, boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy,
      Homotopy.precomp_trans, Homotopy.precomp_symm]
    apply Homotopy.trans_level_congr <;> rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCommutingSquare
