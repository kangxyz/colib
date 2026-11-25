/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareMergedSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareTracks
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumTripleNativeEvaluation

/-!
# Three full scalar lifts into the merged double-square simplex

The three relative comparisons retain both original time coordinates at each level,
including zero. The common vertices are identified by the actual scheme-square equalities;
the ensuing rectangular pasting is a separate comparison.
Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/DoubleSquareMergedLifts.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareMergedSimplex

open BoundedFlatPerfectSplitTripleParameters (comparisonParameter)
open BoundedFlatPerfectDoubleSquareTrack (firstTriple middleTriple lastTriple)

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The split-triple comparison parameter embedded in the first face of the common 23-simplex. -/
def firstParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 18)) :=
  ⟨fun z ↦ StdSimplex.map firstFace.toOrderHom (comparisonParameter z),
    by fun_prop⟩

/-- The split-triple comparison parameter embedded in the middle face of the common 23-simplex. -/
def middleParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 18)) :=
  ⟨fun z ↦ StdSimplex.map middleFace.toOrderHom (comparisonParameter z),
    by fun_prop⟩

/-- The split-triple comparison parameter embedded in the last face of the common 23-simplex. -/
def lastParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 18)) :=
  ⟨fun z ↦ StdSimplex.map lastFace.toOrderHom (comparisonParameter z),
    by fun_prop⟩

/-- Every point of the literal firstTriple is evaluated in the common family. -/
theorem first_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (BoundedFlatPerfectTripleSimplex.structureOn A)).space n) :
    prespectrumSimplexFamily (simplex p q p' q' a b c hp hq) n
      (firstParameter (r, s), x) =
      (firstTriple (p := p) (q := q) (c := c)).level n (r, (s, x)) := by
  change prespectrumSimplexFamily _ n
    (StdSimplex.map firstFace.toOrderHom (comparisonParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, first_face]
  refine (BoundedFlatPerfectSplitTripleSimplex.comparison_native_evaluation c q p n r s x).trans ?_
  rfl

/-- Every point of middleTriple retains its original hq endpoint transport. -/
theorem middle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (BoundedFlatPerfectTripleSimplex.structureOn A)).space n) :
    prespectrumSimplexFamily (simplex p q p' q' a b c hp hq) n
      (middleParameter (r, s), x) =
      (middleTriple p q q' b c hq).level n (r, (s, x)) := by
  change prespectrumSimplexFamily _ n
    (StdSimplex.map middleFace.toOrderHom (comparisonParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, middle_face]
  refine (BoundedFlatPerfectSplitTripleSimplex.comparison_native_evaluation q' b p n r s x).trans ?_
  rfl

/-- Every point of lastTriple retains both original square transports. -/
theorem last_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (BoundedFlatPerfectTripleSimplex.structureOn A)).space n) :
    prespectrumSimplexFamily (simplex p q p' q' a b c hp hq) n
      (lastParameter (r, s), x) =
      (lastTriple p q p' q' a b c hp hq).level n (r, (s, x)) := by
  change prespectrumSimplexFamily _ n
    (StdSimplex.map lastFace.toOrderHom (comparisonParameter (r, s)), x) = _
  rw [prespectrumSimplexFamily_face, last_face]
  refine (BoundedFlatPerfectSplitTripleSimplex.comparison_native_evaluation q' p' a
    n r s x).trans ?_
  rfl

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareMergedSimplex
