/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CycleSymbols
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Skew symmetry of the genuine weight-two graph classes

The diagonal of the first torus power descends through the actual reduced
presheaves with transfers. It sends the weight-one graph of a unit to the
repeated-coordinate graph. Polarizing its additivity gives skew symmetry.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalSkewSymmetry

open _root_.AlgebraicGeometry.Scheme
open DiagonalCycleSymbols PresheafWithTransfers NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- The diagonal of the actual first torus power repeats its single coordinate. -/
def diagonalTorus : SmoothSite.torusPower (Spec (.of k)) 1 ⟶
    SmoothSite.torusPower (Spec (.of k)) 2 :=
  SmoothSite.torusPowerLift (Spec (.of k)) 2
    (fun _ => SmoothSite.torusCoordinate (Spec (.of k)) 1 0)

/-- The diagonal of the rational point gives the literal repeated-coordinate tuple. -/
theorem rationalPoint_diagonalTorus (a : kˣ) :
    WeightOne.rationalPoint k a ≫ diagonalTorus k = rationalTuple k 2 ![a, a] := by
  apply SmoothSite.torusPower_hom_ext
  intro i
  rw [Category.assoc, diagonalTorus, SmoothSite.torusPowerLift_coordinate,
    rationalTuple_coordinate]
  have hi : (![a, a] : Fin 2 → kˣ) i = a := by
    fin_cases i <;> rfl
  rw [hi]
  change (smoothUnitPoint (𝟙 (Spec (.of k))) a ≫
    (SmoothSite.torusPowerOneIso (Spec (.of k))).inv) ≫
      (SmoothSite.torusPowerOneIso (Spec (.of k))).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem diagonalTorus_axis :
    SmoothSite.torusInsertOne (Spec (.of k)) 0 0 ≫ diagonalTorus k =
      SmoothSite.torusInsertOne (Spec (.of k)) 0 0 ≫
        SmoothSite.torusInsertOne (Spec (.of k)) 1 0 := by
  have hb : SmoothSite.torusInsertOne (Spec (.of k)) 0 0 ≫
      SmoothSite.torusPowerToBase (Spec (.of k)) 1 =
      SmoothSite.torusPowerToBase (Spec (.of k)) 0 :=
    SmoothSite.torusPower_hom_ext (Spec (.of k)) 0 (fun i => Fin.elim0 i)
  apply SmoothSite.torusPower_hom_ext
  intro i
  rw [Category.assoc, diagonalTorus, SmoothSite.torusPowerLift_coordinate]
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove (0 : Fin 2) i
  · calc
      _ = SmoothSite.torusPowerToBase (Spec (.of k)) 0 ≫ SmoothSite.torusOne (Spec (.of k)) :=
        SmoothSite.torusInsertOne_coordinate_self (Spec (.of k)) 0 0
      _ = (SmoothSite.torusInsertOne (Spec (.of k)) 0 0 ≫
            SmoothSite.torusPowerToBase (Spec (.of k)) 1) ≫ SmoothSite.torusOne (Spec (.of k)) :=
        congrArg (fun f => f ≫ SmoothSite.torusOne (Spec (.of k))) hb.symm
      _ = _ := by
        simp only [Category.assoc, SmoothSite.torusInsertOne_coordinate_self]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [Category.assoc, SmoothSite.torusInsertOne_coordinate_succAbove]

/-- The actual diagonal induces a morphism of reduced presheaves with transfers. -/
def reducedDiagonalTorus : reducedTorus k 1 ⟶ reducedTorus k 2 :=
  reducedTorusDesc k 1
    ((representableLarge k).map ((Cor.graphFunctor k).map (diagonalTorus k)) ≫
      toReducedTorus k 2) (by
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        change (representableLarge k).map
          ((Cor.graphFunctor k).map (SmoothSite.torusInsertOne (Spec (.of k)) 0 0)) ≫
            (representableLarge k).map ((Cor.graphFunctor k).map (diagonalTorus k)) ≫ _ = 0
        rw [← Functor.map_comp_assoc, ← Functor.map_comp, diagonalTorus_axis,
          Functor.map_comp, Functor.map_comp, Category.assoc]
        change torusIdentityAxis k 1 0 ≫
          (torusIdentityAxis k 2 0 ≫ toReducedTorus k 2) = 0
        rw [torusIdentityAxis_toReducedTorus, comp_zero])

/-- The reduced diagonal sends representatives by graph postcomposition. -/
theorem toReducedTorus_reducedDiagonalTorus :
    toReducedTorus k 1 ≫ reducedDiagonalTorus k =
      (representableLarge k).map ((Cor.graphFunctor k).map (diagonalTorus k)) ≫
        toReducedTorus k 2 :=
  toReducedTorus_desc k 1 _ _

/-- The induced raw map preserves the literal repeated-coordinate graph. -/
theorem rawMap_reducedDiagonalTorus_graphUnit (a : kˣ) :
    rawMap k (reducedDiagonalTorus k) (WeightOne.graphUnitClass k a) =
      graphSymbol k 2 ![a, a] := by
  unfold WeightOne.graphUnitClass graphSymbol
  rw [← cycleClass_one, rawMap_cycleClass k (diagonalTorus k) _
    (toReducedTorus_reducedDiagonalTorus k), ← Functor.map_comp, rationalPoint_diagonalTorus]

/-- Multiplying units in the first coordinate adds their genuine ordered graph classes. -/
theorem graphSymbol_mul_left (a b c : kˣ) :
    graphSymbol k 2 ![a * b, c] = graphSymbol k 2 ![a, c] + graphSymbol k 2 ![b, c] := by
  have h (x : kˣ) : Function.update (![a, c] : Fin 2 → kˣ) 0 x = ![x, c] := by
    funext i
    fin_cases i <;> simp
  simpa only [h] using graphSymbol_mul k 2 ![a, c] 0 a b

/-- Multiplying units in the second coordinate adds their genuine ordered graph classes. -/
theorem graphSymbol_mul_right (a b c : kˣ) :
    graphSymbol k 2 ![a, b * c] = graphSymbol k 2 ![a, b] + graphSymbol k 2 ![a, c] := by
  have h (x : kˣ) : Function.update (![a, b] : Fin 2 → kˣ) 1 x = ![a, x] := by
    funext i
    fin_cases i <;> simp
  simpa only [h] using graphSymbol_mul k 2 ![a, b] 1 b c

/-- The repeated-coordinate graph class is additive in its common unit. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/SkewSymmetry.lean:33-56"
  "adaptation" "Repeated-coordinate class via the actual reduced diagonal"]
theorem graphSymbol_diagonal_mul (a b : kˣ) :
    graphSymbol k 2 ![a * b, a * b] = graphSymbol k 2 ![a, a] + graphSymbol k 2 ![b, b] := by
  have h := congrArg (rawMap k (reducedDiagonalTorus k)) (WeightOne.graphUnitClass_mul k a b)
  simpa only [map_add, rawMap_reducedDiagonalTorus_graphUnit] using h

/-- The actual weight-two graph classes are skew-symmetric over every field. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/SkewSymmetry.lean:58-78"
  "adaptation" "Polarization in the same ordered raw graph classes"]
theorem graphSymbol_add_swap (a b : kˣ) :
    graphSymbol k 2 ![a, b] + graphSymbol k 2 ![b, a] = 0 := by
  have h := graphSymbol_diagonal_mul k a b
  rw [graphSymbol_mul_left, graphSymbol_mul_right, graphSymbol_mul_right] at h
  have hs : (graphSymbol k 2 ![a, a] + graphSymbol k 2 ![b, b]) +
      (graphSymbol k 2 ![a, b] + graphSymbol k 2 ![b, a]) =
        (graphSymbol k 2 ![a, a] + graphSymbol k 2 ![b, b]) + 0 := by
    calc
      _ = (graphSymbol k 2 ![a, a] + graphSymbol k 2 ![a, b]) +
          (graphSymbol k 2 ![b, a] + graphSymbol k 2 ![b, b]) := by abel
      _ = _ := by simpa only [add_zero] using h
  exact add_left_cancel hs

/-- Swapping the original coordinates negates their raw class. -/
theorem graphSymbol_swap (a b : kˣ) :
    graphSymbol k 2 ![b, a] = -graphSymbol k 2 ![a, b] :=
  eq_neg_of_add_eq_zero_left (graphSymbol_add_swap k b a)

/-- The repeated-coordinate graph class is annihilated by two. -/
theorem two_nsmul_graphSymbol_diagonal (a : kˣ) : 2 • graphSymbol k 2 ![a, a] = 0 := by
  simpa only [two_nsmul] using graphSymbol_add_swap k a a

end AlgebraicGeometry.MotivicCohomology.DiagonalSkewSymmetry
