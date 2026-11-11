/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientAutomorphism
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectRankOne

/-!
# The first coefficient row in the original degree-zero complex model

Apply the original degree-zero single functor to the independently specified module row
`0, O, 0`. The resulting original complexes form a bounded-flat quotient row. The actual zero
isomorphisms and identity on the unchanged rank-one object identify it with the canonical
Waldhausen one-step row. This retains the coefficient model before any K-one class map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial ZeroObject
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Every actual degree-zero coefficient entry is bounded-flat perfect. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientSingle.lean:31-41"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientSingle_boundedFlat (X : Scheme.{u}) (p : Interval ⦋1⦌) :
    boundedAboveFlatPerfectComplex X.toRingedSpace ((CochainComplex.singleFunctor X.Modules 0).obj
      ((tensorUnitCoefficientRow X).obj p)) := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j
  · exact boundedAboveFlatPerfectComplex_of_isZero
      ((CochainComplex.singleFunctor X.Modules 0).map_isZero (isZero_zero _))
  · exact (boundedAboveFlatRankOne X).property
  · exact False.elim (Nat.not_succ_le_zero 0 hij)
  · exact boundedAboveFlatPerfectComplex_of_isZero
      ((CochainComplex.singleFunctor X.Modules 0).map_isZero (isZero_zero _))

/-- The actual single of the original module coefficient row, retaining both original zero singles.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientSingle.lean:45-48"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientSingle (X : Scheme.{u}) : Interval ⦋1⦌ ⥤ (boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory :=
  (boundedAboveFlatPerfectComplex X.toRingedSpace).lift
    (tensorUnitCoefficientRow X ⋙ CochainComplex.singleFunctor X.Modules 0)
    (tensorUnitCoefficientSingle_boundedFlat X)

/-- The original zero singles on the two coefficient diagonal positions are actual zero objects. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientSingle.lean:51-56"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientSingle_zero (X : Scheme.{u}) (i : Fin 2) :
    IsZero ((tensorUnitCoefficientSingle X).obj (interval i i le_rfl)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
  fin_cases i <;> exact
    ((CochainComplex.singleFunctor X.Modules 0).map_isZero (isZero_zero X.Modules)).eq_of_src _ _

/-- The coefficient comparison uses its actual zero isomorphisms and unchanged rank-one object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientSingle.lean:59-81"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientSingleIsoAt (X : Scheme.{u}) (p : Interval ⦋1⦌) :
    (tensorUnitCoefficientSingle X).obj p ≅
      (oneDiagram (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) (boundedAboveFlatRankOne
      X)).obj p := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  change Fin 2 at i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      exact (tensorUnitCoefficientSingle_zero X 0).iso (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace).isZero
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Iso.refl _
  | succ i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases j using Fin.cases with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hij)
    | succ j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact (tensorUnitCoefficientSingle_zero X 1).iso (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace).isZero

/-- All original coefficient single arrows commute with the displayed zero comparisons. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientSingle.lean:84-99"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientSingleIsoAt_naturality (X : Scheme.{u})
    {p q : Interval ⦋1⦌} (f : p ⟶ q) :
    (tensorUnitCoefficientSingle X).map f ≫ (tensorUnitCoefficientSingleIsoAt X q).hom =
      (tensorUnitCoefficientSingleIsoAt X p).hom ≫
        (oneDiagram (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) (boundedAboveFlatRankOne
      X)).map f := by
  rcases p with ⟨⟨i, j⟩, hij⟩
  rcases q with ⟨⟨k, l⟩, hkl⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> solve
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact False.elim (Nat.not_succ_le_zero 0 hkl)
  | exact (tensorUnitCoefficientSingle_zero X 0).eq_of_src _ _
  | exact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero.eq_of_tgt _ _
  | have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    simp

/-- The whole single coefficient row is identified with the original rank-one quotient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientSingle.lean:102-106"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
def tensorUnitCoefficientSingleIso (X : Scheme.{u}) :
    tensorUnitCoefficientSingle X ≅
      oneDiagram (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) (boundedAboveFlatRankOne X) :=
  NatIso.ofComponents (tensorUnitCoefficientSingleIsoAt X)
    (tensorUnitCoefficientSingleIsoAt_naturality X)

/-- The independently constructed coefficient single row has all original row conditions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    TensorUnitCoefficientSingle.lean:109-112"
  "adaptation" "Original actual coefficient single, forward unit and weak representative"]
theorem tensorUnitCoefficientSingle_isRow (X : Scheme.{u}) :
    IsRow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) (tensorUnitCoefficientSingle X) :=
  (oneDiagram_isRow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) _).of_iso _
    (tensorUnitCoefficientSingleIso X).symm

end AlgebraicGeometry.Scheme.Modules
