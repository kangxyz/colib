/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf
public import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Total singular complexes of transfer cochain complexes

Apply the original singular construction in each coefficient degree.
The total differential combines the coefficient differential with the
signed simplex differential using Mathlib's cochain totalization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Opposite

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "c" => ComplexShape.up ℤ

local instance (I : Type) : HasColimitsOfShape (Discrete I) (PresheafWithTransfers.{v} k) := by
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{v} :=
    AddCommGrpCat.hasColimitsOfShape
  let : HasColimitsOfShape (Discrete I) ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) :=
    functorCategoryHasColimitsOfShape
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I)
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v})

local instance (K : HomologicalComplex₂ (PresheafWithTransfers.{v} k) c c) :
    K.HasTotal c := fun i =>
  HasColimitsOfShape.has_colimit
    (Discrete.functor (K.toGradedObject.mapObjFun (ComplexShape.π c c c) i))

local instance : (singularCochainFunctor 0 : PresheafWithTransfers.{v} k ⥤
    CochainComplex (PresheafWithTransfers.{v} k) ℤ).Additive := by
  unfold singularCochainFunctor
  infer_instance

/-- The coefficient degree is the first degree of the singular bicomplex. -/
def singularBicomplexFunctor :
    CochainComplex (PresheafWithTransfers.{v} k) ℤ ⥤
      HomologicalComplex₂ (PresheafWithTransfers.{v} k) c c :=
  (singularCochainFunctor 0).mapHomologicalComplex c

/-- The actual total of the singular bicomplex, with the native cochain signs. -/
def singularTotalFunctor :
    CochainComplex (PresheafWithTransfers.{v} k) ℤ ⥤
      CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
  singularBicomplexFunctor k ⋙ HomologicalComplex₂.totalFunctor (PresheafWithTransfers.{v} k) c c c

/-- Each bicomplex column is the existing singular complex in degrees at most zero. -/
@[simp]
theorem singularBicomplexFunctor_obj_X (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ)
    (p : ℤ) :
    ((singularBicomplexFunctor k).obj K).X p = singularCochainComplex (K.X p) 0 := rfl

/-- The total complex preserves the given upper bound on coefficient degrees. -/
theorem singularTotalFunctor_obj_isStrictlyLE (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ)
    (n : ℤ) [K.IsStrictlyLE n] : ((singularTotalFunctor k).obj K).IsStrictlyLE n := by
  apply (CochainComplex.isStrictlyLE_iff _ n).2
  intro i hi
  apply (IsZero.iff_id_eq_zero _).2
  change 𝟙 ((((singularBicomplexFunctor k).obj K).total c).X i) = 0
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p + q = i at hpq
  have hzero : IsZero ((singularCochainComplex (K.X p) 0).X q) := by
    by_cases hq : 0 < q
    · exact isZero_singularCochainComplex_X _ 0 q hq
    · have hp : n < p := by omega
      let ev := singularCochainFunctor (k := k) 0 ⋙
        HomologicalComplex.eval (PresheafWithTransfers.{v} k) c q
      exact ev.map_isZero (K.isZero_of_isStrictlyLE n p hp)
  exact hzero.eq_of_src _ _

end AlgebraicGeometry.PresheafWithTransfers
