/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.Triangulated
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjective
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.UpperBound
import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor

/-!
# Exactness and bounds for the projective reduced torus tensor

The exact structure comes from the original projective quotient and
the exact Nisnevich sheafification. The actual reduced tensor retains
the upper bound of its projective coefficient complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

/-- Use the abelian structure on the target of Nisnevich sheafification. -/
local instance : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

private abbrev nisnevichDerivedMinusInclusion :
    (nisnevichSheafify k).mapDerivedCategoryMinus ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ (nisnevichSheafify k).mapDerivedCategory :=
  Iso.refl _

@[no_expose]
instance : ((nisnevichSheafify k).mapDerivedCategoryMinus).CommShift ℤ :=
  Functor.CommShift.ofComp (nisnevichDerivedMinusInclusion k) ℤ

instance nisnevichDerivedMinus_isTriangulated :
    ((nisnevichSheafify k).mapDerivedCategoryMinus).IsTriangulated := by
  let A := PresheafWithTransfers.{u + 1} k
  let B := SheafWithTransfers.{u + 1} k
  let a := (nisnevichSheafify k).mapDerivedCategory
  let U : DerivedCategory.Minus A ⥤ DerivedCategory A := DerivedCategory.Minus.ι
  let V : DerivedCategory.Minus B ⥤ DerivedCategory B := DerivedCategory.Minus.ι
  let e := nisnevichDerivedMinusInclusion k
  let : ((nisnevichSheafify k).mapDerivedCategoryMinus).CommShift ℤ :=
    Functor.CommShift.ofComp e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  let : U.IsTriangulated := inferInstanceAs
    (((DerivedCategory.TStructure.t (C := A)).minus.ι).IsTriangulated)
  let : V.IsTriangulated := inferInstanceAs
    (((DerivedCategory.TStructure.t (C := B)).minus.ι).IsTriangulated)
  let : a.IsTriangulated := inferInstanceAs
    ((nisnevichSheafify k).mapDerivedCategory).IsTriangulated
  let : (U ⋙ a).IsTriangulated := inferInstance
  exact (Functor.isTriangulated_iff_comp_right e).2
    (inferInstanceAs (U ⋙ a).IsTriangulated)

@[no_expose]
instance : (projectiveReducedTorusTensorToDerivedMinus k).CommShift ℤ := by
  unfold projectiveReducedTorusTensorToDerivedMinus
  infer_instance

instance : (projectiveReducedTorusTensorToDerivedMinus k).IsTriangulated := by
  let G := projectiveDerivedMinusFunctor k (reducedParameterTensorFunctor k)
  let a := (nisnevichSheafify k).mapDerivedCategoryMinus
  let : G.IsTriangulated := inferInstanceAs
    (projectiveDerivedMinusFunctor k (reducedParameterTensorFunctor k)).IsTriangulated
  let : a.IsTriangulated := nisnevichDerivedMinus_isTriangulated k
  exact inferInstanceAs (G ⋙ a).IsTriangulated

/-- The actual reduced projective tensor retains the original
cohomological upper bound. -/
theorem projectiveReducedTorusTensorToDerivedMinus_isLE
    (K : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) (b : ℤ)
    (hK : K.obj.IsLE b) : ((projectiveReducedTorusTensorToDerivedMinus k).obj K).obj.IsLE b := by
  let G := projectiveDerivedMinusFunctor k (reducedParameterTensorFunctor k)
  let A := nisnevichSheafify k
  let : (G.obj K).obj.IsLE b := projectiveDerivedMinusFunctor_isLE k _ K b hK
  exact Stacks.Homology.isLE_mapDerivedCategory_obj A (G.obj K).obj b

end AlgebraicGeometry.SheafWithTransfers
