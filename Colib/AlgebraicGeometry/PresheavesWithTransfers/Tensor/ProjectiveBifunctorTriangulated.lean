/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.Triangulated
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.LeftFactorTriangulated
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.RightFactorTriangulated

/-!
# Exactness of the signed projective bifunctor

The native Stacks mapping-cone comparisons apply to a general additive
bifunctor. They identify the one-sided shift and triangle comparisons on
the existing signed total. The projective equivalence and the inclusion
of bounded-above objects transport these comparisons to the derived functors.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor.Reduction

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ

variable (F : PST(k) ⥤ PST(k) ⥤ PST(k)) [F.Additive] [∀ P, (F.obj P).Additive]

/-- The second slot of the selected homotopy bifunctor is the Stacks mapping-cone functor. -/
def signedTotalHomotopyBifunctorLeftIso (K : HomotopyCategory PST(k) c) :
    ((signedTotalHomotopyBifunctor F).obj K) ≅ bifunctorPhi F K.as :=
  CategoryTheory.Quotient.natIsoLift (homotopic PST(k) c) (bifunctorPhiFactors F K.as).symm

/-- The first slot of the selected homotopy bifunctor is the Stacks mapping-cone functor. -/
def signedTotalHomotopyBifunctorRightIso (L : HomotopyCategory PST(k) c) :
    ((signedTotalHomotopyBifunctor F).flip.obj L) ≅ bifunctorPhiR F L.as :=
  CategoryTheory.Quotient.natIsoLift (homotopic PST(k) c) (bifunctorPhiRFactors F L.as).symm

variable [HasDerivedCategory.{w} PST(k)]

/-- The signed derived total commutes with shift in the second variable and is triangulated. -/
theorem projectiveDerivedMinusBifunctor_exact_right (K : DerivedCategory.Minus PST(k)) :
    ∃ s : ((projectiveDerivedMinusBifunctor F).obj K).CommShift ℤ,
      letI := s; ((projectiveDerivedMinusBifunctor F).obj K).IsTriangulated := by
  let E := (boundedAboveProjectiveEquivalence k).inverse
  let U := (boundedAboveProjectiveCondition k).ι
  let Q := DerivedCategory.Qh (C := PST(k))
  let L := U.obj (E.obj K)
  let B := (projectiveDerivedMinusBifunctor F).obj K
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let C := bifunctorPhi F L.as
  let H := E ⋙ (U ⋙ (C ⋙ Q))
  let : C.CommShift ℤ := bifunctorXi F L.as
  let : E.IsTriangulated := inferInstanceAs
    (((boundedAboveProjectiveEquivalence k).inverse).IsTriangulated)
  let : U.IsTriangulated := inferInstanceAs ((boundedAboveProjectiveCondition k).ι.IsTriangulated)
  let : Q.IsTriangulated := inferInstanceAs ((DerivedCategory.Qh (C := PST(k))).IsTriangulated)
  let : C.IsTriangulated := bifunctorPhi_isTriangulated F L.as
  let : (C ⋙ Q).IsTriangulated := inferInstance
  let : (U ⋙ (C ⋙ Q)).IsTriangulated := inferInstance
  let hH : H.IsTriangulated := inferInstanceAs (E ⋙ (U ⋙ (C ⋙ Q))).IsTriangulated
  let e : B ⋙ V ≅ H := Functor.isoWhiskerLeft (E ⋙ U)
    (Functor.isoWhiskerRight (signedTotalHomotopyBifunctorLeftIso F L) Q)
  let : B.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact ⟨inferInstance, (Functor.isTriangulated_iff_comp_right e).2 hH⟩

/-- The signed derived total commutes with shift in the first variable and is triangulated. -/
theorem projectiveDerivedMinusBifunctor_exact_left (L : DerivedCategory.Minus PST(k)) :
    ∃ s : ((projectiveDerivedMinusBifunctor F).flip.obj L).CommShift ℤ,
      letI := s; ((projectiveDerivedMinusBifunctor F).flip.obj L).IsTriangulated := by
  let E := (boundedAboveProjectiveEquivalence k).inverse
  let U := (boundedAboveProjectiveCondition k).ι
  let Q := DerivedCategory.Qh (C := PST(k))
  let K := U.obj (E.obj L)
  let B := (projectiveDerivedMinusBifunctor F).flip.obj L
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let C := bifunctorPhiR F K.as
  let H := E ⋙ (U ⋙ (C ⋙ Q))
  let : C.CommShift ℤ := bifunctorXiR F K.as
  let : E.IsTriangulated := inferInstanceAs
    (((boundedAboveProjectiveEquivalence k).inverse).IsTriangulated)
  let : U.IsTriangulated := inferInstanceAs ((boundedAboveProjectiveCondition k).ι.IsTriangulated)
  let : Q.IsTriangulated := inferInstanceAs ((DerivedCategory.Qh (C := PST(k))).IsTriangulated)
  let : C.IsTriangulated := bifunctorPhiR_isTriangulated F K.as
  let : (C ⋙ Q).IsTriangulated := inferInstance
  let : (U ⋙ (C ⋙ Q)).IsTriangulated := inferInstance
  let hH : H.IsTriangulated := inferInstanceAs (E ⋙ (U ⋙ (C ⋙ Q))).IsTriangulated
  let e : B ⋙ V ≅ H := Functor.isoWhiskerLeft (E ⋙ U)
    (Functor.isoWhiskerRight (signedTotalHomotopyBifunctorRightIso F K) Q)
  let : B.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact ⟨inferInstance, (Functor.isTriangulated_iff_comp_right e).2 hH⟩

end AlgebraicGeometry.PresheafWithTransfers
