/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.EffectiveMonoidal
public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.TransportExact

/-!
# Monoidal stabilization of the geometric Lefschetz twist

The exact tensor on the effective geometric category extends to the
existing geometric category after identifying its transition with
tensoring by the Lefschetz object. This is an application of the native
finite-stage stabilization, along the original transition functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme
open scoped MonoidalCategory

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The canonical abelian structure on the sheaves with transfers. -/
local instance stableMonoidalSheafAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

set_option quotPrecheck false in
local notation "D" => GeometricMotives k
set_option quotPrecheck false in
local notation "L" => geometricEffectiveLefschetzMotive k
set_option quotPrecheck false in
local notation "T" => geometricLefschetzTensor k

variable [MonoidalCategory (EffectiveMotivesMinus k)] [SymmetricCategory (EffectiveMotivesMinus k)]
  [ObjectProperty.IsMonoidal (isEffectiveGeometric k)]
  (e : tensorRight (geometricEffectiveLefschetzMotive k) ≅ geometricLefschetzTensor k)
  (hL : (β_ (geometricEffectiveLefschetzMotive k) (geometricEffectiveLefschetzMotive k)).hom = 𝟙 _)

/-- The original geometric category inherits the tensor from inverting its Lefschetz object. -/
@[instance_reducible]
def geometricMotivesMonoidalCategoryOfTate : MonoidalCategory D :=
  letI := (Functor.FullyFaithful.ofFullyFaithful T).ofIso e.symm |>.full
  letI := (Functor.FullyFaithful.ofFullyFaithful T).ofIso e.symm |>.faithful
  Stabilization.transportedMonoidalCategory L e hL

/-- The induced tensor on geometric motives is symmetric. -/
@[instance_reducible]
def geometricMotivesSymmetricCategoryOfTate :
    letI := geometricMotivesMonoidalCategoryOfTate k e hL
    SymmetricCategory D :=
  letI := (Functor.FullyFaithful.ofFullyFaithful T).ofIso e.symm |>.full
  letI := (Functor.FullyFaithful.ofFullyFaithful T).ofIso e.symm |>.faithful
  Stabilization.transportedSymmetricCategory L e hL

variable [MonoidalPreadditive (EffectiveMotivesMinus k)]

set_option maxHeartbeats 650000 in
-- The finite-stage Hom group instances use the exact geometric transition.
/-- The stabilized tensor is additive in both arguments on the chosen Hom groups. -/
theorem geometricMotivesMonoidalPreadditiveOfTate :
    letI := geometricMotivesMonoidalCategoryOfTate k e hL
    MonoidalPreadditive D :=
  letI := (Functor.FullyFaithful.ofFullyFaithful T).ofIso e.symm |>.full
  letI := (Functor.FullyFaithful.ofFullyFaithful T).ofIso e.symm |>.faithful
  Stabilization.transportedMonoidalPreadditive L e hL

section Exact

variable [(tensorRight (geometricEffectiveLefschetzMotive k)).Full]
  [(tensorRight (geometricEffectiveLefschetzMotive k)).Faithful]
  [(tensorRight (geometricEffectiveLefschetzMotive k)).CommShift ℤ]
  [NatTrans.CommShift e.hom ℤ] [(tensorRight (geometricEffectiveLefschetzMotive k)).IsTriangulated]
  [∀ A : EffectiveGeometricMotives k, (tensorLeft A).CommShift ℤ]
  [∀ A : EffectiveGeometricMotives k, (tensorLeft A).IsTriangulated]
  [∀ A : EffectiveGeometricMotives k,
    NatTrans.CommShift
      (Stabilization.tensorLeftTwistIso (geometricEffectiveLefschetzMotive k) A).hom ℤ]

set_option maxHeartbeats 650000 in
-- The transported shift uses the full-subcategory and finite-stage instances.
/-- The transported left tensor preserves distinguished triangles on the
original geometric category. -/
theorem geometricMotivesTensorLeftExactOfTate (A : D) :
    letI := geometricMotivesMonoidalCategoryOfTate k e hL
    ∃ s : (tensorLeft A).CommShift ℤ, letI := s; (tensorLeft A).IsTriangulated :=
  ⟨Stabilization.transportedTensorLeftCommShift L e hL A,
    Stabilization.transportedTensorLeft_isTriangulated L e hL A⟩

set_option maxHeartbeats 650000 in
-- The transported shift uses the full-subcategory and finite-stage instances.
/-- The transported right tensor preserves distinguished triangles on the
original geometric category. -/
theorem geometricMotivesTensorRightExactOfTate (A : D) :
    letI := geometricMotivesMonoidalCategoryOfTate k e hL
    ∃ s : (tensorRight A).CommShift ℤ, letI := s; (tensorRight A).IsTriangulated :=
  ⟨Stabilization.transportedTensorRightCommShift L e hL A,
    Stabilization.transportedTensorRight_isTriangulated L e hL A⟩

end Exact

end AlgebraicGeometry.MotivicHomotopy
