/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TateTwist
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReducedTorusObject
public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Effective
import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# The Tate twist on effective geometric motives

The native reduced torus tensor takes each smooth motive to the retract of
the motive of its torus product cut out by the unit section. Exactness
extends this property to the thick subcategory.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Use the native abelian structure of Nisnevich sheaves with transfers. -/
local instance geometricTateAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The native reduced torus tensor preserves the effective geometric property. -/
theorem isEffectiveGeometric_effectiveReducedTorusTensor {K : EffectiveMotivesMinus k}
    (hK : isEffectiveGeometric k K) :
    isEffectiveGeometric k ((effectiveReducedTorusTensorFunctor k).obj K) := by
  let T := effectiveReducedTorusTensorFunctor k
  let Q := (isEffectiveGeometric k).inverseImage T
  let : Q.IsStableUnderRetracts :=
    ObjectProperty.isStableUnderRetracts_inverseImage _ T
  let : T.CommShift ℤ := inferInstanceAs ((effectiveReducedTorusTensorFunctor k).CommShift ℤ)
  let : T.IsTriangulated := inferInstanceAs ((effectiveReducedTorusTensorFunctor k).IsTriangulated)
  let : Q.IsTriangulated := inferInstance
  refine (isEffectiveGeometric_le_iff k Q).2 (fun X => ?_) K hK
  exact (isEffectiveGeometric k).prop_of_retract
    (effectiveReducedTorusTensorRepresentableRetract k X)
    (isEffectiveGeometric_effectiveMotive k _)

/-- Restrict the native exact reduced torus tensor to geometric motives. -/
def geometricReducedTorusTensor :
    EffectiveGeometricMotives k ⥤ EffectiveGeometricMotives k :=
  (isEffectiveGeometric k).lift
    (effectiveGeometricMotivesInclusion k ⋙ effectiveReducedTorusTensorFunctor k)
    (fun K => isEffectiveGeometric_effectiveReducedTorusTensor k K.property)

instance : (geometricReducedTorusTensor k).CommShift ℤ := by
  unfold geometricReducedTorusTensor
  infer_instance

instance : (geometricReducedTorusTensor k).IsTriangulated := by
  unfold geometricReducedTorusTensor
  infer_instance

/-- The original cancellation theorem restricts to geometric motives. -/
def geometricReducedTorusTensorFullyFaithful : (geometricReducedTorusTensor k).FullyFaithful := by
  let f := effectiveReducedTorusTensorFullyFaithful k
  let : (effectiveReducedTorusTensorFunctor k).Full := f.full
  let : (effectiveReducedTorusTensorFunctor k).Faithful := f.faithful
  unfold geometricReducedTorusTensor
  exact Functor.FullyFaithful.ofFullyFaithful _

instance : (geometricReducedTorusTensor k).Full :=
  (geometricReducedTorusTensorFullyFaithful k).full

instance : (geometricReducedTorusTensor k).Faithful :=
  (geometricReducedTorusTensorFullyFaithful k).faithful

/-- The signed weight-one Tate twist preserves geometric motives. -/
theorem isEffectiveGeometric_reducedTorusShift (n : ℤ) {K : EffectiveMotivesMinus k}
    (hK : isEffectiveGeometric k K) :
    isEffectiveGeometric k (((effectiveReducedTorusTensorFunctor k).obj K)⟦n⟧) :=
  ((isEffectiveGeometric k).prop_shift_iff_of_isStableUnderShift
    ((effectiveReducedTorusTensorFunctor k).obj K) n).2
    (isEffectiveGeometric_effectiveReducedTorusTensor k hK)

end AlgebraicGeometry.MotivicHomotopy
