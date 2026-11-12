/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.GeometricallyIntegralFinitePushforward
public import Colib.AlgebraicGeometry.Chow.GeometricallyIntegralGenericPoints
public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import Colib.AlgebraicGeometry.Correspondences.Exterior.FlatPullbackIdentification
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph

/-!
# Exterior identity of a whole finite support

The exterior of a correspondence presented by a full fundamental cycle
is the pushforward of the full product support. Smoothness preserves
each original generic length. The actual finite base-change formula
retains every residue degree, including collisions in the image.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin

universe u

attribute [local instance] Classical.propDecidable

namespace Stacks.Chow

open AlgebraicCycle

/-- The original generic weights are retained along a smooth geometrically
integral map. -/
theorem fundamentalCycle_eq_sum_geometricallyIntegralPullbackPoint
    {P Q : Scheme.{u}} [IsNoetherian P] [IsNoetherian Q]
    (f : P ⟶ Q) [Smooth f] [GeometricallyIntegral f] :
    letI := (fundamentalCycle_genericPoints_finite Q).fintype
    AlgebraicCycle.fundamentalCycle P = ∑ x : genericPoints Q,
      single (geometricallyIntegralPullbackPoint f x.val)
        ((Module.length (Q.presheaf.stalk x.val) (Q.presheaf.stalk x.val)).toNat : ℤ) := by
  classical
  let : Fintype (genericPoints Q) := (fundamentalCycle_genericPoints_finite Q).fintype
  let : Fintype (genericPoints P) := (fundamentalCycle_genericPoints_finite P).fintype
  let e := geometricallyIntegralGenericPointsEquiv f
  rw [AlgebraicCycle.fundamentalCycle, ofGenericCoefficients_eq_sum]
  refine Fintype.sum_equiv e.symm _ _ ?_
  intro x
  change single x.val
      ((Module.length (P.presheaf.stalk x.val) (P.presheaf.stalk x.val)).toNat : ℤ) =
    single (geometricallyIntegralPullbackPoint f (f x.val))
      ((Module.length (Q.presheaf.stalk (f x.val)) (Q.presheaf.stalk (f x.val))).toNat : ℤ)
  have he : geometricallyIntegralPullbackPoint f (f x.val) = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  rw [he, length_stalk_eq_length_stalk_of_smooth f x]

/-- Extending the actual finite support map by a parameter is finite. -/
theorem isFinite_exteriorParameterSupportMap {P B S T : Scheme.{u}}
    (m : P ⟶ B) (b : B ⟶ S) (t : T ⟶ S) [IsFinite m] :
    IsFinite (pullbackParameterExtensionMap m b t) :=
  MorphismProperty.of_isPullback (P := @IsFinite)
    (pullbackParameterExtension_isPullback m b t).flip (inferInstance : IsFinite m)

/-- The entire extended support is Noetherian by its finite-type projection. -/
theorem isNoetherian_exteriorParameterSupport {P S T : Scheme.{u}} (b : P ⟶ S) (t : T ⟶ S)
    [AlgebraicGeometry.IsNoetherian P] [LocallyOfFiniteType t] [QuasiCompact t] :
    AlgebraicGeometry.IsNoetherian (pullback b t) :=
  let hsq : IsPullback (pullback.snd b t) (pullback.fst b t) t b :=
    (IsPullback.of_hasPullback b t).flip
  letI : LocallyOfFiniteType (pullback.fst b t) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hsq
      (inferInstance : LocallyOfFiniteType t)
  letI : QuasiCompact (pullback.fst b t) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq (inferInstance : QuasiCompact t)
  Scheme.isNoetherian_of_finiteType (pullback.fst b t)

/-- Push forward the full fundamental cycle of the actual parameter product. -/
def nativeExteriorFiniteSupportPushforward {k : Type u} [Field k]
    (X Y T : SmoothSite (Spec (.of k))) {K : Scheme.{u}} [AlgebraicGeometry.IsNoetherian K]
    (m : K ⟶ pullback (C := Scheme) X.hom Y.hom) [IsFinite m] :
    AlgebraicCycle
      (pullback (C := Scheme) (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) ℤ :=
  let b : pullback (C := Scheme) X.hom Y.hom ⟶ Spec (.of k) :=
    pullback.fst X.hom Y.hom ≫ X.hom
  let t : T.left ⟶ Spec (.of k) := T.hom
  let p : pullback (m ≫ b) t ⟶ pullback b t := pullbackParameterExtensionMap m b t
  letI : IsFinite p := isFinite_exteriorParameterSupportMap m b t
  letI : AlgebraicGeometry.IsNoetherian (pullback (m ≫ b) t) :=
    isNoetherian_exteriorParameterSupport (m ≫ b) t
  finiteCyclePushforward (p ≫ exteriorOuterDiagonal X Y T)
    (AlgebraicCycle.fundamentalCycle (pullback (m ≫ b) t))

set_option maxHeartbeats 600000 in
-- The coefficient comparison elaborates the full product support and two finite pushforwards.
/-- The actual exterior identity sends a finite-support fundamental cycle
to the full product support followed by the actual common-parameter
diagonal. -/
theorem nativeExterior_val_eq_fundamentalCycle_of_finite_support {k : Type u} [Field k]
    (X Y T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]
    {K : Scheme.{u}} [AlgebraicGeometry.IsNoetherian K]
    (m : K ⟶ pullback (C := Scheme) X.hom Y.hom) [IsFinite m]
    (α : finiteCorrespondences X.hom Y.hom)
    (_hα : α.val = finiteCyclePushforward m (AlgebraicCycle.fundamentalCycle K))
    (_hm : ∀ x : genericPoints K, IsFiniteCorrespondencePoint X.hom Y.hom (m x.val)) :
    (nativeExterior X Y T α).val = nativeExteriorFiniteSupportPushforward X Y T m := by
  classical
  let C := fieldChowSituation k
  let B := pullback (C := Scheme) X.hom Y.hom
  let sB : B ⟶ Spec (.of k) := pullback.fst X.hom Y.hom ≫ X.hom
  let sK : K ⟶ Spec (.of k) := m ≫ sB
  let πB := pullback.fst sB T.hom
  let K' := pullback (C := Scheme) sK T.hom
  let πK : K' ⟶ K := pullback.fst sK T.hom
  let m' : K' ⟶ pullback sB T.hom := pullbackParameterExtensionMap m sB T.hom
  let δ := exteriorOuterDiagonal X Y T
  let hsq : IsPullback πK m' m πB :=
    (pullbackParameterExtension_isPullback m sB T.hom).flip
  let : IsFinite m' := isFinite_exteriorParameterSupportMap m sB T.hom
  let : AlgebraicGeometry.IsNoetherian K' := isNoetherian_exteriorParameterSupport sK T.hom
  change _ = finiteCyclePushforward (m' ≫ δ) (AlgebraicCycle.fundamentalCycle K')
  let : Fintype (genericPoints K) := (fundamentalCycle_genericPoints_finite K).fintype
  let r := exteriorParameterDimension T
  let hd := relativeDimension_exteriorOuterProjection X Y T
  let c (x : genericPoints K) : ℤ :=
    (Module.length (K.presheaf.stalk x.val) (K.presheaf.stalk x.val)).toNat
  let a (x : genericPoints K) :=
    singleFiniteCorrespondence X.hom Y.hom (m x.val) (_hm x)
      (c x * (m.residueDegree x.val : ℤ))
  have hsum : α = ∑ x : genericPoints K, a x := by
    apply Subtype.ext
    rw [_hα, AlgebraicCycle.fundamentalCycle, finiteCyclePushforward_ofGenericCoefficients]
    change _ = (finiteCorrespondences X.hom Y.hom).subtype (∑ x : genericPoints K, a x)
    rw [map_sum]
    rfl
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian sB
  let target (x : genericPoints K) :=
    single (geometricallyIntegralPullbackPoint πB (m x.val)) (c x * (m.residueDegree x.val : ℤ))
  have hleft : nativeExteriorParameterPullback X Y T α =
      ∑ x : genericPoints K, target x := by
    rw [hsum, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact (nativeExteriorParameterPullback_single X Y T (m x.val) (_hm x) _).trans
      (flatPullback_pointCycleAtOwnDimension C (πB ≫ sB) sB πB rfl r hd (m x.val) _)
  have hright : finiteCyclePushforward m' (AlgebraicCycle.fundamentalCycle K') =
      ∑ x : genericPoints K, target x := by
    rw [fundamentalCycle_eq_sum_geometricallyIntegralPullbackPoint πK, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact finiteCyclePushforward_geometricallyIntegralPullbackPoint C sK sB
      (πK ≫ sK) (πB ≫ sB) m πB πK m' hsq rfl rfl rfl r hd x.val (c x)
  rw [nativeExterior_eq_diagonal_parameterPullback, ← finiteCyclePushforward_comp_apply m' δ,
    hleft, hright]

end Stacks.Chow
