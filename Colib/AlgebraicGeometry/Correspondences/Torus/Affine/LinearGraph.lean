/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialSpan
public import Colib.AlgebraicGeometry.Correspondences.Graph.Components
public import Colib.AlgebraicGeometry.Sites.Smooth.Torus
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Linear polynomial spans are the actual native unit graphs

This is the scheme-map part of the original `LinearGraph` comparison, now on
the native Stacks base-change torus. The quotient source is isomorphic to the
original source. Its actual ambient map factors through that isomorphism and
the original unit graph. For `X - 1`, the target is the existing `torusOne`,
which is also the unit insertion in the canonical recursive first power.

The graph cycles below are the existing native signed integer cycles. No
claim identifying them with a general polynomial fundamental-cycle producer
is made here; that producer and its multiplicity theorem remain separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Polynomial TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R]

/-- The linear polynomial for a specified unit has invertible constant coefficient. -/
theorem linear_constant_isUnit (v : Rˣ) : IsUnit ((Polynomial.X - C (v : R)).coeff 0) := by
  simp

/-- The structural map of the actual linear quotient is an isomorphism. -/
instance projection_linear_isIso (v : Rˣ) : IsIso (projection (Polynomial.X - C (v : R))) := by
  have he : CommRingCat.ofHom (AdjoinRoot.of (Polynomial.X - C (v : R))) =
      (quotientSpanXSubCAlgEquiv (v : R)).toRingEquiv.toCommRingCatIso.inv := by
    ext r
    exact (quotientSpanXSubCAlgEquiv_symm_apply (v : R) r).symm
  unfold projection
  rw [he]
  exact inferInstanceAs (IsIso (Scheme.Spec.mapIso
    (quotientSpanXSubCAlgEquiv (v : R)).toRingEquiv.toCommRingCatIso.symm.op).hom)

/-- In the linear quotient the forward root unit is the image of the specified unit. -/
theorem rootUnit_linear (v : Rˣ) :
    AdjoinRoot.rootUnit (Polynomial.X - C (v : R)) (linear_constant_isUnit v) =
      Units.map (AdjoinRoot.of (Polynomial.X - C (v : R))).toMonoidHom v := by
  apply Units.ext
  rw [AdjoinRoot.rootUnit_val]
  change AdjoinRoot.root (Polynomial.X - C (v : R)) =
    AdjoinRoot.of (Polynomial.X - C (v : R)) (v : R)
  have h := AdjoinRoot.eval₂_root (Polynomial.X - C (v : R))
  simpa only [eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero] using h

/-- The literal linear quotient maps to the native unit point, with no coordinate twist. -/
@[reassoc] theorem torusPoint_linear (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    (torusPoint f (Polynomial.X - C (v : R)) (linear_constant_isUnit v)).left =
      projection (Polynomial.X - C (v : R)) ≫ (nativeAffineTorusPoint f v).left := by
  unfold torusPoint
  rw [rootUnit_linear]
  exact nativeAffineTorusPoint_natural f (AdjoinRoot.of (Polynomial.X - C (v : R))) v

/-- The original affine unit point is over the original base. -/
@[reassoc] theorem affineUnitPoint_over
    (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    (nativeAffineTorusPoint f v).left ≫ (multiplicativeGroupBaseChange S ↘ S) = f :=
  Over.w _

/-- The actual source-first graph, not a replacement ambient polynomial model. -/
def unitGraphMap (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    Spec (.of R) ⟶ pullback f (multiplicativeGroupBaseChange S ↘ S) :=
  Stacks.Chow.correspondenceGraphMap f (multiplicativeGroupBaseChange S ↘ S)
    (nativeAffineTorusPoint f v).left (affineUnitPoint_over f v)

/-- The actual linear span is its source isomorphism followed by the genuine graph. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Torus/Affine/LinearGraph.lean:59-88,103-108"
  "adaptation" "Actual linear quotient and graph maps in the native Stacks torus model"]
theorem inclusion_linear (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    inclusion f (Polynomial.X - C (v : R)) (linear_constant_isUnit v) =
      projection (Polynomial.X - C (v : R)) ≫ unitGraphMap f v := by
  apply pullback.hom_ext
  · simp [unitGraphMap]
  · simp [unitGraphMap, torusPoint_linear]

/-- The unit-one affine point is precisely the already chosen native identity section. -/
theorem affineUnitPoint_one (f : Spec (.of R) ⟶ S) :
    (nativeAffineTorusPoint f 1).left = f ≫ (Scheme.SmoothSite.torusOne S).left := by
  change (nativeTorusPoint f (specGlobalUnit 1)).left =
    f ≫ (nativeTorusPoint (𝟙 S) 1).left
  simpa only [specGlobalUnit, map_one] using nativeTorusPoint_one f

/-- The linear equation `X - 1` gives the literal identity section on its quotient source. -/
@[reassoc] theorem torusPoint_linear_one (f : Spec (.of R) ⟶ S) :
    (torusPoint f (Polynomial.X - C (1 : R)) (linear_constant_isUnit (1 : Rˣ))).left =
      projection (Polynomial.X - C (1 : R)) ≫ f ≫ (Scheme.SmoothSite.torusOne S).left := by
  exact (torusPoint_linear f (1 : Rˣ)).trans
    (congrArg (fun g => projection (Polynomial.X - C (1 : R)) ≫ g)
      (affineUnitPoint_one f))

/-- The same unit-one point is retained by the canonical recursive first torus power. -/
theorem affineUnitPoint_one_recursive (f : Spec (.of R) ⟶ S) :
    (nativeAffineTorusPoint f 1).left = f ≫
      (Scheme.SmoothSite.torusInsertOne S 0 0).left ≫
      (Scheme.SmoothSite.torusPowerOneIso S).hom.left := by
  have h : (Scheme.SmoothSite.torusInsertOne S 0 0).left ≫
      (Scheme.SmoothSite.torusPowerOneIso S).hom.left = (Scheme.SmoothSite.torusOne S).left :=
    congrArg (fun h => h.left) (Scheme.SmoothSite.torusInsertOne_zero_powerOneIso S)
  rw [h]
  exact affineUnitPoint_one f

/-- The genuine native integer graph cycle of the specified unit point. -/
def unitGraphCycle (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    Stacks.Chow.finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) := by
  letI : IsSeparated (multiplicativeGroupBaseChange S ↘ S) := by
    change IsSeparated (pullback.snd
      (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S))
    infer_instance
  exact Stacks.Chow.graphCorrespondenceOfComponents f (multiplicativeGroupBaseChange S ↘ S)
    (nativeAffineTorusPoint f v).left (affineUnitPoint_over f v) hR

/-- The actual unit graph has its native component points with coefficient one. -/
theorem unitGraphCycle_coe (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    (unitGraphCycle f v hR).1 = ∑ t ∈ hR.toFinset, single (unitGraphMap f v t) 1 := rfl

/-- The literal linear quotient reaches exactly the same native graph support points. -/
theorem inclusion_linear_apply (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (x : Spec (.of (AdjoinRoot (Polynomial.X - C (v : R))))) :
    inclusion f (Polynomial.X - C (v : R)) (linear_constant_isUnit v) x =
      unitGraphMap f v (projection (Polynomial.X - C (v : R)) x) := by
  rw [inclusion_linear]
  rfl

/-- Arbitrary signed multiples retain the native component-cycle sum. -/
theorem zsmul_unitGraphCycle_coe (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) (n : ℤ) :
    (n • unitGraphCycle f v hR).1 =
      n • ∑ t ∈ hR.toFinset, single (unitGraphMap f v t) 1 := rfl

end AlgebraicGeometry.NativeTorusPolynomial
