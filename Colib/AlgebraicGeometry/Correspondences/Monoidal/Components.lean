/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Exterior

/-!
# Actual generic components in an exterior product

The product of two prime supports need not be integral. This module exposes
its entire finite set of generic points, proves their image admissibility,
and expands the product correspondence into those native primes with their
actual local lengths. These are the labels consumed by the incidence Tor
pairing; no choice of a single product component is made.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y U V : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) U.hom V.hom)

local notation "D" => correspondenceExteriorSupport X Y U V
  (integralComponentAt z) (integralComponentAt w)
local notation "r" => correspondenceExteriorInclusion X Y U V
  (integralComponentAt z) (integralComponentAt w)
local notation "q" => correspondenceExteriorSource X Y U V
  (integralComponentAt z) (integralComponentAt w)

/-- A generic component of the literal product, viewed in the correspondence ambient. -/
abbrev correspondenceExteriorComponentPoint (a : genericPoints D) := r a.val

/-- The actual generic multiplicity of the product support. -/
def correspondenceExteriorComponentWeight (a : genericPoints D) : ℤ :=
  (Module.length ((D).presheaf.stalk a.val) ((D).presheaf.stalk a.val)).toNat

variable (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint U.hom V.hom w)

include hz hw in
/-- Every generic product component is admissible, independently of its cycle coefficient. -/
theorem correspondenceExteriorComponentPoint_admissible (a : genericPoints D) :
    IsFiniteCorrespondencePoint (SmoothSite.product X U).hom (SmoothSite.product Y V).hom
      (correspondenceExteriorComponentPoint X Y U V z w a) := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt w)) := hw.1
  let : UniversallyOpen (exteriorSupportSourceProjection X Y (integralComponentAt z)) :=
    universallyOpen_finiteCorrespondenceProjection_of_smooth X.hom Y.hom z hz
  let : UniversallyOpen (exteriorSupportSourceProjection U V (integralComponentAt w)) :=
    universallyOpen_finiteCorrespondenceProjection_of_smooth U.hom V.hom w hw
  refine ⟨finiteCyclePushforward_isFinite_integralComponentAt r
    (pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y V).hom) a.val ?_, ?_⟩
  · rw [Category.assoc, correspondenceExteriorInclusion_fst]
    infer_instance
  · rw [finiteCyclePushforward_range_integralComponentAt]
    apply finiteCyclePushforward_image_mem_irreducibleComponents r
      (pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y V).hom) a.val
    rw [correspondenceExteriorInclusion_fst,
      ← finiteCyclePushforward_range_integralComponentAt]
    exact finiteUniversallyOpen_range_integralComponentAt q a.val a.property

/-- The product prime expands over all actual generic components with their whole local lengths. -/
theorem correspondenceExteriorPrime_eq_sum_single :
    letI := correspondenceExteriorSupport_isNoetherian X Y U V z w hz hw
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
    correspondenceExteriorPrime X Y U V z w hz hw =
      ∑ a : genericPoints D,
        singleFiniteCorrespondence (SmoothSite.product X U).hom (SmoothSite.product Y V).hom
          (correspondenceExteriorComponentPoint X Y U V z w a)
          (correspondenceExteriorComponentPoint_admissible X Y U V z w hz hw a)
          (correspondenceExteriorComponentWeight X Y U V z w a) := by
  classical
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt w)) := hw.1
  let := correspondenceExteriorSupport_isNoetherian X Y U V z w hz hw
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
  apply Subtype.ext
  rw [correspondenceExteriorPrime_val]
  change finiteCyclePushforward r (AlgebraicCycle.fundamentalCycle D) =
    (finiteCorrespondences (SmoothSite.product X U).hom (SmoothSite.product Y V).hom).subtype
      (∑ a : genericPoints D,
        singleFiniteCorrespondence (SmoothSite.product X U).hom (SmoothSite.product Y V).hom
          (correspondenceExteriorComponentPoint X Y U V z w a)
          (correspondenceExteriorComponentPoint_admissible X Y U V z w hz hw a)
          (correspondenceExteriorComponentWeight X Y U V z w a))
  rw [AlgebraicCycle.fundamentalCycle, finiteCyclePushforward_ofGenericCoefficients, map_sum]
  simp only [residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one]
  rfl

end Stacks.Chow
