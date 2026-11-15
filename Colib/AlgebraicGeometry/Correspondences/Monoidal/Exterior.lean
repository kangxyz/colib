/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Support
public import Colib.AlgebraicGeometry.Correspondences.Additive
public import Colib.AlgebraicGeometry.Correspondences.Category
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# Exterior products on the native signed finite correspondence groups

On two admissible prime cycles, take the whole fundamental cycle of the
literal product of their original supports and push it along the canonical
closed inclusion into the source-first ambient product. Extend in both
variables by their original integer coefficients. The product support may
have several components and nontrivial generic lengths; all are retained.

This module constructs the actual cycle operation for arbitrary smooth
separated finite-type schemes over a field. Composition interchange and
monoidal coherence are separate obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y U V : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) U.hom V.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint U.hom V.hom w)

include hz hw in
/-- Finiteness over the smooth source product makes the whole support product Noetherian. -/
theorem correspondenceExteriorSupport_isNoetherian :
    IsNoetherian (correspondenceExteriorSupport X Y U V
      (integralComponentAt z) (integralComponentAt w)) := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt w)) := hw.1
  exact Scheme.isNoetherian_of_finiteType_of_isNoetherian
    (correspondenceExteriorSource X Y U V (integralComponentAt z) (integralComponentAt w))

/-- The exterior product of two prime correspondences, with all generic product lengths. -/
def correspondenceExteriorPrime :
    finiteCorrespondences (SmoothSite.product X U).hom (SmoothSite.product Y V).hom := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt w)) := hw.1
  let : UniversallyOpen (exteriorSupportSourceProjection X Y (integralComponentAt z)) :=
    universallyOpen_finiteCorrespondenceProjection_of_smooth X.hom Y.hom z hz
  let : UniversallyOpen (exteriorSupportSourceProjection U V (integralComponentAt w)) :=
    universallyOpen_finiteCorrespondenceProjection_of_smooth U.hom V.hom w hw
  letI := correspondenceExteriorSupport_isNoetherian X Y U V z w hz hw
  let r := correspondenceExteriorInclusion X Y U V (integralComponentAt z) (integralComponentAt w)
  let : IsFinite (r ≫
      pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y V).hom) := by
    dsimp only [r]
    rw [correspondenceExteriorInclusion_fst]
    infer_instance
  let : UniversallyOpen (r ≫
      pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y V).hom) := by
    dsimp only [r]
    rw [correspondenceExteriorInclusion_fst]
    infer_instance
  exact ⟨finiteCyclePushforward r (AlgebraicCycle.fundamentalCycle _),
    finiteCyclePushforward_fundamentalCycle_mem_of_universallyOpen
      (SmoothSite.product X U).hom (SmoothSite.product Y V).hom r⟩

/-- The prime value is the whole product support cycle, before any cancellation. -/
theorem correspondenceExteriorPrime_val :
    letI : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
    letI : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt w)) := hw.1
    letI := correspondenceExteriorSupport_isNoetherian X Y U V z w hz hw
    (correspondenceExteriorPrime X Y U V z w hz hw).val =
      finiteCyclePushforward
        (correspondenceExteriorInclusion X Y U V (integralComponentAt z) (integralComponentAt w))
        (AlgebraicCycle.fundamentalCycle
          (correspondenceExteriorSupport X Y U V
            (integralComponentAt z) (integralComponentAt w))) :=
  rfl

/-- The product cycle has the exact local length at every generic point of the support product. -/
theorem correspondenceExteriorPrime_apply_generic
    (a : genericPoints (correspondenceExteriorSupport X Y U V
      (integralComponentAt z) (integralComponentAt w))) :
    (correspondenceExteriorPrime X Y U V z w hz hw).val
      (correspondenceExteriorInclusion X Y U V (integralComponentAt z)
        (integralComponentAt w) a.val) =
      ((Module.length
        ((correspondenceExteriorSupport X Y U V (integralComponentAt z)
          (integralComponentAt w)).presheaf.stalk a.val)
        ((correspondenceExteriorSupport X Y U V (integralComponentAt z)
          (integralComponentAt w)).presheaf.stalk a.val)).toNat : ℤ) := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt w)) := hw.1
  let := correspondenceExteriorSupport_isNoetherian X Y U V z w hz hw
  rw [correspondenceExteriorPrime_val,
    finiteCyclePushforward_apply_of_isClosedImmersion,
    AlgebraicCycle.fundamentalCycle_apply_generic]

include hz hw in
/-- Each displayed generic product length is finite, so `toNat` loses no information. -/
theorem correspondenceExteriorPrime_length_ne_top
    (a : genericPoints (correspondenceExteriorSupport X Y U V
      (integralComponentAt z) (integralComponentAt w))) :
    Module.length
      ((correspondenceExteriorSupport X Y U V (integralComponentAt z)
        (integralComponentAt w)).presheaf.stalk a.val)
      ((correspondenceExteriorSupport X Y U V (integralComponentAt z)
        (integralComponentAt w)).presheaf.stalk a.val) ≠ ⊤ := by
  let := correspondenceExteriorSupport_isNoetherian X Y U V z w hz hw
  exact AlgebraicCycle.fundamentalCycle_length_ne_top _ a

omit z w hz hw in
/-- Bilinear exterior product on the existing native signed cycle subgroups. -/
def correspondenceExterior : finiteCorrespondences X.hom Y.hom →+
    finiteCorrespondences U.hom V.hom →+
      finiteCorrespondences (SmoothSite.product X U).hom (SmoothSite.product Y V).hom :=
  liftFiniteCorrespondence X.hom Y.hom fun z hz =>
    liftFiniteCorrespondence U.hom V.hom fun w hw =>
      correspondenceExteriorPrime X Y U V z w hz hw

/-- Both original integer coefficients multiply the whole product cycle. -/
theorem correspondenceExterior_single (n m : ℤ) :
    correspondenceExterior X Y U V
      (singleFiniteCorrespondence X.hom Y.hom z hz n)
      (singleFiniteCorrespondence U.hom V.hom w hw m) =
        (n * m) • correspondenceExteriorPrime X Y U V z w hz hw := by
  simp [correspondenceExterior, smul_smul]

end Stacks.Chow

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- The tensor object is the ordinary smooth-site product, without another scheme model. -/
def tensorObj (X U : Cor k) : Cor k :=
  Cor.mk (SmoothSite.product X.toSmoothSite U.toSmoothSite)

/-- The actual exterior operation on morphisms of the existing correspondence category. -/
def exteriorProduct {X Y U V : Cor k} : (X ⟶ Y) →+ (U ⟶ V) →+
    (tensorObj X U ⟶ tensorObj Y V) :=
  Stacks.Chow.correspondenceExterior X.toSmoothSite Y.toSmoothSite U.toSmoothSite V.toSmoothSite

theorem exteriorProduct_add_left {X Y U V : Cor k}
    (α α' : X ⟶ Y) (β : U ⟶ V) :
    exteriorProduct (α + α') β = exteriorProduct α β + exteriorProduct α' β :=
  congrArg (fun F => F β) (map_add exteriorProduct α α')

@[simp] theorem exteriorProduct_add_right {X Y U V : Cor k}
    (α : X ⟶ Y) (β β' : U ⟶ V) :
    exteriorProduct α (β + β') = exteriorProduct α β + exteriorProduct α β' :=
  map_add (exteriorProduct α) β β'

theorem exteriorProduct_zero_left {X Y U V : Cor k} (β : U ⟶ V) :
    exteriorProduct (0 : X ⟶ Y) β = 0 :=
  congrArg (fun F : (U ⟶ V) →+ (tensorObj X U ⟶ tensorObj Y V) => F β)
    (map_zero exteriorProduct)

@[simp] theorem exteriorProduct_zero_right {X Y U V : Cor k} (α : X ⟶ Y) :
    exteriorProduct α (0 : U ⟶ V) = 0 :=
  map_zero (exteriorProduct α)

theorem exteriorProduct_neg_left {X Y U V : Cor k}
    (α : X ⟶ Y) (β : U ⟶ V) :
    exteriorProduct (-α) β = -exteriorProduct α β :=
  congrArg (fun F => F β) (map_neg exteriorProduct α)

@[simp] theorem exteriorProduct_neg_right {X Y U V : Cor k}
    (α : X ⟶ Y) (β : U ⟶ V) :
    exteriorProduct α (-β) = -exteriorProduct α β :=
  map_neg (exteriorProduct α) β

end AlgebraicGeometry.Cor
