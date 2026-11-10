/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.GenericCoefficientCycle
public import Colib.AlgebraicGeometry.Chow.GenericPushforward
public import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward
public import Colib.AlgebraicGeometry.Correspondences.Graph.Components
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.StalkLengthGenericPoint
public import StacksFrontier.AlgebraicGeometry.Chow.SmoothComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteFibre

/-!
# Genuine fundamental cycles of finite flat support schemes

The coefficient at each generic point is the length of its actual structure
sheaf stalk over itself. Noetherianness proves that every such length is finite.
Finite flat maps send these components onto actual components of the base:
flatness supplies genericity and finiteness removes the closure from the image.
Consequently a finite map into a correspondence ambient scheme with finite flat
first projection gives a native finite correspondence, including nonreduced
support schemes. No product identity or quotient-stalk comparison is assumed.

This file is a source-only construction, not a kernel-checked acceptance record.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable (A : Scheme.{u}) [IsNoetherian A]

/-- All actual generic components of a Noetherian scheme form a finite set. -/
theorem fundamentalCycle_genericPoints_finite : (genericPoints A).Finite :=
  genericPoints.finite finite_irreducibleComponents_of_isNoetherian

/-- No infinite stalk length is truncated in a fundamental coefficient. -/
theorem fundamentalCycle_length_ne_top (a : genericPoints A) :
    Module.length (A.presheaf.stalk a.val) (A.presheaf.stalk a.val) ≠ ⊤ :=
  (Stacks.Chow.length_stalk_ne_top_iff_mem_genericPoints a.val).mpr a.property

/-- The genuine ungraded fundamental cycle in Mathlib's native cycle group. -/
def fundamentalCycle : AlgebraicCycle A ℤ :=
  ofGenericCoefficients (fundamentalCycle_genericPoints_finite A)
    (fun a => (Module.length (A.presheaf.stalk a.val) (A.presheaf.stalk a.val)).toNat)

@[simp] theorem fundamentalCycle_apply_generic (a : genericPoints A) :
    fundamentalCycle A a.val =
      ((Module.length (A.presheaf.stalk a.val) (A.presheaf.stalk a.val)).toNat : ℤ) :=
  ofGenericCoefficients_apply_generic _ _ a

theorem fundamentalCycle_apply_of_notMem (a : A) (ha : a ∉ genericPoints A) :
    fundamentalCycle A a = 0 :=
  ofGenericCoefficients_apply_of_notMem _ _ a ha

theorem support_fundamentalCycle_subset :
    (fundamentalCycle A).support ⊆ genericPoints A :=
  support_ofGenericCoefficients_subset _ _

theorem finite_support_fundamentalCycle : (fundamentalCycle A).support.Finite :=
  finite_support_ofGenericCoefficients _ _

/-- Reduced generic stalks are fields, so their actual multiplicities are one. -/
theorem fundamentalCycle_apply_generic_of_isReduced [IsReduced A]
    (a : genericPoints A) : fundamentalCycle A a.val = 1 := by
  let := (isField_stalk_of_closure_mem_irreducibleComponents A a.val a.property).toField
  rw [fundamentalCycle_apply_generic,
    Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule
      (A.presheaf.stalk a.val) (A.presheaf.stalk a.val))]
  simp

/-- On a reduced scheme this is the sum of all generic components with weight one. -/
theorem fundamentalCycle_eq_ofGenericCoefficients_one [IsReduced A] :
    fundamentalCycle A =
      ofGenericCoefficients (fundamentalCycle_genericPoints_finite A) (fun _ => (1 : ℤ)) := by
  apply Function.locallyFinsuppWithin.ext
  intro a
  by_cases ha : a ∈ genericPoints A
  · rw [fundamentalCycle_apply_generic_of_isReduced A ⟨a, ha⟩,
      ofGenericCoefficients_apply_generic _ _ ⟨a, ha⟩]
  · rw [fundamentalCycle_apply_of_notMem A a ha,
      ofGenericCoefficients_apply_of_notMem _ _ a ha]

end AlgebraicGeometry.AlgebraicCycle

namespace Stacks.Chow

variable {A X Y S : Scheme.{u}}

/-- Every point of a finite scheme over a generic base point is generic. -/
theorem mem_genericPoints_of_isFinite_image (q : A ⟶ X) [IsFinite q]
    (a : A) (ha : q a ∈ genericPoints X) : a ∈ genericPoints A := by
  have hf : q ⁻¹' {q a} ⊆ genericPoints A :=
    ((quasiFiniteAt_over_genericPoint_tfae q (q a) ha).out 2 1).mp
      (fun b hb => quasiFiniteAt_of_finite_preimage q (q a)
        (q.finite_preimage_singleton (q a)) b hb)
  exact hf rfl

/-- For a finite flat map, genericity is exactly genericity of the image. -/
theorem mem_genericPoints_iff_of_finite_flat (q : A ⟶ X) [IsFinite q] [Flat q]
    (a : A) : a ∈ genericPoints A ↔ q a ∈ genericPoints X :=
  ⟨mem_genericPoints_of_flat q, mem_genericPoints_of_isFinite_image q a⟩

/-- Isomorphisms preserve the genuine generic stalk lengths and full fundamental cycle. -/
theorem finiteCyclePushforward_fundamentalCycle_iso [IsNoetherian A] [IsNoetherian X]
    (e : A ≅ X) :
    finiteCyclePushforward e.hom (AlgebraicCycle.fundamentalCycle A) =
      AlgebraicCycle.fundamentalCycle X := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  obtain ⟨a, rfl⟩ := e.hom.surjective x
  rw [finiteCyclePushforward_apply_of_isClosedImmersion]
  by_cases ha : a ∈ genericPoints A
  · have hx := mem_genericPoints_of_flat e.hom ha
    rw [AlgebraicCycle.fundamentalCycle_apply_generic A ⟨a, ha⟩,
      AlgebraicCycle.fundamentalCycle_apply_generic X ⟨e.hom a, hx⟩]
    exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
      (length_stalk_eq_length_stalk_of_smooth e.hom ⟨a, ha⟩).symm
  · have hx : e.hom a ∉ genericPoints X := by
      intro hx
      have h := mem_genericPoints_of_flat e.inv hx
      apply ha
      have he : e.inv (e.hom a) = a :=
        congrArg (fun t : A ⟶ A => t a) e.hom_inv_id
      exact he ▸ h
    rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem A a ha,
      AlgebraicCycle.fundamentalCycle_apply_of_notMem X (e.hom a) hx]

/-- For a reduced source the true graph pushforward is the existing full graph cycle. -/
theorem finiteCyclePushforward_fundamentalCycle_graph
    [IsNoetherian X] [IsReduced X]
    (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) :
    letI := isClosedImmersion_correspondenceGraphMap f g φ hφ
    finiteCyclePushforward (correspondenceGraphMap f g φ hφ)
        (AlgebraicCycle.fundamentalCycle X) =
      (graphCorrespondenceOfComponents f g φ hφ
        (AlgebraicCycle.fundamentalCycle_genericPoints_finite X)).val := by
  classical
  have := isClosedImmersion_correspondenceGraphMap f g φ hφ
  let hX := AlgebraicCycle.fundamentalCycle_genericPoints_finite X
  let := hX.fintype
  rw [AlgebraicCycle.fundamentalCycle_eq_ofGenericCoefficients_one,
    finiteCyclePushforward_ofGenericCoefficients]
  simp only [residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one]
  exact (Finset.sum_subtype hX.toFinset (fun x => hX.mem_toFinset)
    (fun x => single (correspondenceGraphMap f g φ hφ x) (1 : ℤ))).symm

/-- Finiteness and flatness prove the actual component-image condition. -/
theorem finiteFlat_range_integralComponentAt (q : A ⟶ X) [IsFinite q] [Flat q]
    (a : A) (ha : a ∈ genericPoints A) :
    Set.range ((integralComponentAt a).subschemeι ≫ q) ∈ irreducibleComponents X := by
  rw [finiteCyclePushforward_range_integralComponentAt,
    coe_support_integralComponentAt]
  have himage : q.base '' closure ({a} : Set A) = closure ({q a} : Set X) := by
    simpa only [Set.image_singleton] using
      (q.isClosedMap.closure_image_eq_of_continuous q.continuous ({a} : Set A)).symm
  rw [himage]
  exact mem_genericPoints_of_flat q ha

/-- The true fundamental cycle of a finite flat support span is admissible. -/
theorem finiteCyclePushforward_fundamentalCycle_mem_finiteCorrespondences
    [IsNoetherian A] (f : X ⟶ S) (g : Y ⟶ S)
    [IsSeparated g] [LocallyOfFiniteType g]
    (r : A ⟶ pullback f g) [IsFinite r]
    [IsFinite (r ≫ pullback.fst f g)] [Flat (r ≫ pullback.fst f g)] :
    finiteCyclePushforward r (AlgebraicCycle.fundamentalCycle A) ∈
      finiteCorrespondences f g := by
  apply finiteCyclePushforward_mem_finiteCorrespondences f g r _
    (AlgebraicCycle.finite_support_fundamentalCycle A)
  · intro a _
    rw [Category.assoc]
    infer_instance
  · intro a ha
    rw [Category.assoc]
    exact finiteFlat_range_integralComponentAt (r ≫ pullback.fst f g) a
      (AlgebraicCycle.support_fundamentalCycle_subset A ha)

/-- A native finite correspondence from an actual finite flat support span. -/
def finiteFlatSpanFundamental [IsNoetherian A] (f : X ⟶ S) (g : Y ⟶ S)
    [IsSeparated g] [LocallyOfFiniteType g]
    (r : A ⟶ pullback f g) [IsFinite r]
    [IsFinite (r ≫ pullback.fst f g)] [Flat (r ≫ pullback.fst f g)] :
    finiteCorrespondences f g :=
  ⟨finiteCyclePushforward r (AlgebraicCycle.fundamentalCycle A),
    finiteCyclePushforward_fundamentalCycle_mem_finiteCorrespondences f g r⟩

@[simp] theorem finiteFlatSpanFundamental_val [IsNoetherian A]
    (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated g] [LocallyOfFiniteType g]
    (r : A ⟶ pullback f g) [IsFinite r]
    [IsFinite (r ≫ pullback.fst f g)] [Flat (r ≫ pullback.fst f g)] :
    (finiteFlatSpanFundamental f g r).val =
      finiteCyclePushforward r (AlgebraicCycle.fundamentalCycle A) := rfl

end Stacks.Chow
