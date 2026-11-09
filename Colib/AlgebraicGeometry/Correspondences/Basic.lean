/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# Finite correspondences on native algebraic cycles

A finite correspondence from `X` to `Y` over `S` is an integer algebraic cycle on
`X ×[S] Y` with finite support, each of whose integral components is finite and
surjective onto an irreducible component of `X`. The ambient cycles are Mathlib's
`AlgebraicCycle`; the integral closed subscheme attached to a point is Stacks'
`integralComponentAt`. No second cycle presentation is introduced.

The finite-support condition preserves the source definition even for non-quasi-compact
schemes. For a quasi-compact product it follows from the native cycle condition.
The generic-point criterion identifies exactly the actual integral closed subschemes
used by the source, retaining the component condition for disconnected sources.

Source: `kangxyz/motivic` at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Generators/Basic.lean`.
This file constructs the additive groups and their prime cycles, not composition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {S X Y : Scheme.{u}}

/-- A point of the product is admissible when its native integral closed subscheme
is finite and surjective onto an irreducible component of the source. -/
def IsFiniteCorrespondencePoint (f : X ⟶ S) (g : Y ⟶ S) (z : pullback (C := Scheme) f g) : Prop :=
  IsFinite ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ∧
    Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ∈
      irreducibleComponents X

/-- Finite correspondences as a subgroup of the native integer algebraic cycles. -/
@[colib_tag "COL-0350"]
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Generators/Basic.lean"
  "adaptation" "Finite correspondences on native cycles"]
def finiteCorrespondences (f : X ⟶ S) (g : Y ⟶ S) :
    AddSubgroup (AlgebraicCycle (pullback (C := Scheme) f g) ℤ) where
  carrier := {c | c.support.Finite ∧ ∀ z, c z ≠ 0 → IsFiniteCorrespondencePoint f g z}
  zero_mem' := by
    constructor
    · simpa only [Function.locallyFinsuppWithin.support,
        Function.locallyFinsuppWithin.coe_zero, Function.support_zero] using
        (Set.finite_empty : (∅ : Set (pullback (C := Scheme) f g)).Finite)
    · simp
  add_mem' := by
    intro a b ha hb
    refine ⟨(ha.1.union hb.1).subset (Function.support_add a b), ?_⟩
    intro z hz
    by_cases ha' : a z = 0
    · exact hb.2 z (by simpa [ha'] using hz)
    · exact ha.2 z ha'
  neg_mem' := by
    intro a ha
    exact ⟨by simpa using ha.1, fun z hz => ha.2 z (by simpa using hz)⟩

/-- Membership retains both finite support and the geometric component condition. -/
@[simp]
theorem mem_finiteCorrespondences (f : X ⟶ S) (g : Y ⟶ S)
    (c : AlgebraicCycle (pullback (C := Scheme) f g) ℤ) :
    c ∈ finiteCorrespondences f g ↔
      c.support.Finite ∧ ∀ z, c z ≠ 0 → IsFiniteCorrespondencePoint f g z := Iff.rfl

/-- On a quasi-compact product, finite support is already part of the native cycle API. -/
theorem mem_finiteCorrespondences_iff_of_compact (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace (pullback (C := Scheme) f g)]
    (c : AlgebraicCycle (pullback (C := Scheme) f g) ℤ) :
    c ∈ finiteCorrespondences f g ↔
      ∀ z, c z ≠ 0 → IsFiniteCorrespondencePoint f g z :=
  ⟨fun h => h.2, fun h => ⟨c.finite_support, h⟩⟩

/-- The native generic-point description recovers the original integral-subscheme criterion. -/
theorem isFiniteCorrespondencePoint_genericPointOf_iff (f : X ⟶ S) (g : Y ⟶ S)
    (W : (pullback (C := Scheme) f g).IdealSheafData) (hW : IsIntegral W.subscheme) :
    IsFiniteCorrespondencePoint f g (genericPointOf W hW) ↔
      IsFinite (W.subschemeι ≫ pullback.fst f g) ∧
        Set.range (W.subschemeι ≫ pullback.fst f g) ∈ irreducibleComponents X := by
  exact (congrArg (fun V : (pullback (C := Scheme) f g).IdealSheafData =>
    IsFinite (V.subschemeι ≫ pullback.fst f g) ∧
      Set.range (V.subschemeι ≫ pullback.fst f g) ∈ irreducibleComponents X)
    (integralComponentAt_genericPointOf W hW)).to_iff

/-- An admissible point contributes a prime cycle with any integer multiplicity. -/
theorem single_mem_finiteCorrespondences (f : X ⟶ S) (g : Y ⟶ S)
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) (n : ℤ) :
    single z n ∈ finiteCorrespondences f g := by
  classical
  refine ⟨(Set.finite_singleton z).subset ?_, ?_⟩
  · intro w hw
    have h : w = z := by
      by_contra h
      simp [single_apply, h] at hw
    exact Set.mem_singleton_iff.mpr h
  · intro w hw
    have h : w = z := by
      by_contra h
      simp [single_apply, h] at hw
    exact h ▸ hz

/-- The prime correspondence associated to an actual admissible integral closed subscheme. -/
def finiteCorrespondenceOfIntegralClosedSubscheme (f : X ⟶ S) (g : Y ⟶ S)
    (W : (pullback (C := Scheme) f g).IdealSheafData) (hW : IsIntegral W.subscheme)
    (hfin : IsFinite (W.subschemeι ≫ pullback.fst f g))
    (hcomp : Set.range (W.subschemeι ≫ pullback.fst f g) ∈ irreducibleComponents X) :
    finiteCorrespondences f g :=
  ⟨single (genericPointOf W hW) 1,
    single_mem_finiteCorrespondences f g _
      ((isFiniteCorrespondencePoint_genericPointOf_iff f g W hW).mpr ⟨hfin, hcomp⟩) 1⟩

/-- The actual generic point has coefficient one. -/
@[simp]
theorem finiteCorrespondenceOfIntegralClosedSubscheme_apply (f : X ⟶ S) (g : Y ⟶ S)
    (W : (pullback (C := Scheme) f g).IdealSheafData) (hW : IsIntegral W.subscheme)
    (hfin : IsFinite (W.subschemeι ≫ pullback.fst f g))
    (hcomp : Set.range (W.subschemeι ≫ pullback.fst f g) ∈ irreducibleComponents X) :
    (finiteCorrespondenceOfIntegralClosedSubscheme f g W hW hfin hcomp).1
      (genericPointOf W hW) = 1 := by
  classical
  simp [finiteCorrespondenceOfIntegralClosedSubscheme]

/-- Two integral closed subschemes giving the same prime correspondence are equal. -/
theorem finiteCorrespondenceOfIntegralClosedSubscheme_injective (f : X ⟶ S) (g : Y ⟶ S)
    {W V : (pullback (C := Scheme) f g).IdealSheafData} (hW : IsIntegral W.subscheme)
    (hV : IsIntegral V.subscheme)
    (hWfin : IsFinite (W.subschemeι ≫ pullback.fst f g))
    (hVfin : IsFinite (V.subschemeι ≫ pullback.fst f g))
    (hWcomp : Set.range (W.subschemeι ≫ pullback.fst f g) ∈ irreducibleComponents X)
    (hVcomp : Set.range (V.subschemeι ≫ pullback.fst f g) ∈ irreducibleComponents X)
    (h : finiteCorrespondenceOfIntegralClosedSubscheme f g W hW hWfin hWcomp =
      finiteCorrespondenceOfIntegralClosedSubscheme f g V hV hVfin hVcomp) : W = V := by
  classical
  have hpoint : genericPointOf W hW = genericPointOf V hV := by
    by_contra hne
    have he := congrArg (fun c : finiteCorrespondences f g => c.1 (genericPointOf W hW)) h
    simp [finiteCorrespondenceOfIntegralClosedSubscheme, hne] at he
  calc
    W = integralComponentAt (genericPointOf W hW) := (integralComponentAt_genericPointOf W hW).symm
    _ = integralComponentAt (genericPointOf V hV) := congrArg integralComponentAt hpoint
    _ = V := integralComponentAt_genericPointOf V hV

/-- Every finite correspondence is the finite sum of its actual prime cycles. -/
theorem finiteCorrespondence_eq_sum_single (f : X ⟶ S) (g : Y ⟶ S)
    (c : finiteCorrespondences f g) :
    ∑ z ∈ c.2.1.toFinset, single z (c.1 z) = c.1 := by
  classical
  exact sum_apply_smul_single_eq_self_on_univ c.2.1

end Stacks.Chow
