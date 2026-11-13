/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Additive

/-!
# Extensionality on the native finite-correspondence group

The native subgroup is generated additively by its admissible prime cycles.
Its actual finite-support decomposition proves extensionality of additive maps
from their values on these primes, including all signed coefficients. Iterating
this principle gives biadditive and triadditive extensionality.

This replaces `Finsupp.addHom_ext` in `motivic_source_a6805c4`,
`Composition/Incidence/TorAssociativity.lean`, without introducing another cycle
presentation. It supplies the algebraic reduction to generators, not any
geometric unit or associativity theorem.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u v

namespace Stacks.Chow

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- A signed prime is its integer coefficient times the actual coefficient-one prime. -/
theorem singleFiniteCorrespondence_eq_zsmul (z : pullback (C := Scheme) f g)
    (hz : IsFiniteCorrespondencePoint f g z) (n : ℤ) :
    singleFiniteCorrespondence f g z hz n = n • singleFiniteCorrespondence f g z hz 1 := by
  classical
  apply Subtype.ext
  ext x
  change single z n x = n • single z (1 : ℤ) x
  by_cases hx : x = z <;> simp [single_apply, hx]

/-- The finite decomposition into signed primes, inside the native subgroup itself. -/
theorem finiteCorrespondence_eq_sum_signedSingles (c : finiteCorrespondences f g) :
    c = ∑ z : c.property.1.toFinset,
      singleFiniteCorrespondence f g z.val
        (c.property.2 z.val (by
          simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using z.property))
        (c.val z.val) := by
  classical
  apply Subtype.ext
  change c.val = (finiteCorrespondences f g).subtype (∑ z : c.property.1.toFinset,
    singleFiniteCorrespondence f g z.val
      (c.property.2 z.val (by
        simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using z.property))
      (c.val z.val))
  rw [map_sum]
  change c.val = ∑ z : c.property.1.toFinset, single z.val (c.val z.val)
  exact (finiteCorrespondence_eq_sum_single f g c).symm.trans
    (Finset.sum_coe_sort (s := c.property.1.toFinset)
      (f := fun z : pullback (C := Scheme) f g =>
        (single z (c.val z) : AlgebraicCycle (pullback (C := Scheme) f g) ℤ))).symm

namespace finiteCorrespondences

variable {A : Type v} [AddCommGroup A]

/-- Additive maps out of native finite correspondences agree if they agree on signed primes. -/
theorem addHom_ext (F G : finiteCorrespondences f g →+ A)
    (hFG : ∀ (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
      (n : ℤ), F (singleFiniteCorrespondence f g z hz n) =
        G (singleFiniteCorrespondence f g z hz n)) : F = G := by
  apply AddMonoidHom.ext
  intro c
  rw [finiteCorrespondence_eq_sum_signedSingles f g c, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact hFG z.val _ _

/-- Coefficient-one admissible primes already determine an additive map on all signed cycles. -/
theorem addHom_ext_one (F G : finiteCorrespondences f g →+ A)
    (hFG : ∀ (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z),
      F (singleFiniteCorrespondence f g z hz 1) =
        G (singleFiniteCorrespondence f g z hz 1)) : F = G := by
  apply addHom_ext f g F G
  intro z hz n
  rw [singleFiniteCorrespondence_eq_zsmul, map_zsmul, map_zsmul, hFG z hz]

variable {Z W : Scheme.{u}} (h : Z ⟶ S) (i : W ⟶ S)

/-- Two biadditive maps agree on all native cycles if they agree on coefficient-one primes. -/
theorem biaddHom_ext (F G : finiteCorrespondences f g →+ finiteCorrespondences g h →+ A)
    (hFG : ∀ (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
      (w : pullback (C := Scheme) g h) (hw : IsFiniteCorrespondencePoint g h w),
      F (singleFiniteCorrespondence f g z hz 1) (singleFiniteCorrespondence g h w hw 1) =
        G (singleFiniteCorrespondence f g z hz 1) (singleFiniteCorrespondence g h w hw 1)) :
    F = G := by
  apply addHom_ext_one f g
  intro z hz
  apply addHom_ext_one g h
  intro w hw
  exact hFG z hz w hw

/-- Three successive genuine generator comparisons extend to all signed native cycles. -/
theorem triaddHom_ext
    (F G : finiteCorrespondences f g →+ finiteCorrespondences g h →+
      finiteCorrespondences h i →+ A)
    (hFG : ∀ (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
      (w : pullback (C := Scheme) g h) (hw : IsFiniteCorrespondencePoint g h w)
      (t : pullback (C := Scheme) h i) (ht : IsFiniteCorrespondencePoint h i t),
      F (singleFiniteCorrespondence f g z hz 1) (singleFiniteCorrespondence g h w hw 1)
          (singleFiniteCorrespondence h i t ht 1) =
        G (singleFiniteCorrespondence f g z hz 1) (singleFiniteCorrespondence g h w hw 1)
          (singleFiniteCorrespondence h i t ht 1)) : F = G := by
  apply addHom_ext_one f g
  intro z hz
  apply biaddHom_ext g h i
  intro w hw t ht
  exact hFG z hz w hw t ht

end finiteCorrespondences

end Stacks.Chow
