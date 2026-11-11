/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionStalkLength
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Products of actual finite flat closed support cycles

At a point over a generic base point, a closed support finite over the base
has an Artinian generic stalk. Its actual ambient quotient length is therefore
finite, without any global dimension bound on the ambient scheme. Away from
generic base points, flatness forces all fundamental-cycle coefficients to
vanish. A literal local product of defining equations now gives equality in
the native algebraic-cycle group through the multiplication exact sequence.

The local hypotheses are equations of actual kernel ideal stalks, not a
postulated cycle identity or multiplicity identity. This source is unchecked.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {D E F C X : Scheme.{u}}

/-- The actual ambient quotient by the defining kernel ideal stalk, before truncation. -/
def closedImmersionQuotientStalkLength (i : D ⟶ C) (x : C) : ℕ∞ :=
  Module.length (C.presheaf.stalk x)
    (C.presheaf.stalk x ⧸ IdealSheafData.stalk i.ker x)

/-- On the closed image, the quotient has exactly the full self-length of the source stalk. -/
theorem closedImmersionQuotientStalkLength_image (i : D ⟶ C)
    [IsClosedImmersion i] (d : D) :
    closedImmersionQuotientStalkLength i (i d) =
      Module.length (D.presheaf.stalk d) (D.presheaf.stalk d) := by
  obtain ⟨U, hU, hd, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (i d))
  exact (length_stalk_self_eq_length_quotient_stalk_ker i d U hU hd).symm

/-- Outside the actual closed image the defining ideal is the unit ideal. -/
theorem closedImmersionQuotientStalkLength_eq_zero_of_notMem_range
    (i : D ⟶ C) [IsClosedImmersion i] (x : C) (hx : x ∉ Set.range i) :
    closedImmersionQuotientStalkLength i x = 0 := by
  have hs : x ∉ i.ker.support := by
    change x ∉ (i.ker.support : Set C)
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
    exact hx
  unfold closedImmersionQuotientStalkLength
  rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support i.ker x).mpr hs]
  exact Module.length_eq_zero

/-- A finite support over a generic base point has finite actual quotient length. -/
theorem closedImmersionQuotientStalkLength_ne_top [IsNoetherian D]
    (p : C ⟶ X) (i : D ⟶ C) [IsClosedImmersion i] [IsFinite (i ≫ p)]
    (x : C) (hx : p x ∈ genericPoints X) :
    closedImmersionQuotientStalkLength i x ≠ ⊤ := by
  by_cases hi : x ∈ Set.range i
  · obtain ⟨d, rfl⟩ := hi
    rw [closedImmersionQuotientStalkLength_image]
    exact AlgebraicCycle.fundamentalCycle_length_ne_top D
      ⟨d, mem_genericPoints_of_isFinite_image (i ≫ p) d hx⟩
  · rw [closedImmersionQuotientStalkLength_eq_zero_of_notMem_range i x hi]
    exact ENat.zero_ne_top

/-- Pushforward has coefficient zero away from the actual image. -/
theorem finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range
    [IsNoetherian D] (i : D ⟶ C) [IsFinite i] (x : C)
    (hx : x ∉ Set.range i) :
    finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle D) x = 0 := by
  by_contra h
  obtain ⟨d, _, hd⟩ := finiteCyclePushforward_support_subset i
    (AlgebraicCycle.fundamentalCycle D) h
  exact hx ⟨d, hd⟩

/-- Over a generic base point, the coefficient is the true finite ambient quotient length. -/
theorem finiteCyclePushforward_fundamentalCycle_apply_eq_quotientStalkLength
    [IsNoetherian D] (p : C ⟶ X) (i : D ⟶ C)
    [IsClosedImmersion i] [IsFinite (i ≫ p)]
    (x : C) (hx : p x ∈ genericPoints X) :
    finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle D) x =
      ((closedImmersionQuotientStalkLength i x).toNat : ℤ) := by
  by_cases hi : x ∈ Set.range i
  · obtain ⟨d, rfl⟩ := hi
    rw [finiteCyclePushforward_apply_of_isClosedImmersion,
      closedImmersionQuotientStalkLength_image]
    exact AlgebraicCycle.fundamentalCycle_apply_generic D
      ⟨d, mem_genericPoints_of_isFinite_image (i ≫ p) d hx⟩
  · rw [finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range i x hi,
      closedImmersionQuotientStalkLength_eq_zero_of_notMem_range i x hi]
    simp

/-- Flatness excludes every non-generic-base point from the pushed fundamental support. -/
theorem finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_genericPoints
    [IsNoetherian D] (p : C ⟶ X) (i : D ⟶ C) [IsFinite i] [Flat (i ≫ p)]
    (x : C) (hx : p x ∉ genericPoints X) :
    finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle D) x = 0 := by
  by_contra h
  obtain ⟨d, hd, rfl⟩ := finiteCyclePushforward_support_subset i
    (AlgebraicCycle.fundamentalCycle D) h
  exact hx (mem_genericPoints_of_flat (i ≫ p)
    (AlgebraicCycle.support_fundamentalCycle_subset D hd))

/-- A local product of actual defining ideals gives the genuine cycle product law. -/
theorem finiteCyclePushforward_fundamentalCycle_mul_of_stalk_ker
    [IsNoetherian D] [IsNoetherian E] [IsNoetherian F]
    (p : C ⟶ X) (i : D ⟶ C) (j : E ⟶ C) (l : F ⟶ C)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion l]
    [IsFinite (i ≫ p)] [IsFinite (j ≫ p)] [IsFinite (l ≫ p)]
    [Flat (i ≫ p)] [Flat (j ≫ p)] [Flat (l ≫ p)]
    (hlocal : ∀ x : C, p x ∈ genericPoints X →
      ∃ a b : C.presheaf.stalk x,
        IdealSheafData.stalk i.ker x = Ideal.span {a} ∧
        IdealSheafData.stalk j.ker x = Ideal.span {b} ∧
        IdealSheafData.stalk l.ker x = Ideal.span {a * b} ∧
        b ∈ nonZeroDivisors (C.presheaf.stalk x)) :
    finiteCyclePushforward l (AlgebraicCycle.fundamentalCycle F) =
      finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle D) +
        finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle E) := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  change finiteCyclePushforward l (AlgebraicCycle.fundamentalCycle F) x =
    finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle D) x +
      finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle E) x
  by_cases hx : p x ∈ genericPoints X
  · rw [finiteCyclePushforward_fundamentalCycle_apply_eq_quotientStalkLength p l x hx,
      finiteCyclePushforward_fundamentalCycle_apply_eq_quotientStalkLength p i x hx,
      finiteCyclePushforward_fundamentalCycle_apply_eq_quotientStalkLength p j x hx]
    obtain ⟨a, b, hi, hj, hl, hb⟩ := hlocal x hx
    have hlen : closedImmersionQuotientStalkLength l x =
        closedImmersionQuotientStalkLength i x +
          closedImmersionQuotientStalkLength j x := by
      unfold closedImmersionQuotientStalkLength
      rw [hi, hj, hl]
      exact Ring.ord_mul (C.presheaf.stalk x) hb
    rw [hlen, ENat.toNat_add (closedImmersionQuotientStalkLength_ne_top p i x hx)
      (closedImmersionQuotientStalkLength_ne_top p j x hx)]
    exact Nat.cast_add _ _
  · rw [finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_genericPoints p l x hx,
      finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_genericPoints p i x hx,
      finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_genericPoints p j x hx]
    simp

end Stacks.Chow
