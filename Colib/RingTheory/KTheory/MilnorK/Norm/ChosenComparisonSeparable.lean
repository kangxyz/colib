/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenRecursion
public import Colib.RingTheory.KTheory.MilnorK.Norm.TowerPresentationSeparable
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# The native chosen finite norm in every actual polynomial presentation

Strong induction on the actual extension degree follows the literal selected
witness of the native recursion. Its simple first step is the native minimal
polynomial quotient. Pulling the canonical relative factor back along that
presentation supplies an actual presentation for the strictly smaller remaining
extension. Exact coefficient transport and the unrestricted simple tower close
the induction. The trivial branch uses the actual bijective structure map.

All fields share the universe required by the native chosen norm. The endpoint
assumes separability of the actual finite extension, but neither normality nor a
prime extension degree.
No replacement norm, action, carrier, or presentation-invariance premise occurs.
-/

@[expose] public noncomputable section

open Polynomial Module IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- In the trivial extension branch, the original norms are both the inverse of
an actual structure map. No presentation-independence theorem is used. -/
private theorem milnorKNormRing_eq_simpleMilnorNorm_of_bijective_presentation
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (hb : Function.Bijective (algebraMap k L)) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) := by
  let b : k ≃ₐ[k] L := AlgEquiv.ofBijective (Algebra.ofId k L) hb
  have hdim : finrank k L = 1 := by
    rw [← b.toLinearEquiv.finrank_eq, finrank_self]
  have hd : d = 1 := by
    calc
      d = (poly p).natDegree := (natDegree_eq p).symm
      _ = finrank k (AdjoinRoot (poly p)) := finrank_quotient_span_eq_natDegree.symm
      _ = finrank k L := f.toLinearEquiv.finrank_eq.symm
      _ = 1 := hdim
  subst d
  let g : AdjoinRoot (poly p) ≃ₐ[k] k := f.symm.trans b.symm
  have hchosen := milnorKNormRing_of_bijective hb x
  have hsimple := simpleMilnorNorm_eq_map_of_degree_one p g
    (milnorKRingMap f.toRingHom x)
  have hcomp := milnorKRingMap_comp_apply f.toRingHom g.toRingHom x
  have hg : g.toRingHom.comp f.toRingHom =
      (RingEquiv.ofBijective (algebraMap k L) hb).symm.toRingHom := by
    apply RingHom.ext
    intro z
    change b.symm (f.symm (f z)) = b.symm z
    rw [f.symm_apply_apply]
  have hmaps := congrArg (fun ψ : L →+* k => milnorKRingMap ψ x) hg
  have hsimpleChosen := hsimple.trans (hcomp.trans hmaps)
  exact hchosen.trans hsimpleChosen.symm

/-- For a separable finite extension, the original recursive chosen norm equals the
original simple norm in any supplied actual polynomial presentation. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) := by
  classical
  have main : ∀ n : ℕ, ∀ (K M : Type u) [Field K] [Field M]
      [Algebra K M] [FiniteDimensional K M] [Algebra.IsSeparable K M],
      finrank K M = n → ∀ {d : ℕ} (p : MonicIrreducibleOfDegree K d)
        (f : M ≃ₐ[K] AdjoinRoot (poly p)) (x : MilnorKRing M),
        milnorKNormRing K M x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K M _ _ _ _ _ hn d p f x
      by_cases h : ∃ a : M, a ∉ Set.range (algebraMap K M)
      · let a : M := h.choose
        let : Algebra.IsSeparable K⟮a⟯ M :=
          Algebra.isSeparable_tower_top_of_isSeparable K K⟮a⟯ M
        let hi : IsIntegral K a := Algebra.IsIntegral.isIntegral (R := K) a
        let p₀ := minpolyOfDegree K hi
        let ε := adjoinSimpleEquivQuot K hi
        obtain ⟨rDegree, r, g, hnorm⟩ :=
          exists_simpleMilnorNorm_tower_presentation_of_isSeparable p₀ p ε f
        have hlt : finrank K⟮a⟯ M < n := hn ▸ finrank_adjoin_simple_lt h.choose_spec
        have hremaining : milnorKNormRing K⟮a⟯ M x =
            simpleMilnorNorm r (milnorKRingMap g.toRingHom x) :=
          ih (finrank K⟮a⟯ M) hlt K⟮a⟯ M rfl r g x
        rw [milnorKNormRing_selected_step_apply h]
        change simpleMilnorNorm p₀
            (milnorKRingMap ε.toRingHom (milnorKNormRing K⟮a⟯ M x)) = _
        rw [hremaining]
        exact hnorm x
      · exact milnorKNormRing_eq_simpleMilnorNorm_of_bijective_presentation
          (bijective_algebraMap_of_forall h) p f x
  exact main (finrank k L) k L rfl p f x

/-- Equality of the original additive maps in an actual polynomial presentation. -/
theorem milnorKNormRing_eq_comp_simpleMilnorNorm_of_algEquiv_of_isSeparable
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (f : L ≃ₐ[k] AdjoinRoot (poly p)) :
    milnorKNormRing k L =
      (simpleMilnorNorm p).comp (milnorKRingMap f.toRingHom).toAddMonoidHom := by
  ext x
  exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p f x

/-- In each homogeneous degree, the original chosen norm is the simple norm
of the actual transported class, read in the original whole Milnor ring. -/
theorem coe_milnorKNorm_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d) (f : L ≃ₐ[k] AdjoinRoot (poly p))
    (n : ℕ) (x : MilnorKTheory L n) :
    (milnorKNorm k L n x : MilnorKRing k) =
      simpleMilnorNorm p
        (milnorKTransport f.toRingHom n x : MilnorKRing (AdjoinRoot (poly p))) := by
  rw [milnorKTransport_coe]
  exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p f (x : MilnorKRing L)

/-- The original chosen and simple norms coincide on the native quotient. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_isSeparable
    {k : Type u} [Field k] {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    [FiniteDimensional k (AdjoinRoot (poly p))]
    [Algebra.IsSeparable k (AdjoinRoot (poly p))]
    (x : MilnorKRing (AdjoinRoot (poly p))) :
    milnorKNormRing k (AdjoinRoot (poly p)) x = simpleMilnorNorm p x := by
  have h := milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p
    (AlgEquiv.refl : AdjoinRoot (poly p) ≃ₐ[k] AdjoinRoot (poly p)) x
  change milnorKNormRing k (AdjoinRoot (poly p)) x =
    simpleMilnorNorm p (milnorKRingMap (RingHom.id _) x) at h
  have hid := congrArg (simpleMilnorNorm p) (milnorKRingMap_id_apply x)
  exact h.trans hid

end Stacks.Chow

end
