/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentation
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Equivariance of actual polynomial field presentations

Transport the presentation through the given commuting field equivalences.
The polynomial is its actual coefficient image; the original scalar actions
are unchanged. The quotient square is proved without any norm assumption.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

/-- Transport an actual polynomial presentation across a commuting pair of field
isomorphisms, preserving the supplied algebra actions and the exact quotient square. -/
theorem exists_monicIrreducible_presentation_ringEquiv
    {k k' L L' : Type u} [Field k] [Field k'] [Field L] [Field L']
    [Algebra k L] [Algebra k' L']
    (σ : k ≃+* k') (τ : L ≃+* L')
    (hστ : τ.toRingHom.comp (algebraMap k L) =
      (algebraMap k' L').comp σ.toRingHom)
    {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] AdjoinRoot (poly p)) :
    ∃ (q : MonicIrreducibleOfDegree k' d)
      (g : L' ≃ₐ[k'] AdjoinRoot (poly q))
      (hq : poly q = (poly p).map σ.toRingHom),
      (AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl)).comp
        f.toRingHom = g.toRingHom.comp τ.toRingHom := by
  let q : MonicIrreducibleOfDegree k' d :=
    ⟨(poly p).map σ.toRingHom, (monic p).map _, by
      change Irreducible (Polynomial.mapEquiv σ (poly p))
      rw [MulEquiv.irreducible_iff]
      exact irreducible p, by
      rw [Polynomial.natDegree_map, natDegree_eq]⟩
  have hq : poly q = (poly p).map σ.toRingHom := rfl
  let c : AdjoinRoot (poly p) ≃+* AdjoinRoot (poly q) :=
    AdjoinRoot.mapRingEquiv σ (poly p) (poly q)
      (by change Associated ((poly p).map σ.toRingHom) (poly q); rw [← hq])
  have hc : c.toRingHom =
      AdjoinRoot.map σ.toRingHom (poly p) (poly q) (hq ▸ dvd_rfl) := rfl
  have hτ : ∀ a : k', τ.symm (algebraMap k' L' a) = algebraMap k L (σ.symm a) := by
    intro a
    apply τ.injective
    rw [τ.apply_symm_apply]
    have h := congrArg (fun ψ : k →+* L' => ψ (σ.symm a)) hστ
    change τ (algebraMap k L (σ.symm a)) = algebraMap k' L' (σ (σ.symm a)) at h
    simpa only [σ.apply_symm_apply] using h.symm
  let v : L' ≃+* AdjoinRoot (poly q) := (τ.symm.trans f.toRingEquiv).trans c
  have hv : ∀ a : k', v (algebraMap k' L' a) =
      algebraMap k' (AdjoinRoot (poly q)) a := by
    intro a
    change c (f (τ.symm (algebraMap k' L' a))) = _
    rw [hτ, f.commutes]
    change c.toRingHom (AdjoinRoot.of (poly p) (σ.symm a)) = _
    rw [hc, AdjoinRoot.map_of]
    change AdjoinRoot.of (poly q) (σ (σ.symm a)) = AdjoinRoot.of (poly q) a
    exact congrArg (AdjoinRoot.of (poly q)) (σ.apply_symm_apply a)
  let g : L' ≃ₐ[k'] AdjoinRoot (poly q) := { v with commutes' := hv }
  refine ⟨q, g, hq, ?_⟩
  rw [← hc]
  apply RingHom.ext
  intro z
  change c (f z) = c (f (τ.symm (τ z)))
  rw [τ.symm_apply_apply]

end Stacks.Chow

end
