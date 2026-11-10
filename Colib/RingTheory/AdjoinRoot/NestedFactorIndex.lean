/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.NestedScalarFactorQuotient
public import Colib.RingTheory.AdjoinRoot.TowerFactorOfRootEquiv

/-!
# The complete native nested scalar-factor index

The forward native factor construction and reverse actual-quotient theorem
identify the full dependent lower/relative factor index with the original top
scalar factors. Uniqueness gives both inverse identities on the literal indices.
This module also selects the actual quotient algebra equivalence. Explicit
selected root and map identities belong to the importing upper module.
No norm or multiplicity law is asserted.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

attribute [local instance] instFactIrreduciblePolynomialPoly_colib

private theorem nestedFactorIndex_sigma_poly_injective {F : Type*} [Field F] :
    Function.Injective (fun r : Σ d : ℕ, MonicIrreducibleOfDegree F d => poly r.2) := by
  intro r s h
  obtain ⟨d, r⟩ := r
  obtain ⟨e, s⟩ := s
  change poly r = poly s at h
  obtain rfl : d = e := by rw [← natDegree_eq r, h, natDegree_eq s]
  obtain rfl := poly_injective h
  rfl

/-- Form both literal choices before specializing the carriers and relation. -/
public def nestedFactorIndexEquivOfRelation
    {α β : Type*} (R : α → β → Prop)
    (he : ∀ a, ∃ b, R a b)
    (hur : ∀ a, ∃! b, R a b)
    (hul : ∀ b, ∃! a, R a b) : α ≃ β where
  toFun a := (he a).choose
  invFun b := (hul b).exists.choose
  left_inv a :=
    (hul (he a).choose).unique
      (hul (he a).choose).exists.choose_spec (he a).choose_spec
  right_inv b :=
    (hur (hul b).exists.choose).unique
      (he (hul b).exists.choose).choose_spec (hul b).exists.choose_spec

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K)
  (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "q" => towerFactor p h f
local notation "Q" => AdjoinRoot (poly (Sigma.snd (Subtype.val q)))
local notation "Lower" =>
  {r : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly (Sigma.snd r) ∣ Polynomial.map φ p}
local notation "Top" =>
  {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly (Sigma.snd s) ∣ Polynomial.map φ h}
local notation "Rel" r =>
  {t : Σ d : ℕ,
      MonicIrreducibleOfDegree (AdjoinRoot (poly (Sigma.snd (Subtype.val r)))) d //
    poly (Sigma.snd t) ∣ Polynomial.map
      (AdjoinRoot.map φ p (poly (Sigma.snd (Subtype.val r))) (Subtype.property r))
      (poly (Sigma.snd (Subtype.val q)))}
local notation "Pairs" => Σ r : Lower, Rel r

/-- Existence in the forward direction, now expressed on the literal dependent
pair and with the native scalar-tower `K`-algebra on its actual upper quotient. -/
theorem exists_nestedScalarFactor_pair_quotientAlgEquiv (s : Top) :
    ∃ z : Pairs, ∃ ε : AdjoinRoot (poly z.2.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2),
      ε (root (poly z.2.1.2)) = root (poly s.1.2) := by
  have hlower := existsUnique_lowerScalarFactor_algHom φ p h f s
  obtain ⟨r, ⟨i, hi⟩, _⟩ := hlower
  let R := AdjoinRoot (poly r.1.2)
  let S := AdjoinRoot (poly s.1.2)
  let j : E →+* R := AdjoinRoot.map φ p (poly r.1.2) r.2
  let jh : H →+* S := AdjoinRoot.map φ h (poly s.1.2) s.2
  let g : Q →+* S := jh.comp (towerFactorRingEquiv p h f).toRingHom
  have hc : g.comp (of (poly q.1.2)) = i.toRingHom.comp j := by
    apply RingHom.ext
    intro a
    change jh (towerFactorRingEquiv p h f (of (poly q.1.2) a)) = i (j a)
    have he : towerFactorRingEquiv p h f (of (poly q.1.2) a) = f a :=
      towerFactorRingEquiv_algebraMap p h f a
    rw [he]
    exact (RingHom.congr_fun hi a).symm
  have hgroot : g (root (poly q.1.2)) = root (poly s.1.2) := by
    change jh (towerFactorRingEquiv p h f (root (poly q.1.2))) = root (poly s.1.2)
    rw [towerFactorRingEquiv_root]
    exact AdjoinRoot.map_root φ h (poly s.1.2) s.2
  have hz : ((poly q.1.2).map j).eval₂ i.toRingHom (root (poly s.1.2)) = 0 := by
    rw [Polynomial.eval₂_map, ← hc, ← hgroot, ← Polynomial.hom_eval₂,
      AdjoinRoot.eval₂_root, map_zero]
  let u := towerFactor (poly r.1.2) (poly s.1.2) i
  let θ := towerFactorRingEquiv (poly r.1.2) (poly s.1.2) i
  let hRS : Algebra R S := i.toRingHom.toAlgebra
  let eU : AdjoinRoot (poly u.1.2) →ₐ[R] S :=
    { θ.toRingHom with
      commutes' := fun a =>
        towerFactorRingEquiv_algebraMap (poly r.1.2) (poly s.1.2) i a }
  have hu : aeval (root (poly s.1.2)) (poly u.1.2) = 0 := by
    have hzero := AdjoinRoot.aeval_algHom_eq_zero (poly u.1.2) eU
    have hroot : eU (root (poly u.1.2)) = root (poly s.1.2) :=
      towerFactorRingEquiv_root (poly r.1.2) (poly s.1.2) i
    rw [hroot] at hzero
    exact hzero
  have humin : poly u.1.2 = minpoly R (root (poly s.1.2)) :=
    minpoly.eq_of_irreducible_of_monic (irreducible u.1.2) hu (monic u.1.2)
  have hdiv : poly u.1.2 ∣ (poly q.1.2).map j := by
    rw [humin]
    exact minpoly.dvd R (root (poly s.1.2)) hz
  let t : Rel r := ⟨u.1, hdiv⟩
  let ε : AdjoinRoot (poly t.1.2) ≃ₐ[K] S :=
    towerFactorAlgEquiv (poly r.1.2) (poly s.1.2) i
  refine ⟨⟨r, t⟩, ε, ?_⟩
  exact towerFactorRingEquiv_root (poly r.1.2) (poly s.1.2) i


/-- The original lower factor is determined before comparing dependent relative factors. -/
private theorem nestedScalarFactor_pair_lower_eq
    (s : Top) (r₁ r₂ : Lower) (t₁ : Rel r₁) (t₂ : Rel r₂)
    (ε₁ : AdjoinRoot (poly t₁.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2))
    (ε₂ : AdjoinRoot (poly t₂.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2))
    (h₁ : ε₁ (root (poly t₁.1.2)) = root (poly s.1.2))
    (h₂ : ε₂ (root (poly t₂.1.2)) = root (poly s.1.2)) :
    r₁ = r₂ := by
  let i₁ : AdjoinRoot (poly r₁.1.2) →ₐ[K] AdjoinRoot (poly s.1.2) :=
    ε₁.toAlgHom.comp (ofAlgHom K (poly t₁.1.2))
  let i₂ : AdjoinRoot (poly r₂.1.2) →ₐ[K] AdjoinRoot (poly s.1.2) :=
    ε₂.toAlgHom.comp (ofAlgHom K (poly t₂.1.2))
  have hi₁ : i₁.toRingHom.comp (AdjoinRoot.map φ p (poly r₁.1.2) r₁.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom :=
    (nestedScalarFactor_quotientEquiv_squares φ p h f r₁ t₁ s ε₁ h₁).2.1
  have hi₂ : i₂.toRingHom.comp (AdjoinRoot.map φ p (poly r₂.1.2) r₂.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom :=
    (nestedScalarFactor_quotientEquiv_squares φ p h f r₂ t₂ s ε₂ h₂).2.1
  exact (existsUnique_lowerScalarFactor_algHom φ p h f s).unique
    ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩

/-- Relative factors are unique over one fixed actual lower quotient. -/
private theorem nestedScalarFactor_relative_unique
    (s : Top) (r : Lower) (t₁ t₂ : Rel r)
    (ε₁ : AdjoinRoot (poly t₁.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2))
    (ε₂ : AdjoinRoot (poly t₂.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2))
    (h₁ : ε₁ (root (poly t₁.1.2)) = root (poly s.1.2))
    (h₂ : ε₂ (root (poly t₂.1.2)) = root (poly s.1.2)) :
    t₁ = t₂ := by
  let i₁ : AdjoinRoot (poly r.1.2) →ₐ[K] AdjoinRoot (poly s.1.2) :=
    ε₁.toAlgHom.comp (ofAlgHom K (poly t₁.1.2))
  let i₂ : AdjoinRoot (poly r.1.2) →ₐ[K] AdjoinRoot (poly s.1.2) :=
    ε₂.toAlgHom.comp (ofAlgHom K (poly t₂.1.2))
  have hi₁ : i₁.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom :=
    (nestedScalarFactor_quotientEquiv_squares φ p h f r t₁ s ε₁ h₁).2.1
  have hi₂ : i₂.toRingHom.comp (AdjoinRoot.map φ p (poly r.1.2) r.2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom :=
    (nestedScalarFactor_quotientEquiv_squares φ p h f r t₂ s ε₂ h₂).2.1
  have hi : i₁ = i₂ := lowerScalarFactor_algHom_ext φ p h f s r i₁ i₂ hi₁ hi₂
  have hpoly₁ := rootEquiv_poly_eq_towerFactor
    (poly r.1.2) (poly s.1.2) t₁.1.2 ε₁ h₁
  have hpoly₂ := rootEquiv_poly_eq_towerFactor
    (poly r.1.2) (poly s.1.2) t₂.1.2 ε₂ h₂
  have hcanonical := congrArg
    (fun j : AdjoinRoot (poly r.1.2) →ₐ[K] AdjoinRoot (poly s.1.2) =>
      poly (towerFactor (poly r.1.2) (poly s.1.2) j).1.2) hi
  have hpoly := hpoly₁.trans (hcanonical.trans hpoly₂.symm)
  apply Subtype.ext
  apply nestedFactorIndex_sigma_poly_injective
  exact hpoly

/-- Eliminate the lower equality before introducing any dependent upper data. -/
private theorem nestedScalarFactor_pair_eq_of_lower_eq
    (s : Top) (r₁ r₂ : Lower) (hr : r₁ = r₂) :
    ∀ (t₁ : Rel r₁) (t₂ : Rel r₂)
      (ε₁ : AdjoinRoot (poly t₁.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2))
      (ε₂ : AdjoinRoot (poly t₂.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2)),
      ε₁ (root (poly t₁.1.2)) = root (poly s.1.2) →
      ε₂ (root (poly t₂.1.2)) = root (poly s.1.2) →
      (⟨r₁, t₁⟩ : Pairs) = (⟨r₂, t₂⟩ : Pairs) := by
  cases hr
  intro t₁ t₂ ε₁ ε₂ h₁ h₂
  exact congrArg (fun t : Rel r₁ => (⟨r₁, t⟩ : Pairs))
    (nestedScalarFactor_relative_unique φ p h f s r₁
      t₁ t₂ ε₁ ε₂ h₁ h₂)

/-- The same original top factor cannot come from two different literal pairs.
The lower equality includes its degree index; after it is substituted, the upper
minimal-polynomial equality includes its own dependent degree index. -/
theorem nestedScalarFactor_pair_unique (s : Top) (z₁ z₂ : Pairs)
    (ε₁ : AdjoinRoot (poly z₁.2.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2))
    (ε₂ : AdjoinRoot (poly z₂.2.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2))
    (h₁ : ε₁ (root (poly z₁.2.1.2)) = root (poly s.1.2))
    (h₂ : ε₂ (root (poly z₂.2.1.2)) = root (poly s.1.2)) : z₁ = z₂ := by
  obtain ⟨r₁, t₁⟩ := z₁
  obtain ⟨r₂, t₂⟩ := z₂
  have hr : r₁ = r₂ :=
    nestedScalarFactor_pair_lower_eq φ p h f s
      r₁ r₂ t₁ t₂ ε₁ ε₂ h₁ h₂
  exact nestedScalarFactor_pair_eq_of_lower_eq φ p h f s
    r₁ r₂ hr t₁ t₂ ε₁ ε₂ h₁ h₂

/-- Forward existence and uniqueness for the entire dependent index. -/
theorem existsUnique_nestedScalarFactor_pair_quotientAlgEquiv (s : Top) :
    ∃! z : Pairs, ∃ ε : AdjoinRoot (poly z.2.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2),
      ε (root (poly z.2.1.2)) = root (poly s.1.2) := by
  refine existsUnique_of_exists_of_unique
    (exists_nestedScalarFactor_pair_quotientAlgEquiv φ p h f s) ?_
  intro z₁ z₂ hz₁ hz₂
  refine hz₁.elim fun ε₁ hε₁ => ?_
  refine hz₂.elim fun ε₂ hε₂ => ?_
  exact nestedScalarFactor_pair_unique φ p h f s z₁ z₂ ε₁ ε₂ hε₁ hε₂

/-- The complete equivalence between original top scalar factors and literal
lower/relative scalar-factor pairs. No selected subset is used on either side. -/
def nestedScalarFactorIndexEquiv : Top ≃ Pairs :=
  nestedFactorIndexEquivOfRelation
    (fun (s : Top) (z : Pairs) =>
      ∃ ε : AdjoinRoot (poly z.2.1.2) ≃ₐ[K] AdjoinRoot (poly s.1.2),
        ε (root (poly z.2.1.2)) = root (poly s.1.2))
    (fun s => exists_nestedScalarFactor_pair_quotientAlgEquiv φ p h f s)
    (fun s => existsUnique_nestedScalarFactor_pair_quotientAlgEquiv φ p h f s)
    (fun z => existsUnique_topScalarFactor_quotientEquiv φ p h f z.1 z.2)

/-- The complete-index forward/inverse identity, not only equality of polynomials. -/
theorem nestedScalarFactorIndexEquiv_symm_apply_apply (s : Top) :
    (nestedScalarFactorIndexEquiv φ p h f).symm
      (nestedScalarFactorIndexEquiv φ p h f s) = s :=
  (nestedScalarFactorIndexEquiv φ p h f).symm_apply_apply s

/-- Every literal pair is recovered by the other inverse identity. -/
theorem nestedScalarFactorIndexEquiv_apply_symm_apply (z : Pairs) :
    nestedScalarFactorIndexEquiv φ p h f
      ((nestedScalarFactorIndexEquiv φ p h f).symm z) = z :=
  (nestedScalarFactorIndexEquiv φ p h f).apply_symm_apply z

/-- The actual quotient equivalence attached to the complete native bijection. -/
def nestedScalarFactorQuotientEquiv (s : Top) :
    AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).2.1.2) ≃ₐ[K]
      AdjoinRoot (poly s.1.2) :=
  (exists_nestedScalarFactor_pair_quotientAlgEquiv φ p h f s).choose_spec.choose

end AdjoinRoot

end
