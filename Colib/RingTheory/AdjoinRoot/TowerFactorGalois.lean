/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactor
public import Mathlib.FieldTheory.Normal.Basic

/-!
# Galois enumeration of all split constant-cover branches

An embedding of the constant root field into the original residue field selects
one native factor. Precomposing it by the actual constant Galois automorphisms
runs through every native factor once. The quotient comparisons are the existing
`towerFactorRingEquiv` and their coefficient maps are the original automorphisms.
The closed point need not be separable. No localized branch is declared finite.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h

/-- The actual quotient comparison between a conjugate branch and the chosen branch. -/
def towerFactorCompGalRingEquiv (σ : Gal(E/k)) :
    AdjoinRoot (poly (towerFactor p h (f.comp σ.toAlgHom)).1.2) ≃+*
      AdjoinRoot (poly (towerFactor p h f).1.2) :=
  (towerFactorRingEquiv p h (f.comp σ.toAlgHom)).trans
    (towerFactorRingEquiv p h f).symm

/-- The conjugate quotient comparison has the original coefficient automorphism. -/
theorem towerFactorCompGalRingEquiv_algebraMap (σ : Gal(E/k)) (a : E) :
    towerFactorCompGalRingEquiv p h f σ (algebraMap E _ a) =
      algebraMap E _ (σ a) := by
  apply (towerFactorRingEquiv p h f).injective
  change towerFactorRingEquiv p h f
      ((towerFactorRingEquiv p h f).symm
        (towerFactorRingEquiv p h (f.comp σ.toAlgHom) (algebraMap E _ a))) = _
  rw [RingEquiv.apply_symm_apply, towerFactorRingEquiv_algebraMap,
    towerFactorRingEquiv_algebraMap]
  rfl

/-- The conjugate quotient comparison retains the actual polynomial root. -/
theorem towerFactorCompGalRingEquiv_root (σ : Gal(E/k)) :
    towerFactorCompGalRingEquiv p h f σ
        (root (poly (towerFactor p h (f.comp σ.toAlgHom)).1.2)) =
      root (poly (towerFactor p h f).1.2) := by
  apply (towerFactorRingEquiv p h f).injective
  change towerFactorRingEquiv p h f
      ((towerFactorRingEquiv p h f).symm
        (towerFactorRingEquiv p h (f.comp σ.toAlgHom) (root _))) = _
  rw [RingEquiv.apply_symm_apply, towerFactorRingEquiv_root, towerFactorRingEquiv_root]

/-- The literal conjugate native polynomial maps to the literal chosen polynomial. -/
theorem towerFactor_compGal_poly_map (σ : Gal(E/k)) :
    (poly (towerFactor p h (f.comp σ.toAlgHom)).1.2).map σ.toRingHom =
      poly (towerFactor p h f).1.2 := by
  let q := towerFactor p h (f.comp σ.toAlgHom)
  let q₀ := towerFactor p h f
  let e := towerFactorCompGalRingEquiv p h f σ
  have hc : e.toRingHom.comp (of (poly q.1.2)) =
      (of (poly q₀.1.2)).comp σ.toRingHom := by
    apply RingHom.ext
    intro a
    exact towerFactorCompGalRingEquiv_algebraMap p h f σ a
  have he := Polynomial.hom_eval₂ (p := poly q.1.2) (f := of (poly q.1.2))
    (g := e.toRingHom) (x := root (poly q.1.2))
  have hroot : e.toRingHom (root (poly q.1.2)) = root (poly q₀.1.2) :=
    towerFactorCompGalRingEquiv_root p h f σ
  rw [AdjoinRoot.eval₂_root, map_zero, hc, hroot] at he
  have hdiv : poly q₀.1.2 ∣ (poly q.1.2).map σ.toRingHom := by
    apply (AdjoinRoot.mk_eq_zero (f := poly q₀.1.2)).mp
    rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
    change ((poly q.1.2).map σ.toRingHom).eval₂ (of (poly q₀.1.2))
      (root (poly q₀.1.2)) = 0
    rw [Polynomial.eval₂_map]
    exact he.symm
  have hi : Irreducible ((poly q.1.2).map σ.toRingHom) :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv σ.toRingEquiv)).mpr
      (irreducible q.1.2)
  exact (Polynomial.eq_of_monic_of_associated (monic q₀.1.2)
    ((monic q.1.2).map σ.toRingHom)
    ((irreducible q₀.1.2).associated_of_dvd hi hdiv)).symm

/-- The quotient comparison is exactly the existing coefficient-factor map. -/
theorem towerFactorCompGalRingEquiv_toRingHom (σ : Gal(E/k)) :
    (towerFactorCompGalRingEquiv p h f σ).toRingHom =
      AdjoinRoot.map σ.toRingHom
        (poly (towerFactor p h (f.comp σ.toAlgHom)).1.2)
        (poly (towerFactor p h f).1.2) (by rw [towerFactor_compGal_poly_map]) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, RingHom.comp_apply, AdjoinRoot.map_of]
    exact towerFactorCompGalRingEquiv_algebraMap p h f σ a
  · rw [AdjoinRoot.map_root]
    exact towerFactorCompGalRingEquiv_root p h f σ

/-- Normality identifies every embedding with exactly one precomposition of a fixed one. -/
theorem comp_gal_bijective [Normal k E] :
    Function.Bijective (fun σ : Gal(E/k) => f.comp σ.toAlgHom) := by
  refine ⟨?_, ?_⟩
  · intro σ τ hστ
    apply AlgEquiv.ext
    intro a
    exact f.injective (DFunLike.congr_fun hστ a)
  · intro g
    let : Algebra E H := f.toRingHom.toAlgebra
    let : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    refine ⟨g.restrictNormal' E, ?_⟩
    apply AlgHom.ext
    intro a
    change algebraMap E H (g.restrictNormal E a) = g a
    simpa only [Algebra.algebraMap_self_apply] using g.restrictNormal_commutes E a

/-- Distinct embeddings select distinct actual upper factors. -/
theorem towerFactor_injective : Function.Injective (towerFactor p h) := by
  intro f g hfg
  apply AdjoinRoot.algHom_ext
  have hpoly : X - C (f (root p)) = X - C (g (root p)) := by
    rw [← towerFactor_matched_poly, ← towerFactor_matched_poly, hfg]
  have hz := congrArg (fun a : H[X] => a.coeff 0) hpoly
  simpa only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_inj] using hz

private theorem towerFactorGalois_sigma_poly_injective {F : Type*} [Field F] :
    Function.Injective (fun q : Σ d : ℕ, MonicIrreducibleOfDegree F d => poly q.2) := by
  rintro ⟨d, q⟩ ⟨e, r⟩ hqr
  change poly q = poly r at hqr
  have hde : d = e := by rw [← natDegree_eq q, hqr, natDegree_eq r]
  subst e
  obtain rfl := poly_injective hqr
  rfl

/-- Every upper factor is selected by an embedding when the opposite constant
polynomial splits. This enumerates all branches, including at inseparable h. -/
theorem towerFactor_surjective_of_splits
    (hsplit : (p.map (algebraMap k H)).Splits) :
    Function.Surjective (towerFactor p h) := by
  intro q
  let r := tensorSwapFactorIndexEquiv p h q
  have hs : (poly r.1.2).Splits :=
    hsplit.of_dvd (Polynomial.map_ne_zero (Fact.out : Irreducible p).ne_zero) r.2
  have hd : (poly r.1.2).natDegree = 1 :=
    hs.natDegree_eq_one_of_irreducible (irreducible r.1.2)
  let b : H := -(poly r.1.2).coeff 0
  have hr : poly r.1.2 = X - C b := by
    simpa only [b, map_neg, sub_neg_eq_add] using (monic r.1.2).eq_X_add_C hd
  have hb : p.eval₂ (algebraMap k H) b = 0 := by
    have hdiv : X - C b ∣ p.map (algebraMap k H) := hr ▸ r.2
    simpa only [IsRoot, eval_map] using dvd_iff_isRoot.mp hdiv
  let g : E →ₐ[k] H := AdjoinRoot.liftAlgHom p (Algebra.ofId k H) b hb
  refine ⟨g, ?_⟩
  apply (tensorSwapFactorIndexEquiv p h).injective
  apply Subtype.ext
  apply towerFactorGalois_sigma_poly_injective
  change poly (tensorSwapFactorIndexEquiv p h (towerFactor p h g)).1.2 = poly r.1.2
  rw [towerFactor_matched_poly]
  rw [show g (root p) = b from AdjoinRoot.liftAlgHom_root _ _ _ _, hr]

include f in
/-- A single embedding into the residue field splits the normal constant polynomial. -/
theorem splits_map_of_normal_embedding (hp : p.Monic) [Normal k E] :
    (p.map (algebraMap k H)).Splits := by
  have hs := Normal.splits (inferInstance : Normal k E) (root p)
  rw [minpoly_root (Fact.out : Irreducible p).ne_zero, hp.leadingCoeff,
    inv_one, C_1, mul_one] at hs
  have ht := hs.map f.toRingHom
  have hf : f.toRingHom.comp (algebraMap k E) = algebraMap k H := by
    apply RingHom.ext
    intro a
    exact f.commutes a
  simpa only [Polynomial.map_map, hf] using ht

/-- Precomposition by the original Galois group enumerates every native factor
exactly once. No residue-degree, norm, or branch-coverage hypothesis is supplied. -/
theorem towerFactor_comp_gal_bijective (hp : p.Monic) [Normal k E] :
    Function.Bijective (fun σ : Gal(E/k) => towerFactor p h (f.comp σ.toAlgHom)) := by
  have ht : Function.Bijective (towerFactor p h) :=
    ⟨towerFactor_injective p h,
      towerFactor_surjective_of_splits p h (splits_map_of_normal_embedding p h f hp)⟩
  exact ht.comp (comp_gal_bijective p h f)

end AdjoinRoot
