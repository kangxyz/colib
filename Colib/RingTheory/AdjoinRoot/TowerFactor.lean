/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TensorFactorMaps
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The native tensor factor selected by an actual field embedding

The image of the original root gives a literal linear factor on the opposite side
of the complete tensor factor bijection. Its inverse image has its actual quotient
identified with the original top field. Both original field maps are retained.
Degree multiplication uses the existing scalar tower on that quotient, not an
assumed action of the lower field on the top field. No norm law is asserted.

This is the native algebraic input to the tower route in
`Aglib/KTheory/MilnorK/Norm/Polynomial/PrimeTower.lean` at revision
`52e09db47998f139064acf48a2d3a64494d0dd9a`; no Aglib branch model is imported.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h

/-- The image of the original root determines a literal opposite linear factor. -/
theorem towerFactor_linear_dvd :
    X - C (f (root p)) ∣ p.map (algebraMap k H) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_map]
  exact AdjoinRoot.aeval_algHom_eq_zero p f

/-- Select the existing native factor whose opposite factor is the image-root line. -/
def towerFactor :
    {q : Σ d : ℕ, MonicIrreducibleOfDegree E d // poly q.2 ∣ h.map (algebraMap k E)} :=
  (tensorSwapFactorIndexEquiv p h).symm
    ⟨⟨1, ⟨X - C (f (root p)), monic_X_sub_C _, irreducible_X_sub_C _,
      natDegree_X_sub_C _⟩⟩, towerFactor_linear_dvd p h f⟩

local notation "q" => towerFactor p h f
local notation "r" => tensorSwapFactorIndexEquiv p h q
local notation "Q" => AdjoinRoot (poly q.1.2)

/-- The matched polynomial is exactly the image-root line, not just an associate. -/
theorem towerFactor_matched_poly : poly r.1.2 = X - C (f (root p)) := by
  let s : {s : Σ d : ℕ, MonicIrreducibleOfDegree H d //
      poly s.2 ∣ p.map (algebraMap k H)} :=
    ⟨⟨1, ⟨X - C (f (root p)), monic_X_sub_C _, irreducible_X_sub_C _,
      natDegree_X_sub_C _⟩⟩, towerFactor_linear_dvd p h f⟩
  have hs : r = s := (tensorSwapFactorIndexEquiv p h).apply_symm_apply s
  exact congrArg (fun t : {t : Σ d : ℕ, MonicIrreducibleOfDegree H d //
    poly t.2 ∣ p.map (algebraMap k H)} => poly t.1.2) hs

/-- The actual opposite factor of the selected native factor has degree one. -/
theorem towerFactor_matched_natDegree : (poly r.1.2).natDegree = 1 := by
  rw [towerFactor_matched_poly, natDegree_X_sub_C]

/-- Identify the actual opposite quotient with the original top field by evaluation. -/
def towerFactorTargetEquiv : AdjoinRoot (poly r.1.2) ≃ₐ[H] H :=
  (algEquivOfEq H _ _ (towerFactor_matched_poly p h f)).trans
    (quotientSpanXSubCAlgEquiv (f (root p)))

/-- The actual tensor quotient comparison followed by the literal linear evaluation. -/
def towerFactorRingEquiv : Q ≃+* H :=
  (tensorSwapFactorQuotientEquiv p h q).trans (towerFactorTargetEquiv p h f).toRingEquiv

/-- The original top-field coefficient-factor map is inverted on every element. -/
theorem towerFactorRingEquiv_map (b : H) :
    towerFactorRingEquiv p h f
      (AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 b) = b := by
  change towerFactorTargetEquiv p h f
    (tensorSwapFactorQuotientEquiv p h q
      (AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 b)) = b
  rw [tensorSwapFactorQuotientEquiv_map]
  exact (towerFactorTargetEquiv p h f).commutes b

/-- The inverse is the original coefficient-factor map, with its actual divisibility. -/
theorem towerFactorRingEquiv_symm_toRingHom :
    (towerFactorRingEquiv p h f).symm.toRingHom =
      AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 := by
  apply RingHom.ext
  intro b
  apply (towerFactorRingEquiv p h f).injective
  exact ((towerFactorRingEquiv p h f).apply_symm_apply b).trans
    (towerFactorRingEquiv_map p h f b).symm

/-- The selected quotient root becomes the original top-field root. -/
theorem towerFactorRingEquiv_root :
    towerFactorRingEquiv p h f (root (poly q.1.2)) = root h := by
  simpa only [AdjoinRoot.map_root] using towerFactorRingEquiv_map p h f (root h)

/-- The lower-field coefficients become precisely their images under the given embedding. -/
theorem towerFactorRingEquiv_algebraMap (a : E) :
    towerFactorRingEquiv p h f (algebraMap E Q a) = f a := by
  have hc : (towerFactorTargetEquiv p h f).toRingHom.comp
      (AdjoinRoot.map (algebraMap k H) p (poly r.1.2) r.2) = f.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro c
      change towerFactorTargetEquiv p h f
        (AdjoinRoot.map (algebraMap k H) p (poly r.1.2) r.2 (of p c)) = f (of p c)
      rw [AdjoinRoot.map_of]
      exact ((towerFactorTargetEquiv p h f).commutes (algebraMap k H c)).trans
        (f.commutes c).symm
    · change towerFactorTargetEquiv p h f
        (AdjoinRoot.map (algebraMap k H) p (poly r.1.2) r.2 (root p)) = f (root p)
      rw [AdjoinRoot.map_root]
      have he : algEquivOfEq H (poly r.1.2) (X - C (f (root p)))
          (towerFactor_matched_poly p h f) (root (poly r.1.2)) =
          root (X - C (f (root p))) :=
        algEquivOfEq_root (R := H) (poly r.1.2) (X - C (f (root p)))
          (towerFactor_matched_poly p h f)
      exact (congrArg (fun x : AdjoinRoot (X - C (f (root p))) =>
          quotientSpanXSubCAlgEquiv (f (root p)) x) he).trans
        ((quotientSpanXSubCAlgEquiv_mk (f (root p)) (X : H[X])).trans eval_X)
  change towerFactorTargetEquiv p h f
    (tensorSwapFactorQuotientEquiv p h q (algebraMap E Q a)) = f a
  rw [tensorSwapFactorQuotientEquiv_algebraMap]
  exact RingHom.congr_fun hc a

/-- The constructed quotient identification respects the original base field. -/
def towerFactorAlgEquiv : Q ≃ₐ[k] H :=
  { towerFactorRingEquiv p h f with
    commutes' := fun c => by
      change towerFactorRingEquiv p h f (algebraMap k Q c) = algebraMap k H c
      exact (congrArg (towerFactorRingEquiv p h f)
        (IsScalarTower.algebraMap_apply k E Q c)).trans
          ((towerFactorRingEquiv_algebraMap p h f (algebraMap k E c)).trans
            (f.commutes c)) }

/-- The native scalar tower gives the actual factor degree, without new tower instances. -/
theorem towerFactor_natDegree_mul_natDegree :
    (poly q.1.2).natDegree * p.natDegree = h.natDegree := by
  have hq : Module.finrank E Q = (poly q.1.2).natDegree :=
    (AdjoinRoot.powerBasis (ne_zero q.1.2)).finrank
  have hp : Module.finrank k E = p.natDegree :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible p).ne_zero).finrank
  have hh : Module.finrank k H = h.natDegree :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank
  calc
    (poly q.1.2).natDegree * p.natDegree =
        Module.finrank E Q * Module.finrank k E := congrArg₂ (· * ·) hq.symm hp.symm
    _ = Module.finrank k Q :=
      (Nat.mul_comm _ _).trans (Module.finrank_mul_finrank k E Q)
    _ = h.natDegree := (towerFactorAlgEquiv p h f).toLinearEquiv.finrank_eq.trans hh

/-- A nontrivial original lower degree forces a strict drop in the actual upper factor. -/
theorem towerFactor_natDegree_lt (hp : 1 < p.natDegree) :
    (poly q.1.2).natDegree < h.natDegree := by
  rw [← towerFactor_natDegree_mul_natDegree p h f]
  simpa only [mul_one] using
    Nat.mul_lt_mul_of_pos_left hp (irreducible q.1.2).natDegree_pos

end AdjoinRoot
