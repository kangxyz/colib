/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactorEmbedding

/-!
# Associativity of the actual relative tower-factor presentation

For original embeddings `A → E → H`, let `PA` and `HA` be the native selected
quotients presenting `E` and `H` over `A`. Applying `towerFactor` to their actual
`A`-algebra embedding gives a quotient over `PA`. Its actual quotient ring is
identified with the direct selected quotient over `E`, through their original
maps to `H`.

The comparison preserves the coefficient square over the actual equivalence
`PA ≃+* E`, the original root, the relative coefficient-factor map and the
composite coefficient-factor map from the original `H`. The relative factor
polynomial, transported along `PA ≃+* E`, is exactly the direct monic factor.
Consequently the comparison is also the literal native `AdjoinRoot.map` with
that coefficient equivalence and its proved factor divisibility.

Only the existing quotient algebras and their scalar towers are used. The local
instances below supply the proved irreducibility of their defining polynomials;
they neither replace scalar structures nor introduce a new field presentation.
No norm is defined or norm law assumed.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

variable {k : Type*} [Field k] (a p h : k[X])
  [Fact (Irreducible a)] [Fact (Irreducible p)] [Fact (Irreducible h)]
  (g : AdjoinRoot a →ₐ[k] AdjoinRoot p)
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "A" => AdjoinRoot a
local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "qP" => towerFactor a p g
local notation "qH" => towerFactor a h (f.comp g)
local notation "pA" => poly qP.1.2
local notation "hA" => poly qH.1.2
local notation "PA" => AdjoinRoot pA
local notation "HA" => AdjoinRoot hA

local instance : Fact (Irreducible pA) := ⟨irreducible qP.1.2⟩
local instance : Fact (Irreducible hA) := ⟨irreducible qH.1.2⟩

local notation "fA" => towerFactorEmbeddingAlgHom a p h g f
local notation "qR" => towerFactor pA hA fA
local notation "qD" => towerFactor p h f
local notation "QR" => AdjoinRoot (poly qR.1.2)
local notation "QD" => AdjoinRoot (poly qD.1.2)

/-- Compare the iterated relative quotient and direct quotient through the original top field. -/
def towerFactorAssocRingEquiv : QR ≃+* QD :=
  ((towerFactorRingEquiv pA hA fA).trans
    (towerFactorRingEquiv a h (f.comp g))).trans (towerFactorRingEquiv p h f).symm

/-- The comparison is compatible with the original top field on every element. -/
theorem towerFactorAssocRingEquiv_apply (x : QR) :
    towerFactorRingEquiv p h f (towerFactorAssocRingEquiv a p h g f x) =
      towerFactorRingEquiv a h (f.comp g) (towerFactorRingEquiv pA hA fA x) := by
  change towerFactorRingEquiv p h f
      ((towerFactorRingEquiv p h f).symm
        (towerFactorRingEquiv a h (f.comp g) (towerFactorRingEquiv pA hA fA x))) =
    towerFactorRingEquiv a h (f.comp g) (towerFactorRingEquiv pA hA fA x)
  exact RingEquiv.apply_symm_apply _ _

/-- Associativity preserves the actual map to the original top field, as a ring-hom square. -/
theorem towerFactorAssocRingEquiv_comp_towerFactorRingEquiv :
    (towerFactorRingEquiv p h f).toRingHom.comp
        (towerFactorAssocRingEquiv a p h g f).toRingHom =
      (towerFactorRingEquiv a h (f.comp g)).toRingHom.comp
        (towerFactorRingEquiv pA hA fA).toRingHom := by
  apply RingHom.ext
  intro x
  exact towerFactorAssocRingEquiv_apply a p h g f x

/-- The relative lower coefficients become the direct coefficients under the actual `PA ≃ E`. -/
theorem towerFactorAssocRingEquiv_algebraMap (x : PA) :
    towerFactorAssocRingEquiv a p h g f (algebraMap PA QR x) =
      algebraMap E QD (towerFactorRingEquiv a p g x) := by
  apply (towerFactorRingEquiv p h f).injective
  rw [towerFactorAssocRingEquiv_apply, towerFactorRingEquiv_algebraMap,
    towerFactorEmbeddingAlgHom_apply, towerFactorRingEquiv_algebraMap]

/-- The coefficient square uses the actual coefficient-field equivalence, not a new action. -/
theorem towerFactorAssocRingEquiv_comp_algebraMap :
    (towerFactorAssocRingEquiv a p h g f).toRingHom.comp (algebraMap PA QR) =
      (algebraMap E QD).comp (towerFactorRingEquiv a p g).toRingHom := by
  apply RingHom.ext
  intro x
  exact towerFactorAssocRingEquiv_algebraMap a p h g f x

/-- The comparison also respects the original base field through the existing scalar towers. -/
def towerFactorAssocAlgEquiv : QR ≃ₐ[k] QD :=
  { towerFactorAssocRingEquiv a p h g f with
    commutes' := fun c => by
      change towerFactorAssocRingEquiv a p h g f (algebraMap k QR c) = algebraMap k QD c
      calc
        towerFactorAssocRingEquiv a p h g f (algebraMap k QR c) =
            towerFactorAssocRingEquiv a p h g f
              (algebraMap PA QR (algebraMap k PA c)) :=
          congrArg (towerFactorAssocRingEquiv a p h g f)
            (IsScalarTower.algebraMap_apply k PA QR c)
        _ = algebraMap E QD (towerFactorRingEquiv a p g (algebraMap k PA c)) :=
          towerFactorAssocRingEquiv_algebraMap a p h g f (algebraMap k PA c)
        _ = algebraMap E QD (algebraMap k E c) :=
          congrArg (algebraMap E QD) ((towerFactorAlgEquiv a p g).commutes c)
        _ = algebraMap k QD c := (IsScalarTower.algebraMap_apply k E QD c).symm }

/-- The original-base algebra equivalence retains the actual quotient comparison. -/
theorem towerFactorAssocAlgEquiv_toRingEquiv :
    (towerFactorAssocAlgEquiv a p h g f).toRingEquiv =
      towerFactorAssocRingEquiv a p h g f := rfl

/-- The relative factor root becomes the direct selected factor root. -/
theorem towerFactorAssocRingEquiv_root :
    towerFactorAssocRingEquiv a p h g f (root (poly qR.1.2)) = root (poly qD.1.2) := by
  apply (towerFactorRingEquiv p h f).injective
  rw [towerFactorAssocRingEquiv_apply, towerFactorRingEquiv_root,
    towerFactorRingEquiv_root, towerFactorRingEquiv_root]

/-- The relative coefficient-factor map is carried to the original direct factor map. -/
theorem towerFactorAssocRingEquiv_map (b : HA) :
    towerFactorAssocRingEquiv a p h g f
      (AdjoinRoot.map (algebraMap A PA) hA (poly qR.1.2) qR.2 b) =
    AdjoinRoot.map (algebraMap k E) h (poly qD.1.2) qD.2
      (towerFactorRingEquiv a h (f.comp g) b) := by
  apply (towerFactorRingEquiv p h f).injective
  rw [towerFactorAssocRingEquiv_apply, towerFactorRingEquiv_map,
    towerFactorRingEquiv_map]

/-- The relative coefficient-factor square is an equality of the original native maps. -/
theorem towerFactorAssocRingEquiv_comp_adjoinRootMap :
    (towerFactorAssocRingEquiv a p h g f).toRingHom.comp
        (AdjoinRoot.map (algebraMap A PA) hA (poly qR.1.2) qR.2) =
      (AdjoinRoot.map (algebraMap k E) h (poly qD.1.2) qD.2).comp
        (towerFactorRingEquiv a h (f.comp g)).toRingHom := by
  apply RingHom.ext
  intro b
  exact towerFactorAssocRingEquiv_map a p h g f b

/-- Starting in the original top field, the two actual coefficient-factor routes coincide. -/
theorem towerFactorAssocRingEquiv_map_map (b : H) :
    towerFactorAssocRingEquiv a p h g f
      (AdjoinRoot.map (algebraMap A PA) hA (poly qR.1.2) qR.2
        (AdjoinRoot.map (algebraMap k A) h hA qH.2 b)) =
      AdjoinRoot.map (algebraMap k E) h (poly qD.1.2) qD.2 b := by
  rw [towerFactorAssocRingEquiv_map, towerFactorRingEquiv_map]

/-- The full three-level coefficient-factor square retains both original divisibility proofs. -/
theorem towerFactorAssocRingEquiv_comp_adjoinRootMap_comp_adjoinRootMap :
    (towerFactorAssocRingEquiv a p h g f).toRingHom.comp
        ((AdjoinRoot.map (algebraMap A PA) hA (poly qR.1.2) qR.2).comp
          (AdjoinRoot.map (algebraMap k A) h hA qH.2)) =
      AdjoinRoot.map (algebraMap k E) h (poly qD.1.2) qD.2 := by
  apply RingHom.ext
  intro b
  exact towerFactorAssocRingEquiv_map_map a p h g f b

/-- Coefficient transport sends the actual relative monic factor to the actual direct factor. -/
theorem towerFactorAssoc_poly_map :
    (poly qR.1.2).map (towerFactorRingEquiv a p g).toRingHom = poly qD.1.2 := by
  have hc : (towerFactorAssocRingEquiv a p h g f).toRingHom.comp (of (poly qR.1.2)) =
      (of (poly qD.1.2)).comp (towerFactorRingEquiv a p g).toRingHom :=
    towerFactorAssocRingEquiv_comp_algebraMap a p h g f
  have he := Polynomial.hom_eval₂ (p := poly qR.1.2) (f := of (poly qR.1.2))
    (g := (towerFactorAssocRingEquiv a p h g f).toRingHom) (x := root (poly qR.1.2))
  have hroot : (towerFactorAssocRingEquiv a p h g f).toRingHom
      (root (poly qR.1.2)) = root (poly qD.1.2) :=
    towerFactorAssocRingEquiv_root a p h g f
  rw [AdjoinRoot.eval₂_root, map_zero, hc, hroot] at he
  have hdiv : poly qD.1.2 ∣
      (poly qR.1.2).map (towerFactorRingEquiv a p g).toRingHom := by
    apply (AdjoinRoot.mk_eq_zero (f := poly qD.1.2)).mp
    rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
    change ((poly qR.1.2).map (towerFactorRingEquiv a p g).toRingHom).eval₂
      (of (poly qD.1.2)) (root (poly qD.1.2)) = 0
    rw [Polynomial.eval₂_map]
    exact he.symm
  have hi : Irreducible ((poly qR.1.2).map (towerFactorRingEquiv a p g).toRingHom) :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv (towerFactorRingEquiv a p g))).mpr
      (irreducible qR.1.2)
  exact (Polynomial.eq_of_monic_of_associated (monic qD.1.2)
    ((monic qR.1.2).map (towerFactorRingEquiv a p g).toRingHom)
    ((irreducible qD.1.2).associated_of_dvd hi hdiv)).symm

/-- The comparison is the literal quotient map induced by the original coefficient equivalence. -/
theorem towerFactorAssocRingEquiv_toRingHom :
    (towerFactorAssocRingEquiv a p h g f).toRingHom =
      AdjoinRoot.map (towerFactorRingEquiv a p g).toRingHom
        (poly qR.1.2) (poly qD.1.2) (by rw [towerFactorAssoc_poly_map]) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro x
    change towerFactorAssocRingEquiv a p h g f (of (poly qR.1.2) x) =
      AdjoinRoot.map (towerFactorRingEquiv a p g).toRingHom
        (poly qR.1.2) (poly qD.1.2) (by rw [towerFactorAssoc_poly_map])
        (of (poly qR.1.2) x)
    rw [AdjoinRoot.map_of]
    exact towerFactorAssocRingEquiv_algebraMap a p h g f x
  · change towerFactorAssocRingEquiv a p h g f (root (poly qR.1.2)) =
      AdjoinRoot.map (towerFactorRingEquiv a p g).toRingHom
        (poly qR.1.2) (poly qD.1.2) (by rw [towerFactorAssoc_poly_map])
        (root (poly qR.1.2))
    rw [AdjoinRoot.map_root]
    exact towerFactorAssocRingEquiv_root a p h g f

end AdjoinRoot

end
