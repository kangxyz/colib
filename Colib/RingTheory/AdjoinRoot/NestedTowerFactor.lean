/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.NestedFactorIndexEquiv
public import Colib.RingTheory.AdjoinRoot.TowerFactorOfRootEquiv

/-!
# The canonical tower factor of an actual nested scalar factor

For each original top scalar factor, the complete nested-factor bijection gives
the actual lower and relative factors and their root-preserving quotient
equivalence. Its coefficient restriction is an actual lower-to-top algebra map.
The relative polynomial is exactly the canonical `AdjoinRoot.towerFactor` for
that map: both are the minimal polynomial of the original top root under the
same coefficient action.

The quotient comparison fixes the original lower coefficients, preserves the
root, and is the literal `AdjoinRoot.map` for the identity coefficient map. The
original relative coefficient-factor square is retained. No norm, separability,
normality, characteristic or presentation-independence assumption is used.

The generic root-equivalence canonical factor comparison is reused from
its independent lower algebraic owner.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

private theorem nestedTowerFactor_sigma_poly_injective {F : Type*} [Field F] :
    Function.Injective (fun r : Σ d : ℕ, MonicIrreducibleOfDegree F d => poly r.2) := by
  intro r s h
  obtain ⟨d, r⟩ := r
  obtain ⟨e, s⟩ := s
  change poly r = poly s at h
  obtain rfl : d = e := by rw [← natDegree_eq r, h, natDegree_eq s]
  obtain rfl := poly_injective h
  rfl

variable {k K : Type*} [Field k] [Field K] (φ : k →+* K)
  (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "q" => towerFactor p h f
local notation "Top" =>
  {s : Σ d : ℕ, MonicIrreducibleOfDegree K d // poly (Sigma.snd s) ∣ Polynomial.map φ h}

/-- The actual lower-to-top map induced by the chosen nested quotient equivalence. -/
def nestedScalarFactorLowerAlgHom (s : Top) :
    AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) →ₐ[K]
      AdjoinRoot (poly s.1.2) :=
  (nestedScalarFactorQuotientEquiv φ p h f s).toAlgHom.comp
    (ofAlgHom K (poly (nestedScalarFactorIndexEquiv φ p h f s).2.1.2))



/-- The coefficient action is literally the restriction of the original quotient equivalence. -/
theorem nestedScalarFactorLowerAlgHom_apply (s : Top) (a : (AdjoinRoot (poly
  (nestedScalarFactorIndexEquiv φ p h f s).1.1.2))) :
    (nestedScalarFactorLowerAlgHom φ p h f s) a = (nestedScalarFactorQuotientEquiv φ p h f s) (of
      (poly ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2) a) := rfl

/-- This induced embedding retains the original lower-field scalar-factor square. -/
theorem nestedScalarFactorLowerAlgHom_comp_adjoinRootMap (s : Top) :
    ((nestedScalarFactorLowerAlgHom φ p h f s)).toRingHom.comp (AdjoinRoot.map φ p (poly
      ((nestedScalarFactorIndexEquiv φ p h f s).1).1.2) ((nestedScalarFactorIndexEquiv φ p h f
      s).1).2) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp f.toRingHom :=
  (nestedScalarFactorQuotientEquiv_maps φ p h f s).2.1

/-- The actual relative factor and the canonical tower factor have identical polynomials. -/
theorem nestedScalarFactor_poly_eq_towerFactor (s : Top) : poly ((nestedScalarFactorIndexEquiv φ p h
  f s).2).1.2 = poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
  (nestedScalarFactorLowerAlgHom φ p h f s)).1.2 := by
  have hroot := nestedScalarFactorQuotientEquiv_root φ p h f s
  have hpoly := rootEquiv_poly_eq_towerFactor (poly ((nestedScalarFactorIndexEquiv φ p h f
    s).1).1.2) (poly s.1.2) ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2
    (nestedScalarFactorQuotientEquiv φ p h f s) hroot
  exact hpoly

/-- Equality of the native factor indices includes the literal dependent degree. -/
theorem nestedScalarFactor_index_eq_towerFactor (s : Top) : ((nestedScalarFactorIndexEquiv φ p h f
  s).2).1 = (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
  (nestedScalarFactorLowerAlgHom φ p h f s)).1 :=
  nestedTowerFactor_sigma_poly_injective (nestedScalarFactor_poly_eq_towerFactor φ p h f s)

/-- The same original relative factor divides the original top polynomial
over the lower quotient. -/
theorem nestedScalarFactor_dvd_top_map (s : Top) :
    poly ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2 ∣ (poly s.1.2).map (algebraMap K
      (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2))) := by
  rw [nestedScalarFactor_poly_eq_towerFactor φ p h f s]
  exact (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
    (nestedScalarFactorLowerAlgHom φ p h f s)).2

/-- With its proved top divisibility, the original relative index is the canonical native factor. -/
theorem nestedScalarFactor_eq_towerFactor (s : Top) :
    (⟨((nestedScalarFactorIndexEquiv φ p h f s).2).1, nestedScalarFactor_dvd_top_map φ p h f s⟩ :
      {v : Σ d : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f
        s).1.1.2)) d //
        poly v.2 ∣ (poly s.1.2).map (algebraMap K (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ
          p h f s).1.1.2)))}) = (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2)
          (poly s.1.2) (nestedScalarFactorLowerAlgHom φ p h f s)) := by
  apply Subtype.ext
  exact nestedScalarFactor_index_eq_towerFactor φ p h f s

/-- The canonical factor is exactly the identity-coefficient transport of the relative factor. -/
theorem nestedScalarFactor_towerFactor_poly_eq_map_id (s : Top) :
    poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
      (nestedScalarFactorLowerAlgHom φ p h f s)).1.2 = (poly ((nestedScalarFactorIndexEquiv φ p h f
      s).2).1.2).map (RingHom.id (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2)))
      := by
  have hpoly := nestedScalarFactor_poly_eq_towerFactor φ p h f s
  have hmap := Polynomial.map_id
    (p := poly (nestedScalarFactorIndexEquiv φ p h f s).2.1.2)
  have hresult := hpoly.symm.trans hmap.symm
  exact hresult

/-- The literal divisibility used by the identity-coefficient quotient map. -/
theorem nestedScalarFactor_towerFactor_dvd_map_id (s : Top) :
    poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
      (nestedScalarFactorLowerAlgHom φ p h f s)).1.2 ∣ (poly ((nestedScalarFactorIndexEquiv φ p h f
      s).2).1.2).map (RingHom.id (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2)))
      := by
  have hroot := nestedScalarFactorQuotientEquiv_root φ p h f s
  have hdiv := rootEquiv_towerFactor_dvd_map_id (poly ((nestedScalarFactorIndexEquiv φ p h f
    s).1).1.2) (poly s.1.2) ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2
    (nestedScalarFactorQuotientEquiv φ p h f s) hroot
  exact hdiv

/-- Compare the two actual relative quotients through their original maps to the top quotient. -/
def nestedScalarFactorTowerRingEquiv (s : Top) : (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p
  h f s).2.1.2)) ≃+* (AdjoinRoot (poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f
  s).1.1.2) (poly s.1.2) (nestedScalarFactorLowerAlgHom φ p h f s)).1.2)) :=
  ((nestedScalarFactorQuotientEquiv φ p h f s)).toRingEquiv.trans ((towerFactorRingEquiv (poly
    (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2) (nestedScalarFactorLowerAlgHom φ p
    h f s))).symm

/-- The comparison identifies the actual maps into the original top scalar quotient. -/
theorem nestedScalarFactorTowerRingEquiv_apply (s : Top) (x : (AdjoinRoot (poly
  (nestedScalarFactorIndexEquiv φ p h f s).2.1.2))) :
    (towerFactorRingEquiv (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
      (nestedScalarFactorLowerAlgHom φ p h f s)) (nestedScalarFactorTowerRingEquiv φ p h f s x) =
      (nestedScalarFactorQuotientEquiv φ p h f s) x := by
  change (towerFactorRingEquiv (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
    (nestedScalarFactorLowerAlgHom φ p h f s)) ((towerFactorRingEquiv (poly
    (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2) (nestedScalarFactorLowerAlgHom φ p
    h f s)).symm ((nestedScalarFactorQuotientEquiv φ p h f s) x)) = (nestedScalarFactorQuotientEquiv
    φ p h f s) x
  exact ((towerFactorRingEquiv (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
    (nestedScalarFactorLowerAlgHom φ p h f s))).apply_symm_apply ((nestedScalarFactorQuotientEquiv φ
    p h f s) x)

/-- The quotient comparison fixes the original lower-field coefficients. -/
theorem nestedScalarFactorTowerRingEquiv_algebraMap (s : Top) (a : (AdjoinRoot (poly
  (nestedScalarFactorIndexEquiv φ p h f s).1.1.2))) :
    nestedScalarFactorTowerRingEquiv φ p h f s (algebraMap (AdjoinRoot (poly
      (nestedScalarFactorIndexEquiv φ p h f s).1.1.2)) (AdjoinRoot (poly
      (nestedScalarFactorIndexEquiv φ p h f s).2.1.2)) a) =
      algebraMap (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2)) (AdjoinRoot
        (poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
        (nestedScalarFactorLowerAlgHom φ p h f s)).1.2)) a := by
  have hcoeff := rootEquivTowerRingEquiv_algebraMap
    (poly ((nestedScalarFactorIndexEquiv φ p h f s).1).1.2) (poly s.1.2)
      ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2 (nestedScalarFactorQuotientEquiv φ p h f s) a
  exact hcoeff

/-- The quotient comparison carries the original relative root to the canonical tower root. -/
theorem nestedScalarFactorTowerRingEquiv_root (s : Top) :
    nestedScalarFactorTowerRingEquiv φ p h f s (root (poly ((nestedScalarFactorIndexEquiv φ p h f
      s).2).1.2)) =
      root (poly (towerFactor (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
        (nestedScalarFactorLowerAlgHom φ p h f s)).1.2) := by
  have hroot := nestedScalarFactorQuotientEquiv_root φ p h f s
  have hcomp := rootEquivTowerRingEquiv_root (poly ((nestedScalarFactorIndexEquiv φ p h f s).1).1.2)
    (poly s.1.2) ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2 (nestedScalarFactorQuotientEquiv φ
    p h f s) hroot
  exact hcomp

/-- The comparison is the native quotient map for the identity coefficient map. -/
theorem nestedScalarFactorTowerRingEquiv_toRingHom (s : Top) :
    (nestedScalarFactorTowerRingEquiv φ p h f s).toRingHom =
      AdjoinRoot.map (RingHom.id (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2)))
        (poly ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2) (poly (towerFactor (poly
        (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2) (nestedScalarFactorLowerAlgHom
        φ p h f s)).1.2)
        (nestedScalarFactor_towerFactor_dvd_map_id φ p h f s) := by
  have hroot := nestedScalarFactorQuotientEquiv_root φ p h f s
  have hmap := rootEquivTowerRingEquiv_toRingHom (poly ((nestedScalarFactorIndexEquiv φ p h f
    s).1).1.2) (poly s.1.2) ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2
    (nestedScalarFactorQuotientEquiv φ p h f s) hroot
  exact hmap

/-- The actual quotient comparison square, as an equality of original ring homomorphisms. -/
theorem nestedScalarFactorTowerRingEquiv_comp_towerFactorRingEquiv (s : Top) :
    ((towerFactorRingEquiv (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
      (nestedScalarFactorLowerAlgHom φ p h f s))).toRingHom.comp (nestedScalarFactorTowerRingEquiv φ
      p h f s).toRingHom =
      ((nestedScalarFactorQuotientEquiv φ p h f s)).toRingHom := by
  apply RingHom.ext
  intro x
  exact nestedScalarFactorTowerRingEquiv_apply φ p h f s x

/-- The canonical branch quotient map retains the original relative coefficient-factor square. -/
theorem nestedScalarFactor_towerFactor_map_square (s : Top) :
    ((towerFactorRingEquiv (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
      (nestedScalarFactorLowerAlgHom φ p h f s))).toRingHom.comp
        ((AdjoinRoot.map (RingHom.id (AdjoinRoot (poly (nestedScalarFactorIndexEquiv φ p h f
          s).1.1.2))) (poly ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2) (poly (towerFactor
          (poly (nestedScalarFactorIndexEquiv φ p h f s).1.1.2) (poly s.1.2)
          (nestedScalarFactorLowerAlgHom φ p h f s)).1.2)
          (nestedScalarFactor_towerFactor_dvd_map_id φ p h f s)).comp
            (AdjoinRoot.map (AdjoinRoot.map φ p (poly ((nestedScalarFactorIndexEquiv φ p h f
              s).1).1.2) ((nestedScalarFactorIndexEquiv φ p h f s).1).2)
              (poly q.1.2) (poly ((nestedScalarFactorIndexEquiv φ p h f s).2).1.2)
                ((nestedScalarFactorIndexEquiv φ p h f s).2).2)) =
      (AdjoinRoot.map φ h (poly s.1.2) s.2).comp
        (towerFactorRingEquiv p h f).toRingHom := by
  let z := nestedScalarFactorIndexEquiv φ p h f s
  let ρ := AdjoinRoot.map (AdjoinRoot.map φ p (poly z.1.1.2) z.1.2)
    (poly q.1.2) (poly z.2.1.2) z.2.2
  let θ := towerFactorRingEquiv (poly z.1.1.2) (poly s.1.2)
    (nestedScalarFactorLowerAlgHom φ p h f s)
  have hmap := nestedScalarFactorTowerRingEquiv_toRingHom φ p h f s
  have hreplace := congrArg
    (fun ψ : _ →+* _ => θ.toRingHom.comp (ψ.comp ρ)) hmap.symm
  have hcomp := nestedScalarFactorTowerRingEquiv_comp_towerFactorRingEquiv φ p h f s
  have hcompρ := congrArg (fun ψ : _ →+* _ => ψ.comp ρ) hcomp
  have hsquare := (nestedScalarFactorQuotientEquiv_maps φ p h f s).2.2
  have hresult := hreplace.trans (hcompρ.trans hsquare)
  exact hresult

end AdjoinRoot

end
