/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Colib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.ScalarExtension
public import Colib.RingTheory.MvPolynomial.ScalarTowerDescent
public import Colib.RingTheory.Bertini.FiniteSubfieldParameters

/-!
# The same quadratic coordinates at one finite separable stage

Finite tensor support models the original coefficients and both principal-open elements at
one actual intermediate field. Canonical scalar-extension and localization comparisons then
descend the full tuple's finiteness and etaleness, and the tail tuple's smoothness. The etale
open D(r_e) and the smooth whole-fiber open D(r) retain distinct image equations. Their
point and whole-fiber incidence conditions and relative dimension are separate obligations.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial Algebra.TensorProduct
universe u
namespace QuadraticIncidence.InfinityChart
variable (K E L B : Type u) [Field K] [Field E] [Field L]
 [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
 [CommRing B] [Algebra K B] {σ : Type u} [Fintype σ]
 (g : σ → E ⊗[K] B) (d : ℕ)
/-- The actual intermediate-field tensor inclusion extends each original quadratic function. -/
theorem originalFunction_tensorInclusion (c : Fin d × Exponent σ → E) (i : Fin d) :
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B)
      (aeval g (parameterTuple E σ d c i).val) =
    aeval (fun j => Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g j))
      (parameterTuple L σ d (fun q => algebraMap E L (c q)) i).val := by
  let φ : E ⊗[K] B →ₐ[E] L ⊗[K] B :=
    ((cancelBaseChange K E L L B).toAlgHom.restrictScalars E).comp
      Algebra.TensorProduct.includeRight
  have h := originalFunction_scalarExtension E L (E ⊗[K] B) (L ⊗[K] B) φ g d c i
  change cancelBaseChange K E L L B
    ((1 : L) ⊗ₜ[E] aeval g (parameterTuple E σ d c i).val) =
      aeval (fun j => cancelBaseChange K E L L B ((1 : L) ⊗ₜ[E] g j))
        (parameterTuple L σ d (fun q => algebraMap E L (c q)) i).val at h
  simpa only [cancelBaseChange_includeRight] using h

/-- A faithfully-flat descending property descends on the exact original quadratic coordinate
map. -/
theorem of_quadraticCoordinateHom_scalarTower
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat) (hi : RingHom.RespectsIso P)
    (c : Fin d × Exponent σ → E)
    (hf : P (quadraticCoordinateHom L (L ⊗[K] B)
      (fun j => Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g j)) d
      (fun q => algebraMap E L (c q)))) :
    P (quadraticCoordinateHom E (E ⊗[K] B) g d c) := by
  unfold quadraticCoordinateHom at hf ⊢
  apply MvPolynomial.of_aeval_scalarTower K E L B
    (fun i : Fin d => aeval g (parameterTuple E σ d c i).val) P hP hi
  simpa only [originalFunction_tensorInclusion] using hf

/-- Descent preserves the original quadratic coordinates and their chosen principal-open element. -/
theorem of_quadraticCoordinateHom_away_scalarTower
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat) (hi : RingHom.RespectsIso P)
    (c : Fin d × Exponent σ → E) (r : E ⊗[K] B)
    (hf : P ((algebraMap (L ⊗[K] B) (Localization.Away
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))).comp
      (quadraticCoordinateHom L (L ⊗[K] B)
        (fun j => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) (g j)) d
        (fun q => algebraMap E L (c q))))) :
    P ((algebraMap (E ⊗[K] B) (Localization.Away r)).comp
      (quadraticCoordinateHom E (E ⊗[K] B) g d c)) := by
  unfold quadraticCoordinateHom at hf ⊢
  apply MvPolynomial.of_aevalAway_scalarTower K E L B
    (fun i : Fin d => aeval g (parameterTuple E σ d c i).val) P hP hi r
  simpa only [originalFunction_tensorInclusion] using hf
end QuadraticIncidence.InfinityChart
namespace QuadraticIncidence.InfinityChart
open IntermediateField
/-- One finite separable stage retains the same auxiliary row, tail coordinates and two
distinct opens.
Finiteness of the full tuple, etaleness on its chosen principal open and smoothness of the tail
on its separate principal open descend to those actual models. The base field may be finite. -/
theorem exists_finsetSubfield_sameTuple_coordinates
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)
    (s : Finset L) (a : Exponent σ → L) (c : Fin d × Exponent σ → L)
    (rₑ r : L ⊗[K] B)
    (hf : (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j)
      (d + 1) (prependParameters L d a c)).Finite)
    (he : ((algebraMap (L ⊗[K] B) (Localization.Away rₑ)).comp
      (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j)
        (d + 1) (prependParameters L d a c))).Etale)
    (hs : ((algebraMap (L ⊗[K] B) (Localization.Away r)).comp
      (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j) d c)).Smooth) :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite K (adjoin K (t : Set L)) ∧
      Algebra.IsSeparable K (adjoin K (t : Set L)) ∧
      ∃ (a' : Exponent σ → adjoin K (t : Set L))
        (c' : Fin d × Exponent σ → adjoin K (t : Set L))
        (rₑ' r' : (adjoin K (t : Set L)) ⊗[K] B),
        (∀ e, (a' e : L) = a e) ∧ (∀ q, (c' q : L) = c q) ∧
        finsetTensorInclusion K L B t rₑ' = rₑ ∧ finsetTensorInclusion K L B t r' = r ∧
        (quadraticCoordinateHom (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B)
          (fun j => 1 ⊗ₜ[K] g j) (d + 1)
          (prependParameters (adjoin K (t : Set L)) d a' c')).Finite ∧
        ((algebraMap ((adjoin K (t : Set L)) ⊗[K] B) (Localization.Away rₑ')).comp
          (quadraticCoordinateHom (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B)
            (fun j => 1 ⊗ₜ[K] g j) (d + 1)
            (prependParameters (adjoin K (t : Set L)) d a' c'))).Etale ∧
        ((algebraMap ((adjoin K (t : Set L)) ⊗[K] B) (Localization.Away r')).comp
          (quadraticCoordinateHom (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B)
            (fun j => 1 ⊗ₜ[K] g j) d c')).Smooth := by
  obtain ⟨t, ht, hfinite, a', c', rₑ', r', ha, hc, hₑ, hr⟩ :=
    exists_finsetSubfield_quadraticParameters K L B d s a c rₑ r
  subst rₑ r
  have haL (e : Exponent σ) : algebraMap (adjoin K (t : Set L)) L (a' e) = a e := ha e
  have hcL (q : Fin d × Exponent σ) :
      algebraMap (adjoin K (t : Set L)) L (c' q) = c q := hc q
  refine ⟨t, ht, hfinite, isSeparable_finsetAdjoinDiagram_obj K L t,
    a', c', rₑ', r', ha, hc, rfl, rfl, ?_, ?_, ?_⟩
  · apply of_quadraticCoordinateHom_scalarTower K (adjoin K (t : Set L)) L B
      (fun j => 1 ⊗ₜ[K] g j) (d + 1) _
      RingHom.Finite.codescendsAlong_faithfullyFlat RingHom.finite_respectsIso
      (prependParameters (adjoin K (t : Set L)) d a' c')
    simpa only [prependParameters_scalarExtension, haL, hcL,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using hf
  · apply of_quadraticCoordinateHom_away_scalarTower K (adjoin K (t : Set L)) L B
      (fun j => 1 ⊗ₜ[K] g j) (d + 1) _
      RingHom.Etale.codescendsAlong_faithfullyFlat RingHom.Etale.respectsIso
      (prependParameters (adjoin K (t : Set L)) d a' c') rₑ'
    change ((algebraMap _ (Localization.Away (finsetTensorInclusion K L B t rₑ'))).comp
      (quadraticCoordinateHom L _
        (fun j => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K (adjoin K (t : Set L)) L) (AlgHom.id K B)
          ((1 : adjoin K (t : Set L)) ⊗ₜ[K] g j)) (d + 1)
        (fun q => algebraMap (adjoin K (t : Set L)) L
          (prependParameters (adjoin K (t : Set L)) d a' c' q)))).Etale
    simpa only [prependParameters_scalarExtension, haL, hcL,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using he
  · apply of_quadraticCoordinateHom_away_scalarTower K (adjoin K (t : Set L)) L B
      (fun j => 1 ⊗ₜ[K] g j) d _
      RingHom.Smooth.codescendsAlong_faithfullyFlat RingHom.Smooth.respectsIso c' r'
    change ((algebraMap _ (Localization.Away (finsetTensorInclusion K L B t r'))).comp
      (quadraticCoordinateHom L _
        (fun j => Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom K (adjoin K (t : Set L)) L) (AlgHom.id K B)
          ((1 : adjoin K (t : Set L)) ⊗ₜ[K] g j)) d
        (fun q => algebraMap (adjoin K (t : Set L)) L (c' q)))).Smooth
    simpa only [hcL, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using hs
end QuadraticIncidence.InfinityChart
