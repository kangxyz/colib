/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.AffineUnitSymbolResidues
public import Colib.RingTheory.KTheory.MilnorK.Residue.LinearPlaceTranslation
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueOnGenerators

/-!
# Literal linear specialization of native affine norms

Adapted from Aglib `Dedekind/AffineNormSpecialization.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 34–173.
The local ring is exactly the localization at `(X - C a)`. Specialization is
the native shift-map main component, and evaluation uses the native quotient
and residue dictionaries. Constant recovery is proved on symbols and extended
to every class, in every degree, rather than postulated as a norm premise.
-/

@[expose] public noncomputable section
namespace Stacks.Chow

open Polynomial IsLocalRing

namespace PolynomialResidue

variable {k : Type*} [Field k]

attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

local instance linearPointIsMaximal (a : k) :
    (Ideal.span ({Polynomial.X - C a} : Set k[X])).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C a)

/-- The literal quotient-residue dictionary followed by evaluation at the endpoint. -/
def linearResidueEquiv (a : k) :
    ResidueField (Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X]))) ≃+* k :=
  (quotientRingEquivResidueField (Ideal.span ({Polynomial.X - C a} : Set k[X]))).symm.trans
    (quotientSpanXSubCAlgEquiv a).toRingEquiv

/-- Evaluation recovers the residue of the original constant. -/
theorem linearResidueEquiv_residue_constant (a c : k) :
    linearResidueEquiv a
      (residue (Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X])))
        (algebraMap k (Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X])))
          c)) = c := by
  change (quotientSpanXSubCAlgEquiv a)
    ((quotientRingEquivResidueField (Ideal.span ({Polynomial.X - C a} : Set k[X]))).symm
      (residue (Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X])))
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X])))
          (C c)))) = c
  rw [residue_algebraMap_eq_quotientRingEquivResidueField, RingEquiv.symm_apply_apply]
  exact (quotientSpanXSubCAlgEquiv a).commutes c

/-- The native residue identification is compatible with the original base field. -/
theorem linearResidueEquiv_algebraMap (a c : k) :
    linearResidueEquiv a
      (algebraMap k (ResidueField
        (Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X])))) c) = c := by
  change linearResidueEquiv a
    (residue (Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X])))
      (algebraMap k (Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X])))
        c)) = c
  exact linearResidueEquiv_residue_constant a c

/-- Specialization at the actual linear uniformizer, evaluated at its root. -/
def linearSpecialization (a : k) (n : ℕ) :
    MilnorKTheory (RatFunc k) n →ₗ[ℤ] MilnorKTheory k n :=
  (milnorKTheoryMap (linearResidueEquiv a).toRingHom n).comp
    (dvrMilnorSpecialization (F := RatFunc k)
      (irreducible_algebraMap_self (p := Polynomial.X - C a)) n)

/-- The actual canonical linear-place residue, evaluated at its root. -/
def linearResidue (a : k) (n : ℕ) :
    MilnorKTheory (RatFunc k) (n + 1) →ₗ[ℤ] MilnorKTheory k n :=
  (milnorKTheoryMap (linearResidueEquiv a).toRingHom n).comp
    (affineLineResidue (Ideal.span ({Polynomial.X - C a} : Set k[X])) n).toIntLinearMap

/-- Constant symbols are recovered by the actual specialization, including degree zero. -/
theorem linearSpecialization_constant_symbols (a : k) (n : ℕ) (b : Fin n → kˣ) :
    linearSpecialization a n
      (milnorKTupleSymbol (Units.map (RatFunc.C : k →+* RatFunc k).toMonoidHom ∘ b)) =
        milnorKTupleSymbol b := by
  let R := Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X]))
  let v : Fin n → Rˣ := Units.map (algebraMap k R).toMonoidHom ∘ b
  have hv : Units.map (algebraMap R (RatFunc k)).toMonoidHom ∘ v =
      Units.map (RatFunc.C : k →+* RatFunc k).toMonoidHom ∘ b := by
    funext i
    apply Units.ext
    change algebraMap R (RatFunc k) (algebraMap k[X] R (C (b i : k))) = RatFunc.C (b i : k)
    rw [← IsScalarTower.algebraMap_apply k[X] R (RatFunc k), RatFunc.algebraMap_C]
  rw [← hv, linearSpecialization, LinearMap.comp_apply,
    dvrMilnorSpecialization_ringUnits, milnorKTheoryMap_tupleSymbol]
  congr 1
  funext i
  apply Units.ext
  exact linearResidueEquiv_residue_constant a (b i)

/-- Literal specialization is a left inverse to restriction on the entire native group. -/
theorem linearSpecialization_comp_constants (a : k) (n : ℕ) :
    (linearSpecialization a n).comp
      (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n) = LinearMap.id := by
  apply milnorKTheory_linearMap_ext
  intro b
  rw [LinearMap.comp_apply, milnorKTheoryMap_tupleSymbol,
    linearSpecialization_constant_symbols, LinearMap.id_apply]

/-- Recovery for an arbitrary constant class. -/
theorem linearSpecialization_constants (a : k) (n : ℕ) (x : MilnorKTheory k n) :
    linearSpecialization a n (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n x) = x :=
  LinearMap.congr_fun (linearSpecialization_comp_constants a n) x

/-- Every pair of actual linear specializations agrees on the constant image. -/
theorem linearSpecialization_eq_of_mem_constant_range (a b : k) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) n)
    (hx : x ∈ LinearMap.range (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n)) :
    linearSpecialization a n x = linearSpecialization b n x := by
  obtain ⟨y, rfl⟩ := hx
  rw [linearSpecialization_constants, linearSpecialization_constants]

/-- Appending the literal linear parameter recovers every constant through residue. -/
theorem linearResidue_mulSymbol_constants (a : k) (n : ℕ) (x : MilnorKTheory k n) :
    linearResidue a n
      (milnorKMulSymbol (RatFunc k) n (polyUnit (irreducible_X_sub_C a).ne_zero)
        (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n x)) = x := by
  have h : (linearResidue a n).comp
      ((milnorKMulSymbol (RatFunc k) n
        (polyUnit (irreducible_X_sub_C a).ne_zero)).toIntLinearMap.comp
          (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n)) = LinearMap.id := by
    apply milnorKTheory_linearMap_ext
    intro b
    let R := Localization.AtPrime (Ideal.span ({Polynomial.X - C a} : Set k[X]))
    let v : Fin n → Rˣ := Units.map (algebraMap k R).toMonoidHom ∘ b
    have hv : Units.map (algebraMap R (RatFunc k)).toMonoidHom ∘ v =
        Units.map (RatFunc.C : k →+* RatFunc k).toMonoidHom ∘ b := by
      funext i
      apply Units.ext
      change algebraMap R (RatFunc k) (algebraMap k[X] R (C (b i : k))) = RatFunc.C (b i : k)
      rw [← IsScalarTower.algebraMap_apply k[X] R (RatFunc k), RatFunc.algebraMap_C]
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      milnorKTheoryMap_tupleSymbol, LinearMap.id_apply]
    rw [← hv, milnorKMulSymbol_tupleSymbol, linearResidue, LinearMap.comp_apply]
    unfold affineLineResidue
    simp only [AddMonoidHom.coe_toIntLinearMap]
    rw [← dvrFracUniformizer_irreducible_algebraMap_self
        (irreducible_X_sub_C a).ne_zero,
      dvrMilnorTameSymbol'_tuple_snoc_uniformizer, milnorKTheoryMap_tupleSymbol]
    congr 1
    funext i
    apply Units.ext
    exact linearResidueEquiv_residue_constant a (b i)
  exact LinearMap.congr_fun h x

/-- On the constant image the parameter residue is the actual specialization. -/
theorem linearResidue_mulSymbol_eq_specialization (a : k) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) n)
    (hx : x ∈ LinearMap.range (milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n)) :
    linearResidue a n
      (milnorKMulSymbol (RatFunc k) n (polyUnit (irreducible_X_sub_C a).ne_zero) x) =
      linearSpecialization a n x := by
  obtain ⟨y, rfl⟩ := hx
  rw [linearResidue_mulSymbol_constants, linearSpecialization_constants]

end PolynomialResidue

namespace DedekindResidue

open PolynomialResidue IsDedekindDomain

universe u
variable (k S E : Type u) [Field k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- Actual endpoint specializations of an unramified class's native norm agree. -/
theorem linearSpecialization_norm_eq_of_totalResidue_zero (a b : k) (n : ℕ)
    (x : MilnorKTheory E (n + 1)) (hx : totalResidue S E n x = 0) :
    linearSpecialization a (n + 1) (milnorKNorm (RatFunc k) E (n + 1) x) =
      linearSpecialization b (n + 1) (milnorKNorm (RatFunc k) E (n + 1) x) :=
  linearSpecialization_eq_of_mem_constant_range a b (n + 1) _
    (norm_mem_constant_range_of_totalResidue_zero k S E n x hx)

/-- Global unit symbols have equal actual endpoint specializations of their norm. -/
theorem linearSpecialization_norm_ring_unit_symbol_eq (a b : k) (n : ℕ)
    (u : Fin (n + 1) → Sˣ) :
    linearSpecialization a (n + 1) (milnorKNorm (RatFunc k) E (n + 1)
      (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) =
      linearSpecialization b (n + 1) (milnorKNorm (RatFunc k) E (n + 1)
        (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) :=
  linearSpecialization_eq_of_mem_constant_range a b (n + 1) _
    (norm_ring_unit_symbol_mem_constant_range k S E n u)

/-- Last-slot linear-parameter residue of the actual norm is its specialization. -/
theorem linearResidue_norm_ring_unit_symbol_mulSymbol (a : k) (n : ℕ)
    (u : Fin (n + 1) → Sˣ) :
    linearResidue a (n + 1)
      (milnorKMulSymbol (RatFunc k) (n + 1) (polyUnit (irreducible_X_sub_C a).ne_zero)
        (milnorKNorm (RatFunc k) E (n + 1)
          (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u)))) =
      linearSpecialization a (n + 1) (milnorKNorm (RatFunc k) E (n + 1)
        (milnorKTupleSymbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) :=
  linearResidue_mulSymbol_eq_specialization a (n + 1) _
    (norm_ring_unit_symbol_mem_constant_range k S E n u)

end DedekindResidue
end Stacks.Chow
