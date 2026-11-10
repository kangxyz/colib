/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Ext
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Data.DFinsupp.Module

/-!
# Finite support of actual Dedekind-domain residues

The original fraction field is retained. Nonzero numerator and denominator
principal ideals have finitely many prime factors. Away from those factors a
fraction is a local unit, so every all-unit symbol has zero actual DVR residue.
Symbol generation then proves finite support for every Milnor class.

Adapted from `Aglib/KTheory/MilnorK/Dedekind/ResidueSupport.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 27–188. The actual
height-one spectrum, localizations, original field and `DFinsupp` support remain
unchanged. The native Stacks symbols and canonical tame residues are used directly.
-/

@[expose] public noncomputable section

namespace Stacks.Chow.DedekindResidue

open IsDedekindDomain

variable (S E : Type*) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E]

/-- The canonical localization action on the specified original fraction field.
This is the same native lift as `AdicCompletion.originalBranchFractionAlgebra`. -/
instance fractionAlgebra (q : HeightOneSpectrum S) : Algebra (Localization.AtPrime q.asIdeal) E :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime q.asIdeal) E
    q.asIdeal.primeCompl (nonZeroDivisors S) q.asIdeal.primeCompl_le_nonZeroDivisors

/-- The actual localization action extends the original domain action. -/
instance fractionTower (q : HeightOneSpectrum S) :
    IsScalarTower S (Localization.AtPrime q.asIdeal) E :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (Localization.AtPrime q.asIdeal) E q.asIdeal.primeCompl (nonZeroDivisors S)
    q.asIdeal.primeCompl_le_nonZeroDivisors

/-- The localization action has exactly the original domain triangle. -/
@[simp] theorem fractionAlgebra_algebraMap (q : HeightOneSpectrum S) (s : S) :
    algebraMap (Localization.AtPrime q.asIdeal) E
      (algebraMap S (Localization.AtPrime q.asIdeal) s) = algebraMap S E s :=
  (IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) E s).symm

/-- The original domain triangle determines the fraction map uniquely.
In particular, the explicit localization lift in the original source is this map. -/
theorem fractionAlgebra_unique (q : HeightOneSpectrum S)
    (f : Localization.AtPrime q.asIdeal →+* E)
    (hf : ∀ s : S, f (algebraMap S (Localization.AtPrime q.asIdeal) s) = algebraMap S E s) :
    f = algebraMap (Localization.AtPrime q.asIdeal) E := by
  apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
  ext s
  exact (hf s).trans (IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) E s)

/-- The specified original field remains the fraction field of each original localization. -/
instance fractionRing (q : HeightOneSpectrum S) :
    IsFractionRing (Localization.AtPrime q.asIdeal) E :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal) E

/-- The actual localization at a height-one prime is a DVR. -/
instance localDvr (q : HeightOneSpectrum S) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot _

/-- Only finitely many height-one primes contain a nonzero element. -/
theorem finite_primes_containing (s : S) (hs : s ≠ 0) :
    Set.Finite {q : HeightOneSpectrum S | s ∈ q.asIdeal} := by
  have h := Ideal.finite_factors (R := S)
    (I := Ideal.span {s}) (by simpa using hs)
  simpa only [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] using h

/-- Every fraction-field unit lifts to a local unit outside a finite set of primes. -/
theorem finite_nonlocal_units (a : Eˣ) :
    Set.Finite {q : HeightOneSpectrum S |
      ¬ ∃ u : (Localization.AtPrime q.asIdeal)ˣ,
        Units.map (algebraMap (Localization.AtPrime q.asIdeal) E).toMonoidHom u = a} := by
  obtain ⟨s, t, ht, hst⟩ := IsFractionRing.div_surjective S (a : E)
  have hs : s ≠ 0 := by
    intro h
    simp only [h, map_zero, zero_div] at hst
    exact a.ne_zero hst.symm
  refine ((finite_primes_containing S s hs).union
    (finite_primes_containing S t (nonZeroDivisors.ne_zero ht))).subset ?_
  intro q hq
  by_contra h
  have hs' : s ∈ q.asIdeal.primeCompl := fun hm => h (Or.inl hm)
  have ht' : t ∈ q.asIdeal.primeCompl := fun hm => h (Or.inr hm)
  let us := (IsLocalization.map_units (Localization.AtPrime q.asIdeal) ⟨s, hs'⟩).unit
  let ut := (IsLocalization.map_units (Localization.AtPrime q.asIdeal) ⟨t, ht'⟩).unit
  apply hq
  refine ⟨us / ut, ?_⟩
  rw [map_div]
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.coe_map,
    us, ut, IsUnit.unit_spec]
  change algebraMap (Localization.AtPrime q.asIdeal) E
      (algebraMap S (Localization.AtPrime q.asIdeal) s) /
    algebraMap (Localization.AtPrime q.asIdeal) E
      (algebraMap S (Localization.AtPrime q.asIdeal) t) = (a : E)
  simpa only [← IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) E] using hst

/-- Every actual symbol has finite residue support in every positive degree. -/
theorem finite_residue_symbol_support (n : ℕ) (a : Fin (n + 1) → Eˣ) :
    Set.Finite {q : HeightOneSpectrum S |
      dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n (milnorKTupleSymbol a) ≠ 0} := by
  classical
  have h := Set.finite_iUnion (fun i => finite_nonlocal_units S E (a i))
  refine h.subset ?_
  intro q hq
  by_contra h
  have hu : ∀ i, ∃ u : (Localization.AtPrime q.asIdeal)ˣ,
      Units.map (algebraMap (Localization.AtPrime q.asIdeal) E).toMonoidHom u = a i := by
    intro i
    by_contra hi
    exact h (Set.mem_iUnion.mpr ⟨i, hi⟩)
  choose u hu using hu
  apply hq
  apply dvrMilnorTameSymbol'_eq_zero_of_milnorKSymbolProd n (List.ofFn a) rfl
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
  exact ⟨u i, congrArg Units.val (hu i)⟩

/-- Classes with finite actual support form an integer submodule. -/
private def finiteResidueSubmodule (n : ℕ) : Submodule ℤ (MilnorKTheory E (n + 1)) where
  carrier := {x | Set.Finite {q : HeightOneSpectrum S |
    dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x ≠ 0}}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro q hq
    by_contra h
    have hx0 : dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x = 0 := by
      simpa using fun hn => h (Or.inl hn)
    have hy0 : dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n y = 0 := by
      simpa using fun hn => h (Or.inr hn)
    exact hq (by rw [map_add, hx0, hy0, add_zero])
  smul_mem' := by
    intro z x hx
    refine hx.subset ?_
    intro q hq hx0
    exact hq (by rw [map_zsmul, hx0, smul_zero])

/-- Actual DVR residues of every original fraction-field class have finite support. -/
theorem finite_residue_support (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    Set.Finite {q : HeightOneSpectrum S |
      dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x ≠ 0} := by
  have h : (finiteResidueSubmodule S E n).mkQ = 0 := by
    apply milnorKTheory_linearMap_ext
    intro a
    change (Submodule.Quotient.mk (milnorKTupleSymbol a) : MilnorKTheory E (n + 1) ⧸
      finiteResidueSubmodule S E n) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (finite_residue_symbol_support S E n a)
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h x)

/-- Native residue Milnor groups carry their existing additive group structures. -/
instance residueAddCommGroup (n : ℕ) :
    (q : HeightOneSpectrum S) → AddCommGroup (MilnorKTheory (IsLocalRing.ResidueField
      (Localization.AtPrime q.asIdeal)) n) := fun _ => inferInstance

/-- The existing integer actions on the native residue Milnor groups. -/
instance residueModule (n : ℕ) :
    (q : HeightOneSpectrum S) → Module ℤ (MilnorKTheory (IsLocalRing.ResidueField
      (Localization.AtPrime q.asIdeal)) n) := fun _ => inferInstance

/-- The actual total residue, with finite support proved for every class. -/
def totalResidue (n : ℕ) : MilnorKTheory E (n + 1) →ₗ[ℤ]
    Π₀ q : HeightOneSpectrum S, MilnorKTheory (IsLocalRing.ResidueField
      (Localization.AtPrime q.asIdeal)) n where
  toFun x := ⟨fun q => dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x,
    Trunc.mk ⟨(finite_residue_support S E n x).toFinset.val, fun q => by
      classical
      by_cases hq : dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x = 0
      · exact Or.inr hq
      · exact Or.inl ((finite_residue_support S E n x).mem_toFinset.mpr hq)⟩⟩
  map_add' x y := by
    apply DFinsupp.ext
    intro q
    exact map_add (dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n) x y
  map_smul' z x := by
    apply DFinsupp.ext
    intro q
    exact map_zsmul (dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n) z x

/-- Each total-residue coordinate is the original DVR residue, literally. -/
@[simp] theorem totalResidue_apply (n : ℕ) (x : MilnorKTheory E (n + 1))
    (q : HeightOneSpectrum S) :
    totalResidue S E n x q = dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x := rfl

/-- The total residue vanishes precisely when every local residue vanishes. -/
theorem totalResidue_eq_zero_iff (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    totalResidue S E n x = 0 ↔ ∀ q : HeightOneSpectrum S,
      dvrMilnorTameSymbol' (Localization.AtPrime q.asIdeal) E n x = 0 := by
  constructor
  · intro h q
    exact DFunLike.congr_fun h q
  · intro h
    exact DFinsupp.ext h

end Stacks.Chow.DedekindResidue
