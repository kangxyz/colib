/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import Colib.RingTheory.Polynomial.LinearPlaceTranslation
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.PolyResidueRing

/-!
# Native Milnor residues at linear places and Taylor translation

Taylor translation by `+a` carries the actual linear place `(X - C a)` to the
origin. The actual local Taylor map sends the specified uniformizer `X - C a`
to `X`, so the canonical DVR residue square has unit correction and exponent
both equal to one. Transport by the native quotient and evaluation maps then
identifies this residue with the native origin residue after `RatFunc.laurent a`.

The whole-ring polynomial residue is compared only on homogeneous classes.
The bridge applies to every original `MonicIrreducibleOfDegree` and is then
specialized to the literal native constructor with polynomial `X - C a`.
No point carrier, field, residue, local map, or norm is defined here. There are
no characteristic, finiteness, normality, or separability assumptions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open Polynomial IsLocalRing

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

variable {k : Type u} [Field k]

local instance milnorLinearPlaceTranslation_isMaximal_span_X_sub_C (a : k) :
    (Ideal.span ({X - C a} : Set k[X])).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C a)

/-- Canonical DVR residues commute with the actual local Taylor map, with
ramification exponent one, before choosing residue-field coordinates. -/
theorem dvrMilnorTameSymbol'_map_laurent_X_sub_C (a : k) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
        (milnorKTheoryMap (RatFunc.laurent a).toRingHom (n + 1) x) =
      milnorKTheoryMap
        (ResidueField.map
          (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
            (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
            (span_X_sub_C_eq_comap_taylorEquiv a))) n
        (dvrMilnorTameSymbol'
          (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) (RatFunc k) n x) := by
  have h := DFunLike.congr_fun
    (dvrMilnorTameSymbol'_map_ramified
      (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
        (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
        (span_X_sub_C_eq_comap_taylorEquiv a))
      (RatFunc.laurent a).toRingHom
      (RatFunc.laurent_algebraMap_localizationAtPrime_X_sub_C a)
      (irreducible_algebraMap_self (p := X - C a))
      (irreducible_algebraMap_X (k := k)) (1 : (localRingAtOrigin k)ˣ) 1
      (by simpa using localRingHom_taylorEquiv_X_sub_C a) n) x
  simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    Nat.cast_one, one_smul] using h

/-- The actual canonical residue at `X - C a`, evaluated using the original
quotient dictionary, is the original origin residue after native translation. -/
theorem dvrMilnorTameSymbol'_map_laurent_linearPlace (a : k) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKTheoryMap (RatFunc.laurent a).toRingHom (n + 1) x)) =
      milnorKTheoryMap
        ((quotientSpanXSubCAlgEquiv a).toRingHom.comp
          (quotientRingEquivResidueField
            (Ideal.span ({X - C a} : Set k[X]))).symm.toRingHom) n
        (dvrMilnorTameSymbol'
          (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) (RatFunc k) n x) := by
  let z : MilnorKTheory
      (ResidueField (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X])))) n :=
    dvrMilnorTameSymbol'
      (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) (RatFunc k) n x
  let f : ResidueField (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) →+*
      ResidueField (localRingAtOrigin k) :=
    ResidueField.map
      (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
        (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
        (span_X_sub_C_eq_comap_taylorEquiv a))
  let g : ResidueField (localRingAtOrigin k) →+* k :=
    (residueFieldAtOriginEquiv k).symm.toRingHom
  let h : ResidueField
      (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) →+* k :=
    (quotientSpanXSubCAlgEquiv a).toRingHom.comp
      (quotientRingEquivResidueField
        (Ideal.span ({X - C a} : Set k[X]))).symm.toRingHom
  have hfield : g.comp f = h :=
    residueFieldAtOriginEquiv_symm_comp_residueField_map_taylorEquiv a
  have hcomp : milnorKTheoryMap (g.comp f) n z =
      milnorKTheoryMap g n (milnorKTheoryMap f n z) :=
    DFunLike.congr_fun (milnorKTheoryMap_comp (n := n) f g) z
  have hcoordinates : milnorKTheoryMap (g.comp f) n z = milnorKTheoryMap h n z :=
    congrArg
      (fun e : ResidueField
        (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) →+* k =>
          milnorKTheoryMap e n z) hfield
  have hnatural := congrArg
    (fun y : MilnorKTheory (ResidueField (localRingAtOrigin k)) n =>
      milnorKTheoryMap g n y) (dvrMilnorTameSymbol'_map_laurent_X_sub_C a n x)
  exact hnatural.trans (hcomp.symm.trans hcoordinates)

/-- On an original homogeneous class, the original whole-ring polynomial
residue is exactly the canonical DVR residue transported by its native
quotient dictionary. No new residue on the homogeneous group is introduced. -/
theorem monicIrreducibleResidue_coe_eq_canonical {d : ℕ}
    (ψ : MonicIrreducibleOfDegree k d) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    monicIrreducibleResidue ψ (x : MilnorKRing (RatFunc k)) =
      (milnorKTheoryMap
        (quotientRingEquivResidueField (Ideal.span {poly ψ})).symm.toRingHom n
        (dvrMilnorTameSymbol' (Localization.AtPrime (Ideal.span {poly ψ}))
          (RatFunc k) n x) : MilnorKRing (k[X] ⧸ Ideal.span {poly ψ})) := by
  rw [dvrMilnorTameSymbol'_eq_of_ramified_identity
    (irreducible_algebraMap_self (p := poly ψ))]
  simp only [milnorKTheoryMap_eq_transport]
  rfl

/-- The actual whole-ring residue at the literal native linear point, on any
homogeneous class, is the native translated origin residue after evaluation. -/
theorem monicIrreducibleResidue_X_sub_C_coe_eq_origin (a : k) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a,
            natDegree_X_sub_C a⟩ : MonicIrreducibleOfDegree k 1)
          (x : MilnorKRing (RatFunc k))) =
      (milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKTheoryMap (RatFunc.laurent a).toRingHom (n + 1) x)) : MilnorKRing k) := by
  let ψ : MonicIrreducibleOfDegree k 1 :=
    ⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩
  let e : (k[X] ⧸ Ideal.span {poly ψ}) →+* k :=
    (quotientSpanXSubCAlgEquiv a).toRingHom
  let q : (Ideal.span {poly ψ}).ResidueField →+* (k[X] ⧸ Ideal.span {poly ψ}) :=
    (quotientRingEquivResidueField (Ideal.span {poly ψ})).symm.toRingHom
  let z : MilnorKTheory (Ideal.span {poly ψ}).ResidueField n :=
    dvrMilnorTameSymbol' (Localization.AtPrime (Ideal.span {poly ψ})) (RatFunc k) n x
  have hpoly : milnorKRingMap e (monicIrreducibleResidue ψ (x : MilnorKRing (RatFunc k))) =
      milnorKRingMap e
        (milnorKTheoryMap q n z : MilnorKRing (k[X] ⧸ Ideal.span {poly ψ})) :=
    congrArg (fun y : MilnorKRing (k[X] ⧸ Ideal.span {poly ψ}) => milnorKRingMap e y)
      (monicIrreducibleResidue_coe_eq_canonical ψ n x)
  have hcoe :
      (milnorKTheoryMap e n (milnorKTheoryMap q n z) : MilnorKRing k) =
        milnorKRingMap e
          (milnorKTheoryMap q n z : MilnorKRing (k[X] ⧸ Ideal.span {poly ψ})) :=
    congrArg
      (fun t : MilnorKTheory (k[X] ⧸ Ideal.span {poly ψ}) n →ₗ[ℤ] MilnorKTheory k n =>
        (t (milnorKTheoryMap q n z) : MilnorKRing k))
      (milnorKTheoryMap_eq_transport (n := n) e)
  have hcomp : milnorKTheoryMap (e.comp q) n z =
      milnorKTheoryMap e n (milnorKTheoryMap q n z) :=
    DFunLike.congr_fun (milnorKTheoryMap_comp (n := n) q e) z
  have horigin : milnorKTheoryMap (e.comp q) n z =
      milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKTheoryMap (RatFunc.laurent a).toRingHom (n + 1) x)) :=
    (dvrMilnorTameSymbol'_map_laurent_linearPlace a n x).symm
  exact hpoly.trans (hcoe.symm.trans
    ((congrArg (fun y : MilnorKTheory k n => (y : MilnorKRing k)) hcomp.symm).trans
      (congrArg (fun y : MilnorKTheory k n => (y : MilnorKRing k)) horigin)))

end Stacks.Chow

end
