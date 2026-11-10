module

import Colib.RingTheory.KTheory.MilnorK.Residue.LinearPlaceTranslation

noncomputable section

set_option autoImplicit false

open Polynomial IsLocalRing Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
  isDiscreteValuationRing_localizationAtPrime_polynomial

universe u

variable {k : Type u} [Field k]

local instance milnorLinearPlaceTranslationTest_isMaximal_span_X_sub_C (a : k) :
    (Ideal.span ({X - C a} : Set k[X])).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C a)

example (a : k) (n : ℕ) (x : MilnorKTheory (RatFunc k) (n + 1)) :
    dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
        (milnorKTheoryMap (RatFunc.laurent a).toRingHom (n + 1) x) =
      milnorKTheoryMap
        (ResidueField.map
          (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
            (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
            (span_X_sub_C_eq_comap_taylorEquiv a))) n
        (dvrMilnorTameSymbol'
          (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) (RatFunc k) n x) :=
  dvrMilnorTameSymbol'_map_laurent_X_sub_C a n x

example (a : k) (n : ℕ) (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKTheoryMap (RatFunc.laurent a).toRingHom (n + 1) x)) =
      milnorKTheoryMap
        ((quotientSpanXSubCAlgEquiv a).toRingHom.comp
          (quotientRingEquivResidueField
            (Ideal.span ({X - C a} : Set k[X]))).symm.toRingHom) n
        (dvrMilnorTameSymbol'
          (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) (RatFunc k) n x) :=
  dvrMilnorTameSymbol'_map_laurent_linearPlace a n x

example {d : ℕ} (ψ : MonicIrreducibleOfDegree k d) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    monicIrreducibleResidue ψ (x : MilnorKRing (RatFunc k)) =
      (milnorKTheoryMap
        (quotientRingEquivResidueField (Ideal.span {poly ψ})).symm.toRingHom n
        (dvrMilnorTameSymbol' (Localization.AtPrime (Ideal.span {poly ψ}))
          (RatFunc k) n x) : MilnorKRing (k[X] ⧸ Ideal.span {poly ψ})) :=
  monicIrreducibleResidue_coe_eq_canonical ψ n x

example (a : k) (n : ℕ) (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a,
            natDegree_X_sub_C a⟩ : MonicIrreducibleOfDegree k 1)
          (x : MilnorKRing (RatFunc k))) =
      (milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKTheoryMap (RatFunc.laurent a).toRingHom (n + 1) x)) : MilnorKRing k) :=
  monicIrreducibleResidue_X_sub_C_coe_eq_origin a n x

example (a : k) (x : MilnorKTheory (RatFunc k) 1) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a,
            natDegree_X_sub_C a⟩ : MonicIrreducibleOfDegree k 1)
          (x : MilnorKRing (RatFunc k))) =
      (milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom 0
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) 0
          (milnorKTheoryMap (RatFunc.laurent a).toRingHom 1 x)) : MilnorKRing k) :=
  monicIrreducibleResidue_X_sub_C_coe_eq_origin a 0 x
