module

import Colib.RingTheory.Polynomial.LinearPlaceTranslation
import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.PolyResidueRing

noncomputable section

set_option autoImplicit false

open Polynomial IsLocalRing Stacks.Chow

variable {k : Type*} [Field k]

local instance linearPlaceTranslationTest_isMaximal_span_X_sub_C (a : k) :
    (Ideal.span ({X - C a} : Set k[X])).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C a)

example (a : k) : Function.Bijective (RatFunc.laurent a) := by
  change Function.Bijective (RatFunc.laurent a).toRingHom
  rw [← RatFunc.ringEquivOfRingEquiv_taylorEquiv_toRingHom]
  exact (IsFractionRing.ringEquivOfRingEquiv (K := RatFunc k) (L := RatFunc k)
    (taylorEquiv a).toRingEquiv).bijective

example (a : k) :
    Localization.localRingEquiv (Ideal.span ({X - C a} : Set k[X]))
        (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingEquiv
        (span_X_sub_C_eq_comap_taylorEquiv a)
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X])))
          (X - C a)) =
      algebraMap k[X] (localRingAtOrigin k) X :=
  localRingHom_taylorEquiv_X_sub_C a

example (a : k) :
    let q : MonicIrreducibleOfDegree k 1 :=
      ⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩
    ∀ x : Localization.AtPrime (Ideal.span {MonicIrreducibleOfDegree.poly q}),
      RatFunc.laurent a
          (algebraMap (Localization.AtPrime (Ideal.span {MonicIrreducibleOfDegree.poly q}))
            (RatFunc k) x) =
        algebraMap (localRingAtOrigin k) (RatFunc k)
          (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
            (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
            (span_X_sub_C_eq_comap_taylorEquiv a) x) := by
  intro q x
  exact RatFunc.laurent_algebraMap_localizationAtPrime_X_sub_C a x

example (a : k) (p : k[X]) :
    ResidueField.map
        (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
          (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
          (span_X_sub_C_eq_comap_taylorEquiv a))
        (residue (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X])))
          (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) p)) =
      residueFieldAtOriginEquiv k (p.eval a) :=
  residueField_map_taylorEquiv_algebraMap a p

example (a : k) :
    (residueFieldAtOriginEquiv k).symm.toRingHom.comp
        (ResidueField.map
          (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
            (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
            (span_X_sub_C_eq_comap_taylorEquiv a))) =
      (quotientSpanXSubCAlgEquiv a).toRingHom.comp
        (quotientRingEquivResidueField
          (Ideal.span ({X - C a} : Set k[X]))).symm.toRingHom :=
  residueFieldAtOriginEquiv_symm_comp_residueField_map_taylorEquiv a

end
