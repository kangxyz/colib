/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Laurent
public import Mathlib.RingTheory.Polynomial.Quotient
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ConstantRetraction

/-!
# Translating the actual linear place to the origin

The native Taylor equivalence at `a` carries `X - C a` to `X`. Its native local
ring map commutes with `RatFunc.laurent a`, whose underlying ring homomorphism
is the fraction-field equivalence induced by `Polynomial.taylorEquiv a`.
The induced residue map agrees with evaluation at `a` through the existing
polynomial-quotient and origin-residue equivalences.

All carriers and maps are the existing native ones. In particular, the local
ring is the literal localization at `(X - C a)`, and the polynomial residue
field is the literal quotient by that ideal. No point, local ring, rational
function field, residue field, or translation map is defined here. There is
no characteristic, finiteness, normality, or separability assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open Polynomial IsLocalRing Stacks.Chow

variable {k : Type*} [Field k]

local instance linearPlaceTranslation_isMaximal_span_X_sub_C (a : k) :
    (Ideal.span ({X - C a} : Set k[X])).IsMaximal :=
  isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C a)

namespace Polynomial

/-- Taylor translation by `+a`, not `-a`, contracts the origin ideal to the
actual ideal of the linear place `a`. -/
theorem span_X_sub_C_eq_comap_taylorEquiv (a : k) :
    Ideal.span ({X - C a} : Set k[X]) =
      (Ideal.span ({X} : Set k[X])).comap (taylorEquiv a).toRingHom := by
  ext p
  change p ∈ Ideal.span ({X - C a} : Set k[X]) ↔
    taylor a p ∈ Ideal.span ({X} : Set k[X])
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton, dvd_iff_isRoot,
    Polynomial.IsRoot, X_dvd_iff, taylor_coeff_zero]

/-- The native local Taylor map sends every original polynomial to its native
Taylor expansion in the origin localization. -/
theorem localRingHom_taylorEquiv_algebraMap (a : k) (p : k[X]) :
    Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
        (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
        (span_X_sub_C_eq_comap_taylorEquiv a)
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) p) =
      algebraMap k[X] (localRingAtOrigin k) (taylor a p) :=
  Localization.localRingHom_to_map _ _ _ _ p

/-- The actual uniformizer maps exactly to `X`: the ramification exponent and
unit correction for this local map are both one. -/
theorem localRingHom_taylorEquiv_X_sub_C (a : k) :
    Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
        (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
        (span_X_sub_C_eq_comap_taylorEquiv a)
        (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X])))
          (X - C a)) =
      algebraMap k[X] (localRingAtOrigin k) X := by
  rw [localRingHom_taylorEquiv_algebraMap]
  simp only [map_sub, taylor_X, taylor_C, add_sub_cancel_right]

/-- The actual localized equivalence has the actual local Taylor homomorphism
as its underlying ring map. -/
theorem localRingEquiv_taylorEquiv_toRingHom (a : k) :
    (Localization.localRingEquiv (Ideal.span ({X - C a} : Set k[X]))
      (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingEquiv
      (span_X_sub_C_eq_comap_taylorEquiv a)).toRingHom =
    Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
      (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
      (span_X_sub_C_eq_comap_taylorEquiv a) := rfl

end Polynomial

namespace RatFunc

/-- The native rational Taylor map is exactly the underlying map of the native
fraction-field equivalence induced by the polynomial Taylor equivalence. -/
theorem ringEquivOfRingEquiv_taylorEquiv_toRingHom (a : k) :
    (IsFractionRing.ringEquivOfRingEquiv (K := RatFunc k) (L := RatFunc k)
      (Polynomial.taylorEquiv a).toRingEquiv).toRingHom =
      (laurent a).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := k[X])
  intro p
  change IsFractionRing.ringEquivOfRingEquiv (K := RatFunc k) (L := RatFunc k)
      (Polynomial.taylorEquiv a).toRingEquiv (algebraMap k[X] (RatFunc k) p) =
    laurent a (algebraMap k[X] (RatFunc k) p)
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, laurent_algebraMap]
  rfl

/-- The original rational Taylor map commutes with the actual local map from
the linear place `a` to the origin. -/
theorem laurent_comp_algebraMap_localizationAtPrime_X_sub_C (a : k) :
    (laurent a).toRingHom.comp
        (algebraMap (Localization.AtPrime (Ideal.span ({Polynomial.X - Polynomial.C a} : Set k[X])))
          (RatFunc k)) =
      (algebraMap (localRingAtOrigin k) (RatFunc k)).comp
        (Localization.localRingHom (Ideal.span ({Polynomial.X - Polynomial.C a} : Set k[X]))
          (Ideal.span ({Polynomial.X} : Set k[X])) (taylorEquiv a).toRingHom
          (span_X_sub_C_eq_comap_taylorEquiv a)) := by
  apply IsLocalization.ringHom_ext
    (Ideal.span ({Polynomial.X - Polynomial.C a} : Set k[X])).primeCompl
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply k[X]
      (Localization.AtPrime (Ideal.span ({Polynomial.X - Polynomial.C a} : Set k[X]))) (RatFunc k),
    localRingHom_taylorEquiv_algebraMap,
    ← IsScalarTower.algebraMap_apply k[X] (localRingAtOrigin k) (RatFunc k)]
  exact laurent_algebraMap a p

/-- The generic square on an arbitrary element of the original local ring.
This supplies the exact map compatibility used by DVR residue naturality. -/
theorem laurent_algebraMap_localizationAtPrime_X_sub_C (a : k)
    (x : Localization.AtPrime (Ideal.span ({Polynomial.X - Polynomial.C a} : Set k[X]))) :
    laurent a
        (algebraMap (Localization.AtPrime (Ideal.span ({Polynomial.X - Polynomial.C a} : Set k[X])))
          (RatFunc k) x) =
      algebraMap (localRingAtOrigin k) (RatFunc k)
        (Localization.localRingHom (Ideal.span ({Polynomial.X - Polynomial.C a} : Set k[X]))
          (Ideal.span ({Polynomial.X} : Set k[X])) (taylorEquiv a).toRingHom
          (span_X_sub_C_eq_comap_taylorEquiv a) x) :=
  RingHom.congr_fun (laurent_comp_algebraMap_localizationAtPrime_X_sub_C a) x

/-- The same generic square with the native local equivalence, rather than its
underlying local homomorphism. -/
theorem laurent_comp_algebraMap_localRingEquiv_taylorEquiv (a : k) :
    (laurent a).toRingHom.comp
        (algebraMap (Localization.AtPrime (Ideal.span ({Polynomial.X - Polynomial.C a} : Set k[X])))
          (RatFunc k)) =
      (algebraMap (localRingAtOrigin k) (RatFunc k)).comp
        (Localization.localRingEquiv (Ideal.span ({Polynomial.X - Polynomial.C a} : Set k[X]))
          (Ideal.span ({Polynomial.X} : Set k[X])) (taylorEquiv a).toRingEquiv
          (span_X_sub_C_eq_comap_taylorEquiv a)).toRingHom := by
  rw [localRingEquiv_taylorEquiv_toRingHom]
  exact laurent_comp_algebraMap_localizationAtPrime_X_sub_C a

end RatFunc

namespace Stacks.Chow

/-- On original polynomials, the native residue map of local Taylor translation
is evaluation at `a` through the existing origin residue equivalence. -/
theorem residueField_map_taylorEquiv_algebraMap (a : k) (p : k[X]) :
    ResidueField.map
        (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
          (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
          (span_X_sub_C_eq_comap_taylorEquiv a))
        (residue (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X])))
          (algebraMap k[X] (Localization.AtPrime (Ideal.span ({X - C a} : Set k[X]))) p)) =
      residueFieldAtOriginEquiv k (p.eval a) := by
  rw [ResidueField.map_residue, localRingHom_taylorEquiv_algebraMap,
    residue_algebraMap_polynomial, taylor_coeff_zero]
  rfl

/-- The actual quotient-to-residue comparison, local Taylor map, and inverse
origin residue equivalence compose to the native quotient evaluation at `a`. -/
theorem residueField_taylorEquiv_quotient_square (a : k) :
    (residueFieldAtOriginEquiv k).symm.toRingHom.comp
        ((ResidueField.map
          (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
            (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
            (span_X_sub_C_eq_comap_taylorEquiv a))).comp
          (quotientRingEquivResidueField (Ideal.span ({X - C a} : Set k[X]))).toRingHom) =
      (quotientSpanXSubCAlgEquiv a).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change (residueFieldAtOriginEquiv k).symm
      (ResidueField.map
        (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
          (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
          (span_X_sub_C_eq_comap_taylorEquiv a))
        (quotientRingEquivResidueField (Ideal.span ({X - C a} : Set k[X]))
          (Ideal.Quotient.mk _ p))) = p.eval a
  rw [← residue_algebraMap_eq_quotientRingEquivResidueField,
    residueField_map_taylorEquiv_algebraMap, RingEquiv.symm_apply_apply]

/-- The residue-field dictionary starting in the actual residue field at the
linear place. The right side is the native polynomial quotient dictionary
followed by the native evaluation equivalence, with no assumed square. -/
theorem residueFieldAtOriginEquiv_symm_comp_residueField_map_taylorEquiv (a : k) :
    (residueFieldAtOriginEquiv k).symm.toRingHom.comp
        (ResidueField.map
          (Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
            (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
            (span_X_sub_C_eq_comap_taylorEquiv a))) =
      (quotientSpanXSubCAlgEquiv a).toRingHom.comp
        (quotientRingEquivResidueField
          (Ideal.span ({X - C a} : Set k[X]))).symm.toRingHom := by
  apply RingHom.ext
  intro z
  let e := quotientRingEquivResidueField (Ideal.span ({X - C a} : Set k[X]))
  let f := Localization.localRingHom (Ideal.span ({X - C a} : Set k[X]))
    (Ideal.span ({X} : Set k[X])) (taylorEquiv a).toRingHom
    (span_X_sub_C_eq_comap_taylorEquiv a)
  obtain ⟨x, rfl⟩ := e.surjective z
  have h : (residueFieldAtOriginEquiv k).symm (ResidueField.map f (e x)) =
      quotientSpanXSubCAlgEquiv a x :=
    RingHom.congr_fun (residueField_taylorEquiv_quotient_square a) x
  change (residueFieldAtOriginEquiv k).symm (ResidueField.map f (e x)) =
    quotientSpanXSubCAlgEquiv a (e.symm (e x))
  exact h.trans (congrArg (quotientSpanXSubCAlgEquiv a) (e.symm_apply_apply x)).symm

end Stacks.Chow

end
