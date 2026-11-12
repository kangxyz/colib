/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedKGroups
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenCofinality
public import Colib.KTheory.Waldhausen.GrothendieckComparison.AsSmall


/-!
# Honest K-zero exactness of the actual supported coefficient r_Z and q_Z

Actual supported bounded-flat joint cylinders transport through the original
supported evaluation equivalence. They prove positive graded K-vanishing and
injectivity of the same coarse K-zero value. The actual supported grading lift
and native perfect evaluation identify q_Z with the original raw quotient.

The original supported restriction square proves image(r_Z0) = kernel(q_Z0).
Compact P suffices for q_Z0 surjectivity; compact P and Q suffice for the image
identity. Only the combined injective exact tail uses quasi-separated Q and a
compact auxiliary support complement T, through supported cofinality.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules

section QuotientTransport
variable {A B C A' B' C' : Type (u + 1)}
  [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']

/-- Original image-kernel exactness transports through actual endpoint equivalences. -/
private theorem range_ker_of_exact_comparison (r : A →* B) (q : B →* C)
    (r' : A' →* B') (q' : B' →* C') (eA : A ≃* A') (eB : B ≃* B')
    (c : C →* C') (hc : Function.Injective c)
    (hr : ∀ x, eB (r x) = r' (eA x)) (hq : ∀ x, c (q x) = q' (eB x))
    (he : r'.range = q'.ker) : r.range = q.ker := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    change q (r w) = 1
    apply hc
    rw [map_one, hq, hr]
    have hm : r' (eA w) ∈ q'.ker := by
      rw [← he]
      exact ⟨eA w, rfl⟩
    exact hm
  · intro hx
    change q x = 1 at hx
    have hm : eB x ∈ r'.range := by
      rw [he]
      change q' (eB x) = 1
      rw [← hq, hx, map_one]
    obtain ⟨z, hz⟩ := hm
    refine ⟨eA.symm z, ?_⟩
    apply eB.injective
    rw [hr, MulEquiv.apply_symm_apply]
    exact hz

/-- Quotient surjectivity transfers through actual evaluation and an injective value map. -/
private theorem surjective_of_quotient_comparison (q : B →* C) (q' : B' →* C')
    (eB : B ≃* B') (c : C →* C') (hc : Function.Injective c)
    (hq : ∀ x, c (q x) = q' (eB x)) (hs : Function.Surjective q') :
    Function.Surjective q := by
  intro y
  obtain ⟨z, hz⟩ := hs (c y)
  refine ⟨eB.symm z, hc ?_⟩
  rw [hq, MulEquiv.apply_symm_apply]
  exact hz

end QuotientTransport

private theorem multiplicativeQuotient_range_ker {A B : Type (u + 1)}
    [AddCommGroup A] [AddCommGroup B] (m : A →+ B) :
    m.toMultiplicative.range = (QuotientAddGroup.mk' m.range).toMultiplicative.ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change Multiplicative.ofAdd ((QuotientAddGroup.mk' m.range) (m a.toAdd)) = 1
    apply congrArg Multiplicative.ofAdd
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨a.toAdd, rfl⟩
  · intro hx
    have hz : (QuotientAddGroup.mk' m.range) x.toAdd = 0 :=
      congrArg Multiplicative.toAdd hx
    obtain ⟨a, ha⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz
    exact ⟨Multiplicative.ofAdd a, congrArg Multiplicative.ofAdd ha⟩

private theorem multiplicativeQuotient_surjective {B : Type (u + 1)}
    [AddCommGroup B] (H : AddSubgroup B) :
    Function.Surjective (QuotientAddGroup.mk' H).toMultiplicative := by
  intro y
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective H y.toAdd
  exact ⟨Multiplicative.ofAdd x, congrArg Multiplicative.ofAdd hx⟩

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

omit [IsOpenImmersion f.left] in
/-- Original perfect evaluation retains the inverse algebraic K-zero comparison on all classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenKZeroExact.lean:150"
  "adaptation" "Original supported K-zero image/kernel and actual quotient surjectivity"]
theorem boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv_grothendieck [CompactSpace P.left]
    (a : Under R) :
    (grothendieckKZeroEquivOfAsSmall
      (perfectSupportedWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)).symm.toMonoidHom.comp
        (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0).toMonoidHom =
      (AlgebraicGrothendieck.map (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
        (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a)
        (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation_exact
          f T a)).toMultiplicative.comp
          (grothendieckKZeroEquivOfAsSmall
            (boundedAboveFlatCoefficientSupportedSectionWaldhausen
              (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)).symm.toMonoidHom := by
  apply kZero_hom_ext (boundedAboveFlatCoefficientSupportedSectionWaldhausen
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
  intro S
  change (grothendieckKZeroEquivOfAsSmall (perfectSupportedWaldhausen
    (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)).symm
    (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0
      ((boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).kZeroObjectClass S)) =
    (AlgebraicGrothendieck.map (boundedAboveFlatCoefficientSupportedSectionWaldhausen
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
      (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a)
      (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation_exact f T a)).toMultiplicative
        ((grothendieckKZeroEquivOfAsSmall
          (boundedAboveFlatCoefficientSupportedSectionWaldhausen
            (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)).symm
            ((boundedAboveFlatCoefficientSupportedSectionWaldhausen
              (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).kZeroObjectClass S))
  rw [boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv_objectClass,
    grothendieckKZeroEquivOfAsSmall_symm_objectClass,
    grothendieckKZeroEquivOfAsSmall_symm_objectClass]
  exact congrArg Multiplicative.ofAdd
    (map_objectClass (boundedAboveFlatCoefficientSupportedSectionWaldhausen
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
      (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a)
      (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation_exact f T a) S).symm

private theorem toMultiplicative_comp_of_lift
    {A B G H : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup G] [_root_.Group H]
    {l : A →+ G} {q : B →+ G} {m : A →+ B}
    {e : H →* Multiplicative A} {k : H →* Multiplicative B}
    (hl : l = q.comp m) (hk : k = m.toMultiplicative.comp e) :
    l.toMultiplicative.comp e = q.toMultiplicative.comp k := by
  rw [hl, hk]
  rfl

/-- The original q followed by its actual coarse value is the raw quotient after evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenKZeroExact.lean:200"
  "adaptation" "Original supported K-zero image/kernel and actual quotient surjectivity"]
theorem boundedAboveFlatCoefficientSupportedOpenKZeroValueMap_comp_grading [CompactSpace P.left]
    (a : Under R) :
    (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap f T a).comp
        (KMap (Fibration.changeWeak_exact
          (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).nested) 0) =
      (QuotientAddGroup.mk'
        (AlgebraicGrothendieck.map (perfectSupportedOpenWeakWaldhausen (schemeMap f a)
          (boundedAboveFlatCoefficientSupportOpen Q T a))
          (perfectSupportedRestrict (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a))
          (perfectSupportedOpenRestrict_waldhausenExact (schemeMap f a)
            (boundedAboveFlatCoefficientSupportOpen Q T a))).range).toMultiplicative.comp
        ((grothendieckKZeroEquivOfAsSmall
          (perfectSupportedWaldhausen
            (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)).symm.toMonoidHom.comp
            (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0).toMonoidHom) := by
  change ((boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseKZeroValueMap
    (boundedAboveFlatCoefficientSupportedSectionJointData
      (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι).reflexiveAsSmall.sourceFactorization).comp
      _ = _
  rw [Cofinality.Grading.coarseKZeroValueMap_comp_changeWeak]
  exact toMultiplicative_comp_of_lift
    (boundedAboveFlatCoefficientSupportedFullOpenGrading_lift f T a)
    (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv_grothendieck f T a)

/-- The unchanged actual q map is surjective on K-zero; only the original open is compact. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenKZeroExact.lean:225"
  "adaptation" "Original supported K-zero image/kernel and actual quotient surjectivity"]
theorem boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_surjective [CompactSpace P.left]
    (a : Under R) :
    Function.Surjective
      (KMap (Fibration.changeWeak_exact
        (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).nested) 0) := by
  let d := boundedAboveFlatCoefficientSupportedFullOpenGrading f T a
  let q := KMap (Fibration.changeWeak_exact d.nested) 0
  let m := AlgebraicGrothendieck.map (perfectSupportedOpenWeakWaldhausen (schemeMap f a)
          (boundedAboveFlatCoefficientSupportOpen Q T a))
    (perfectSupportedRestrict (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a))
      (perfectSupportedOpenRestrict_waldhausenExact (schemeMap f a)
            (boundedAboveFlatCoefficientSupportOpen Q T a))
  let e := (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0).trans
    (grothendieckKZeroEquivOfAsSmall (perfectSupportedWaldhausen
      (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)).symm
  exact surjective_of_quotient_comparison q (QuotientAddGroup.mk' m.range).toMultiplicative e
    (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap f T a)
    (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap_injective f T a)
    (fun x ↦ DFunLike.congr_fun
      (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap_comp_grading f T a) x)
    (multiplicativeQuotient_surjective m.range)

/-- The original r image equals the kernel of the actual q on honest K-zero classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenKZeroExact.lean:248"
  "adaptation" "Original supported K-zero image/kernel and actual quotient surjectivity"]
theorem boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_range_ker
    [CompactSpace P.left] [CompactSpace Q.left] (a : Under R) :
    (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) 0).range =
      (KMap (Fibration.changeWeak_exact
        (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).nested) 0).ker := by
  let W := perfectSupportedOpenWeakWaldhausen (schemeMap f a)
          (boundedAboveFlatCoefficientSupportOpen Q T a)
  let V := perfectSupportedWaldhausen (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι
  let I := perfectSupportedRestrict (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a)
  let hI := perfectSupportedOpenRestrict_waldhausenExact (schemeMap f a)
            (boundedAboveFlatCoefficientSupportOpen Q T a)
  let m := AlgebraicGrothendieck.map W I hI
  let r := KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) 0
  let q := KMap (Fibration.changeWeak_exact
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).nested) 0
  let eW := (boundedAboveFlatCoefficientSupportedOpenPerfectKEquiv f T a 0).trans
    (grothendieckKZeroEquivOfAsSmall W).symm
  let eV := (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0).trans
    (grothendieckKZeroEquivOfAsSmall V).symm
  have hr (x : (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).K 0) :
      eV (r x) = m.toMultiplicative (eW x) := by
    change (grothendieckKZeroEquivOfAsSmall V).symm
      (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0 (r x)) = _
    rw [boundedAboveFlatCoefficientSupportedOpenRestriction_perfectKComparison]
    exact grothendieckKZeroEquivOfAsSmall_symm_natural W V I hI
      (boundedAboveFlatCoefficientSupportedOpenPerfectKEquiv f T a 0 x)
  exact range_ker_of_exact_comparison r q m.toMultiplicative
    (QuotientAddGroup.mk' m.range).toMultiplicative eW eV
    (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap f T a)
    (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap_injective f T a) hr
    (fun x ↦ DFunLike.congr_fun
      (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap_comp_grading f T a) x)
    (multiplicativeQuotient_range_ker m)

/-- The actual original r/q Model arrows form the honest short exact K-zero tail. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenKZeroExact.lean:283"
  "adaptation" "Original supported K-zero image/kernel and actual quotient surjectivity"]
theorem boundedAboveFlatCoefficientSupportedOpenModel_KZero_exact [CompactSpace P.left]
    [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] [CompactSpace T] (a : Under R) :
    Function.Injective
      (KMap (boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a).hom.isExact 0) ∧
      (KMap (boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a).hom.isExact
        0).range =
        (KMap (boundedAboveFlatCoefficientSupportedOpenGradingModelMap f T a).hom.isExact 0).ker ∧
      Function.Surjective
        (KMap (boundedAboveFlatCoefficientSupportedOpenGradingModelMap f T a).hom.isExact 0) :=
  ⟨boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_zero_injective f T a,
    boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_range_ker f T a,
    boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_surjective f T a⟩

end AlgebraicGeometry.Scheme.Modules


namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0589"]
  boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_surjective

attribute [colib_tag "COL-0589"]
  boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_range_ker

attribute [colib_tag "COL-0589"]
  boundedAboveFlatCoefficientSupportedOpenModel_KZero_exact

end AlgebraicGeometry.Scheme.Modules
