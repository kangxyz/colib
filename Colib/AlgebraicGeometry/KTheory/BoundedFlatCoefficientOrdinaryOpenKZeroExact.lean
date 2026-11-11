/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedKValue
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenCofinality
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectWaldhausen
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.EquivalenceJoint
public import Colib.KTheory.Waldhausen.Cofinality.GeneralKZeroValue
public import Colib.KTheory.Waldhausen.GrothendieckComparison.AsSmall


/-!
# Honest K-zero exactness of the original global C/F/G section maps

The original native fine evaluation equivalence transports actual bounded-flat
joint data. Its quotient grading therefore has an injective original coarse
value map. The accepted grading lift and original perfect evaluation identify
the composite of that value with q as the unchanged raw-perfect image quotient.

Original C/F evaluation and the original r square transport the algebraic
quotient's exactness, rather than assuming a K-zero image condition. Compactness
of the open suffices for q-zero surjectivity; compactness of both endpoints
suffices for image equals kernel. Quasi-separatedness is used only to combine
these facts with the separate global injectivity of r.
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
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:47"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
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
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:75"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
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

@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:87"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
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

@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:102"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
private theorem multiplicativeQuotient_surjective {B : Type (u + 1)}
    [AddCommGroup B] (H : AddSubgroup B) :
    Function.Surjective (QuotientAddGroup.mk' H).toMultiplicative := by
  intro y
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective H y.toAdd
  exact ⟨Multiplicative.ofAdd x, congrArg Multiplicative.ofAdd hx⟩

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation

omit [IsOpenImmersion f.left] in
/-- Original perfect evaluation retains the inverse classical K-zero comparison on all classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:145"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
theorem boundedAboveFlatCoefficientFullOpenPerfectKEquiv_grothendieck [CompactSpace P.left]
    (a : Under R) :
    (grothendieckKZeroEquivOfAsSmall
      (RingedSpace.perfectComplexesWaldhausen (space (op P,
        a)).toRingedSpace)).symm.toMonoidHom.comp
        (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a 0).toMonoidHom =
      (AlgebraicGrothendieck.map (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
        (boundedAboveFlatCoefficientFullOpenPerfectEvaluation f a)
        (boundedAboveFlatCoefficientFullOpenPerfectEvaluation_exact f a)).toMultiplicative.comp
          (grothendieckKZeroEquivOfAsSmall
            (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))).symm.toMonoidHom := by
  apply kZero_hom_ext (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
  intro S
  change (grothendieckKZeroEquivOfAsSmall (RingedSpace.perfectComplexesWaldhausen (space (op P,
    a)).toRingedSpace)).symm
    (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a 0
      ((boundedAboveFlatCoefficientSectionWaldhausen (op P, a)).kZeroObjectClass S)) =
    (AlgebraicGrothendieck.map (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
      (boundedAboveFlatCoefficientFullOpenPerfectEvaluation f a)
      (boundedAboveFlatCoefficientFullOpenPerfectEvaluation_exact f a)).toMultiplicative
        ((grothendieckKZeroEquivOfAsSmall
          (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))).symm
            ((boundedAboveFlatCoefficientSectionWaldhausen (op P, a)).kZeroObjectClass S))
  rw [boundedAboveFlatCoefficientFullOpenPerfectKEquiv_objectClass,
    grothendieckKZeroEquivOfAsSmall_symm_objectClass,
    grothendieckKZeroEquivOfAsSmall_symm_objectClass]
  exact congrArg Multiplicative.ofAdd
    (map_objectClass (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
      (boundedAboveFlatCoefficientFullOpenPerfectEvaluation f a)
      (boundedAboveFlatCoefficientFullOpenPerfectEvaluation_exact f a) S).symm

/-- The original q followed by its actual coarse value is the raw quotient after evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:175"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
theorem boundedAboveFlatCoefficientOpenKZeroValueMap_comp_grading [CompactSpace P.left]
    (a : Under R) :
    (boundedAboveFlatCoefficientOpenKZeroValueMap f a).comp
        (KMap (Fibration.changeWeak_exact (boundedAboveFlatCoefficientFullOpenGrading f a).nested)
          0) =
      (QuotientAddGroup.mk'
        (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (schemeMap f a))
          (perfectComplexesRestrictOpenImmersion (schemeMap f a))
          (perfectOpenRestrict_isExact (schemeMap f a))).range).toMultiplicative.comp
        ((grothendieckKZeroEquivOfAsSmall
          (RingedSpace.perfectComplexesWaldhausen (space (op P,
            a)).toRingedSpace)).symm.toMonoidHom.comp
            (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a 0).toMonoidHom) := by
  change ((boundedAboveFlatCoefficientFullOpenGrading f a).coarseKZeroValueMap
    (boundedAboveFlatCoefficientSectionJointData (op P,
      a)).reflexiveAsSmall.sourceFactorization).comp
      _ = _
  rw [Cofinality.Grading.coarseKZeroValueMap_comp_changeWeak]
  have hcomp {A B G H : Type (u + 1)} [AddCommGroup A] [AddCommGroup B]
      [AddCommGroup G] [_root_.Group H]
      {l : A →+ G} {q : B →+ G} {m : A →+ B}
      {e : H →* Multiplicative A} {k : H →* Multiplicative B}
      (hl : l = q.comp m) (hk : k = m.toMultiplicative.comp e) :
      l.toMultiplicative.comp e = q.toMultiplicative.comp k := by
    rw [hl, hk]
    rfl
  exact hcomp (boundedAboveFlatCoefficientFullOpenGrading_lift f a)
    (boundedAboveFlatCoefficientFullOpenPerfectKEquiv_grothendieck f a)

/-- The unchanged actual q map is surjective on K-zero; only the original open is compact. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:195"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
theorem boundedAboveFlatCoefficientOpenGrading_KMap_zero_surjective [CompactSpace P.left]
    (a : Under R) :
    Function.Surjective
      (KMap (Fibration.changeWeak_exact (boundedAboveFlatCoefficientFullOpenGrading f a).nested)
        0) := by
  let d := boundedAboveFlatCoefficientFullOpenGrading f a
  let q := KMap (Fibration.changeWeak_exact d.nested) 0
  let m := AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (schemeMap f a))
    (perfectComplexesRestrictOpenImmersion (schemeMap f a))
    (perfectOpenRestrict_isExact (schemeMap f a))
  let e := (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a 0).trans
    (grothendieckKZeroEquivOfAsSmall (RingedSpace.perfectComplexesWaldhausen (space (op P,
      a)).toRingedSpace)).symm
  exact surjective_of_quotient_comparison q (QuotientAddGroup.mk' m.range).toMultiplicative e
    (boundedAboveFlatCoefficientOpenKZeroValueMap f a)
    (boundedAboveFlatCoefficientOpenKZeroValueMap_injective f a)
    (fun x => DFunLike.congr_fun (boundedAboveFlatCoefficientOpenKZeroValueMap_comp_grading f a) x)
    (multiplicativeQuotient_surjective m.range)

/-- The original r image equals the kernel of the actual q on honest K-zero classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:212"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
theorem boundedAboveFlatCoefficientOpenGrading_KMap_zero_range_ker
    [CompactSpace P.left] [CompactSpace Q.left] (a : Under R) :
    (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) 0).range =
      (KMap (Fibration.changeWeak_exact
        (boundedAboveFlatCoefficientFullOpenGrading f a).nested) 0).ker := by
  let W := perfectOpenWeakWaldhausen (schemeMap f a)
  let V := RingedSpace.perfectComplexesWaldhausen (space (op P, a)).toRingedSpace
  let I := perfectComplexesRestrictOpenImmersion (schemeMap f a)
  let hI := perfectOpenRestrict_isExact (schemeMap f a)
  let m := AlgebraicGrothendieck.map W I hI
  let r := KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) 0
  let q := KMap (Fibration.changeWeak_exact (boundedAboveFlatCoefficientFullOpenGrading f
    a).nested) 0
  let eW := (boundedAboveFlatCoefficientOpenPerfectKEquiv f a 0).trans
    (grothendieckKZeroEquivOfAsSmall W).symm
  let eV := (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a 0).trans
    (grothendieckKZeroEquivOfAsSmall V).symm
  have hr (x : (boundedAboveFlatCoefficientOpenWaldhausen f a).K 0) :
      eV (r x) = m.toMultiplicative (eW x) := by
    change (grothendieckKZeroEquivOfAsSmall V).symm
      (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a 0 (r x)) = _
    rw [boundedAboveFlatCoefficientOpenRestriction_perfectKComparison]
    exact grothendieckKZeroEquivOfAsSmall_symm_natural W V I hI
      (boundedAboveFlatCoefficientOpenPerfectKEquiv f a 0 x)
  exact range_ker_of_exact_comparison r q m.toMultiplicative
    (QuotientAddGroup.mk' m.range).toMultiplicative eW eV
    (boundedAboveFlatCoefficientOpenKZeroValueMap f a)
    (boundedAboveFlatCoefficientOpenKZeroValueMap_injective f a) hr
    (fun x => DFunLike.congr_fun (boundedAboveFlatCoefficientOpenKZeroValueMap_comp_grading f a) x)
    (multiplicativeQuotient_range_ker m)

/-- The actual original r/q Model arrows form the honest short exact K-zero tail. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenKZeroExact.lean:243"
  "adaptation" "Original ordinary joint cylinders, injective K-zero value and actual r/q exactness"]
theorem boundedAboveFlatCoefficientOpenModel_KZero_exact [CompactSpace P.left]
    [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] (a : Under R) :
    Function.Injective (KMap (boundedAboveFlatCoefficientOpenRestrictionModelMap f a).hom.isExact
      0) ∧
      (KMap (boundedAboveFlatCoefficientOpenRestrictionModelMap f a).hom.isExact 0).range =
        (KMap (boundedAboveFlatCoefficientOpenGradingModelMap f a).hom.isExact 0).ker ∧
      Function.Surjective (KMap (boundedAboveFlatCoefficientOpenGradingModelMap f a).hom.isExact
        0) :=
  ⟨boundedAboveFlatCoefficientOpenRestriction_KMap_zero_injective f a,
    boundedAboveFlatCoefficientOpenGrading_KMap_zero_range_ker f a,
    boundedAboveFlatCoefficientOpenGrading_KMap_zero_surjective f a⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0594"]
  boundedAboveFlatCoefficientOpenModel_KZero_exact

attribute [colib_tag "COL-0594"]
  boundedAboveFlatCoefficientOpenGrading_KMap_zero_range_ker

attribute [colib_tag "COL-0594"]
  boundedAboveFlatCoefficientOpenGrading_KMap_zero_surjective

end AlgebraicGeometry.Scheme.Modules
