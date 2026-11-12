/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ParameterGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineInfinity

/-! # Local equations of the original principal family

The original boundary unit becomes the literal interpolation on an affine chart.
Adapted from `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/PolynomialFamily/`
`PrincipalFamilyLocalFraction.lean` at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped Polynomial

universe u

namespace AlgebraicGeometry

local instance integralNonemptyTop {D : Scheme.{u}} [IsIntegral D] :
    Nonempty (⊤ : D.Opens) := ⟨⟨genericPoint D, Opens.mem_top _⟩⟩

local instance openImageNonempty {D E : Scheme.{u}} (i : D ⟶ E) [IsOpenImmersion i]
    (U : D.Opens) [Nonempty U] : Nonempty (i ''ᵁ U) := by
  obtain ⟨x, hx⟩ := ‹Nonempty U›
  exact ⟨⟨i x, ⟨x, hx, rfl⟩⟩⟩

local instance dominantIntegralOpen {D E : Scheme.{u}} [IsIntegral D] [IsIntegral E]
    (i : D ⟶ E) [IsOpenImmersion i] : IsDominant i :=
  ((tfae_isDominant_of_isIntegral i).out 1 2).mpr (genericPoint_eq_of_isOpenImmersion i)

namespace Scheme.Hom

variable {D E : Scheme.{u}} [IsIntegral D] [IsIntegral E] (i : D ⟶ E) [IsDominant i]

/-- The germ of a global section pulls back to the germ of its actual pullback. -/
theorem dominantFunctionFieldMap_globalSection (s : Γ(E, ⊤)) :
    dominantFunctionFieldMap i (sectionRationalFunction s) =
      sectionRationalFunction (i.appTop s) :=
  (dominantFunctionFieldMap_germToFunctionField_of_mem i (genericPoint D)
    ⊤ (Opens.mem_top _) ⊤ (Opens.mem_top _) le_top s).trans
      (congrArg (D.germToFunctionField ⊤)
        (ConcreteCategory.congr_hom (Scheme.Hom.appLE_eq_app i (U := ⊤)) s))

/-- For an open immersion the map on rational sections uses the actual open isomorphism. -/
theorem dominantFunctionFieldMap_appIso_inv [IsOpenImmersion i]
    (U : D.Opens) [Nonempty U] (s : Γ(D, U)) :
    dominantFunctionFieldMap i (E.germToFunctionField (i ''ᵁ U) ((i.appIso U).inv s)) =
      D.germToFunctionField U s := by
  obtain ⟨x, hx⟩ := ‹Nonempty U›
  have hle : U ≤ i ⁻¹ᵁ i ''ᵁ U := (i.preimage_image_eq U).ge
  have hg := dominantFunctionFieldMap_germToFunctionField_of_mem i x
    (i ''ᵁ U) ⟨x, hx, rfl⟩ U hx hle ((i.appIso U).inv s)
  have ha := ConcreteCategory.congr_hom (i.appIso_inv_appLE hle) s
  change i.appLE (i ''ᵁ U) U hle ((i.appIso U).inv s) =
    D.presheaf.map (homOfLE (le_rfl : U ≤ U)).op s at ha
  have hId : homOfLE (le_rfl : U ≤ U) = 𝟙 U := Subsingleton.elim _ _
  rw [hId, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply] at ha
  exact hg.trans (congrArg (D.germToFunctionField U) ha)

end Scheme.Hom

namespace PrincipalFamilyUnitOpen

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil

variable {k : Type u} [Field k] {C W : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  [IsIntegral W] [IsLocallyNoetherian W] (p : C ⟶ Spec (.of k))
  (v : W ⟶ C) [IsOpenImmersion v]

/-- The actual rational germ specified by the original open section. -/
def openSectionGerm (f : Γ(W, ⊤)) : C.functionField :=
  C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f)

variable {D : Scheme.{u}} (q : D ⟶ Spec (.of k))

/-- The original denominator pulled through the whole polynomial projection. -/
def denominator (b : Γ(D, ⊤)) : Γ(parameterSpace q, ⊤) :=
  (projection q).appTop b

/-- The literal numerator of the family where the original unit is a fraction. -/
def numerator (a b : Γ(D, ⊤)) : Γ(parameterSpace q, ⊤) :=
  parameter q * denominator q a + (1 - parameter q) * denominator q b

@[simp] theorem denominator_endpoint (c : k) (b : Γ(D, ⊤)) :
    (endpoint q c).appTop (denominator q b) = b := by
  rw [denominator, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, endpoint_projection]
  rfl

@[simp] theorem numerator_zero (a b : Γ(D, ⊤)) :
    (endpoint q 0).appTop (numerator q a b) = b := by
  simp only [numerator, map_add, map_mul, map_sub, map_one, endpoint_parameter,
    map_zero, zero_mul, sub_zero, one_mul, zero_add, denominator_endpoint]

@[simp] theorem numerator_one (a b : Γ(D, ⊤)) :
    (endpoint q 1).appTop (numerator q a b) = a := by
  simp only [numerator, map_add, map_mul, map_sub, map_one, endpoint_parameter,
    one_mul, sub_self, zero_mul, add_zero, denominator_endpoint]

omit [IsIntegral C] [IsNoetherian C] in
/-- The parameter itself is unchanged under the original chart map. -/
theorem parameterMap_parameter (f : D ⟶ C) :
    (parameterMap p f).appTop (parameter p) = parameter (f ≫ p) := by
  unfold parameter
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, parameterMap_snd]

local instance projectionDominant : IsDominant (projection q) := by
  let : Surjective (projection q) :=
    ⟨fun x => ⟨endpoint q 0 x, congrArg (fun f : D ⟶ D => f x) (endpoint_projection q 0)⟩⟩
  infer_instance

/-- Pullback along the original whole chart realizes the prescribed interpolation. -/
theorem ambientRationalFunction_pullback_dominant (f : Γ(W, ⊤))
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)] :
    dominantFunctionFieldMap (parameterMap p v) (ambientRationalFunction p v f) =
      sectionRationalFunction (familySection (v ≫ p) f) := by
  unfold ambientRationalFunction ambientUnitSection ambientUnitOpen
  simp only [lineMap_eq_parameterMap]
  rw [Scheme.Hom.dominantFunctionFieldMap_appIso_inv, unitSection, sectionRationalFunction]
  exact (parameterSpace (v ≫ p)).presheaf.germ_res_apply _ _ _ _

/-- The original ambient unit is the polynomial in the pullback of the original rational germ. -/
theorem ambientRationalFunction_eq_polynomial (f : Γ(W, ⊤))
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)] :
    ambientRationalFunction p v f =
      sectionRationalFunction (parameter p) * dominantFunctionFieldMap (projection p)
        (openSectionGerm v f) + (1 - sectionRationalFunction (parameter p)) := by
  apply (dominantFunctionFieldMap (parameterMap p v)).injective
  rw [ambientRationalFunction_pullback_dominant]
  simp only [map_add, map_mul, map_sub, map_one,
    Scheme.Hom.dominantFunctionFieldMap_globalSection, parameterMap_parameter]
  have hcomp : (dominantFunctionFieldMap (parameterMap p v)).comp
      (dominantFunctionFieldMap (projection p)) =
        (dominantFunctionFieldMap (projection (v ≫ p))).comp (dominantFunctionFieldMap v) := by
    rw [← dominantFunctionFieldMap_comp, ← dominantFunctionFieldMap_comp]
    exact dominantFunctionFieldMap_congr _ _ (parameterMap_projection p v)
  rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply, openSectionGerm,
    Scheme.Hom.dominantFunctionFieldMap_appIso_inv]
  have hg := Scheme.Hom.dominantFunctionFieldMap_globalSection (projection (v ≫ p)) f
  change dominantFunctionFieldMap (projection (v ≫ p))
    ((W.germToFunctionField ⊤).hom f) = _ at hg
  rw [hg]
  simp only [familySection, sectionRationalFunction, map_add, map_mul, map_sub, map_one]

/-- The same interpolation on the original affine chart is its literal fraction. -/
theorem ambientRationalFunction_chart_fraction_dominant (f : Γ(W, ⊤))
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)]
    (U : C.Opens) [IsIntegral U.toScheme]
    (a b : Γ(U.toScheme, ⊤)) (hb : b ≠ 0)
    (hab : sectionRationalFunction a / sectionRationalFunction b =
      dominantFunctionFieldMap U.ι (openSectionGerm v f)) :
    dominantFunctionFieldMap (parameterMap p U.ι) (ambientRationalFunction p v f) =
      sectionRationalFunction (numerator (U.ι ≫ p) a b) /
        sectionRationalFunction (denominator (U.ι ≫ p) b) := by
  have hcomp : (dominantFunctionFieldMap (parameterMap p U.ι)).comp
      (dominantFunctionFieldMap (projection p)) =
        (dominantFunctionFieldMap (projection (U.ι ≫ p))).comp (dominantFunctionFieldMap U.ι) := by
    rw [← dominantFunctionFieldMap_comp, ← dominantFunctionFieldMap_comp]
    exact dominantFunctionFieldMap_congr _ _ (parameterMap_projection p U.ι)
  have hden : sectionRationalFunction (denominator (U.ι ≫ p) b) ≠ 0 := by
    rw [denominator, ← Scheme.Hom.dominantFunctionFieldMap_globalSection]
    have hb' : sectionRationalFunction b ≠ 0 :=
      (map_ne_zero_iff _ (U.toScheme.germToFunctionField_injective ⊤)).mpr hb
    exact (map_ne_zero_iff _ (dominantFunctionFieldMap (projection (U.ι ≫ p))).injective).mpr hb'
  rw [ambientRationalFunction_eq_polynomial]
  simp only [map_add, map_mul, map_sub, map_one,
    Scheme.Hom.dominantFunctionFieldMap_globalSection, parameterMap_parameter]
  rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply, ← hab, map_div₀,
    Scheme.Hom.dominantFunctionFieldMap_globalSection,
    Scheme.Hom.dominantFunctionFieldMap_globalSection]
  unfold sectionRationalFunction denominator at hden
  simp only [numerator, denominator, sectionRationalFunction, map_add, map_mul, map_sub, map_one]
  field_simp [hden]

end PrincipalFamilyUnitOpen

end AlgebraicGeometry
