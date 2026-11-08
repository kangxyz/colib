/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportRestrictionVanishing

/-!
# Exact open restriction with prescribed support

Literal termwise restriction carries support outside an arbitrary open to support
outside its actual inverse image. Both Waldhausen structures use native Stacks
perfectness, ambient monomorphisms and genuine quasi-isomorphisms.

Adapted from Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Restriction.lean
at c561118b7795eb9780be9ed391c3251d6a4d0afd. No compactness or separation is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Actual open restriction preserves the inverse-image support predicate. -/
theorem perfectSupported_restrict {K : CochainComplex X.Modules ℤ}
    (hK : perfectSupported T.ι K) :
    perfectSupported (j ⁻¹ᵁ T).ι
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  ⟨Complex.isPerfectComplex_restrictOpenImmersion j K hK.1,
    restrictAcyclic_preimage j T K hK.2⟩

/-- Literal restriction between the native supported full categories. -/
def perfectSupportedRestrict : (perfectSupported T.ι).FullSubcategory ⥤
    (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory :=
  (perfectSupported (j ⁻¹ᵁ T).ι).lift ((perfectSupported T.ι).ι ⋙
    (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => perfectSupported_restrict j T K.property)

@[simp] theorem perfectSupportedRestrict_obj (K : (perfectSupported T.ι).FullSubcategory) :
    ((perfectSupportedRestrict j T).obj K).obj =
      ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj := rfl

@[simp] theorem perfectSupportedRestrict_map {K L : (perfectSupported T.ι).FullSubcategory}
    (f : K ⟶ L) : ((perfectSupportedRestrict j T).map f).hom =
      ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom := rfl

/-- Actual supported restriction is exact for ambient Mono and QuasiIso. -/
theorem perfectSupportedRestrict_exact :
    Waldhausen.IsExact (perfectSupportedWaldhausen T.ι).cof
      (perfectSupportedWaldhausen T.ι).weq (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq (perfectSupportedRestrict j T) := by
  let F := (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)
  let P := perfectSupported T.ι
  let Q := perfectSupported (j ⁻¹ᵁ T).ι
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero Q.ι
    exact F.map_isZero ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
      (Waldhausen.complexes X.Modules) P (perfectSupported_cofibrationClosed T.ι)).zero hZ)
  · intro K L f hf
    change Mono (F.map f.hom)
    have : Mono (C := CochainComplex X.Modules ℤ) f.hom := hf
    infer_instance
  · intro K L f hf
    change QuasiIso (F.map f.hom)
    have : QuasiIso (C := X.Modules) f.hom := hf
    infer_instance
  · intro A B D Z i f g k hi h
    apply IsPushout.of_map_of_faithful Q.ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes X.Modules) P (perfectSupported_cofibrationClosed T.ι) hi h).map F

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0331",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Restriction.lean:53-65"
    "adaptation"
    "Native supported relative-open coarse model and actual maps, without fine-open comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedRestrict_exact
