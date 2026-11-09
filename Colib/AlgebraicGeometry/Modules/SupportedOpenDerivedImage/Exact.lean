/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Closure
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Subcategory

/-!
# The actual Waldhausen structure on the derived restriction image

Closure produces the structure on the full subcategory of actual chain complexes, with
ambient monomorphisms and quasi-isomorphisms. Inclusion and corestriction retain every
underlying map and are proved exact. The geometric roof input remains explicit.

Adapted from Quillen's `OpenDerivedImage/Exact.lean` and `OpenDerivedImage/Structure.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules]

instance : (complexObjects j T).IsClosedUnderIsomorphisms where
  of_iso e h := (complexObjects_iff_of_derivedIso j T (DerivedCategory.Q.mapIso e)).1 h

instance : (complexObjects j T).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (derivedObjects j T).prop_of_isZero (DerivedCategory.Q.map_isZero (isZero_zero _))⟩

/-- The original shifted complex remains in the image. -/
theorem complexObjects_shift {E : CochainComplex U.Modules ℤ}
    (hE : complexObjects j T E) (n : ℤ) : complexObjects j T (E⟦n⟧) := by
  have h : derivedObjects j T ((DerivedCategory.Q.obj E)⟦n⟧) :=
    (derivedObjects j T).le_shift _ _ hE
  exact (derivedObjects j T).prop_of_iso ((DerivedCategory.Q.commShiftIso n).app E).symm h

instance [Fact (HasDerivedRoofs j T)] :
    (abelianExactStructure (CochainComplex U.Modules ℤ)).IsExtensionClosed
      (complexObjects j T) where
  prop_middle := complexObjects_of_shortExact j T Fact.out

instance [Fact (HasDerivedRoofs j T)] : (complexObjects j T).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex U.Modules ℤ)).extensionClosed_finiteProducts
    (complexObjects j T)

/-- Every ambient pushout along a monomorphism has its actual apex in the image. -/
theorem cofibrationClosed (hroof : HasDerivedRoofs j T) :
    Waldhausen.CofibrationClosedSubcategory.Closed
      (Waldhausen.complexes U.Modules) (complexObjects j T) where
  zero_mem := (complexObjects j T).prop_zero
  pushout_mem hi h hA hB hD := by
    have : Mono _ := hi
    have hb : complexObjects j T (_ ⊞ _) := complexObjects_of_shortExact j T hroof
      (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact hB hD
    have hs : h.shortComplex.ShortExact :=
      { exact := h.exact_shortComplex
        mono_f := by dsimp [CommSq.shortComplex]; infer_instance
        epi_g := h.epi_shortComplex_g }
    exact complexObjects_quotient_of_shortExact j T hroof hs hA hb

/-- The image inherits actual ambient monomorphisms and quasi-isomorphisms. -/
def waldhausen (hroof : HasDerivedRoofs j T) : Waldhausen.Structure (Obj j T) :=
  Waldhausen.CofibrationClosedSubcategory.waldhausenStructure
    (Waldhausen.complexes U.Modules) (complexObjects j T) (cofibrationClosed j T hroof)

/-- Inclusion into the original perfect category is exact on the original maps. -/
theorem inclusion_isExact (hroof : HasDerivedRoofs j T) :
    Waldhausen.IsExact (waldhausen j T hroof).cof (waldhausen j T hroof).weq
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq (inclusion j T) where
  zero h := by
    apply IsZero.of_full_of_faithful_of_isZero
      (ObjectProperty.ι (perfectSupported (j ⁻¹ᵁ T).ι))
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_exact
      (Waldhausen.complexes U.Modules) (complexObjects j T) (cofibrationClosed j T hroof)).zero h
  cofibration _ h := h
  weak _ h := h
  pushout hi h := by
    apply IsPushout.of_map_of_faithful
      (ObjectProperty.ι (perfectSupported (j ⁻¹ᵁ T).ι))
    exact Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes U.Modules) (complexObjects j T) (cofibrationClosed j T hroof) hi h

/-- The inherited cofibration is exactly the original ambient perfect cofibration. -/
theorem inclusion_cof_iff (hroof : HasDerivedRoofs j T) {A B : Obj j T} (f : A ⟶ B) :
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof ((inclusion j T).map f) ↔
      (waldhausen j T hroof).cof f := Iff.rfl

/-- Restriction corestricts exactly, without replacing objects or chain maps. -/
theorem corestrict_isExact (hroof : HasDerivedRoofs j T) :
    Waldhausen.IsExact (perfectSupportedWaldhausen T.ι).cof
      (perfectSupportedWaldhausen T.ι).weq
      (waldhausen j T hroof).cof (waldhausen j T hroof).weq (corestrict j T) := by
  let F := (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)
  let P : ObjectProperty (CochainComplex X.Modules ℤ) :=
    perfectSupported T.ι
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero (complexObjects j T).ι
    exact F.map_isZero
      ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
        (Waldhausen.complexes X.Modules) P
        (perfectSupported_cofibrationClosed T.ι)).zero hZ)
  · intro K L f hf
    change Mono (F.map f.hom)
    have : Mono (C := CochainComplex X.Modules ℤ) f.hom := hf
    infer_instance
  · intro K L f hf
    change QuasiIso (F.map f.hom)
    have : QuasiIso (C := X.Modules) f.hom := hf
    infer_instance
  · intro A B D Z i f g k hi h
    apply IsPushout.of_map_of_faithful (complexObjects j T).ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes X.Modules) P
      (perfectSupported_cofibrationClosed T.ι) hi h).map F

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
