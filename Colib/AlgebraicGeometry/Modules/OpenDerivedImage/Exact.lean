/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Closure
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

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

instance : (complexObjects j).IsClosedUnderIsomorphisms where
  of_iso e h := (complexObjects_iff_of_derivedIso j (DerivedCategory.Q.mapIso e)).1 h

instance : (complexObjects j).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (derivedObjects j).prop_of_isZero (DerivedCategory.Q.map_isZero (isZero_zero _))⟩

/-- The original shifted complex remains in the image. -/
theorem complexObjects_shift {E : CochainComplex U.Modules ℤ}
    (hE : complexObjects j E) (n : ℤ) : complexObjects j (E⟦n⟧) := by
  have h : derivedObjects j ((DerivedCategory.Q.obj E)⟦n⟧) :=
    (derivedObjects j).le_shift _ _ hE
  exact (derivedObjects j).prop_of_iso ((DerivedCategory.Q.commShiftIso n).app E).symm h

instance [Fact (HasDerivedRoofs j)] :
    (abelianExactStructure (CochainComplex U.Modules ℤ)).IsExtensionClosed (complexObjects j) where
  prop_middle := complexObjects_of_shortExact j Fact.out

instance [Fact (HasDerivedRoofs j)] : (complexObjects j).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex U.Modules ℤ)).extensionClosed_finiteProducts
    (complexObjects j)

/-- Every ambient pushout along a monomorphism has its actual apex in the image. -/
theorem cofibrationClosed (hroof : HasDerivedRoofs j) :
    Waldhausen.CofibrationClosedSubcategory.Closed
      (Waldhausen.complexes U.Modules) (complexObjects j) where
  zero_mem := (complexObjects j).prop_zero
  pushout_mem hi h hA hB hD := by
    have : Mono _ := hi
    have hb : complexObjects j (_ ⊞ _) := complexObjects_of_shortExact j hroof
      (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact hB hD
    have hs : h.shortComplex.ShortExact :=
      { exact := h.exact_shortComplex
        mono_f := by dsimp [CommSq.shortComplex]; infer_instance
        epi_g := h.epi_shortComplex_g }
    exact complexObjects_quotient_of_shortExact j hroof hs hA hb

/-- The image inherits actual ambient monomorphisms and quasi-isomorphisms. -/
def waldhausen (hroof : HasDerivedRoofs j) : Waldhausen.Structure (Obj j) :=
  Waldhausen.CofibrationClosedSubcategory.waldhausenStructure
    (Waldhausen.complexes U.Modules) (complexObjects j) (cofibrationClosed j hroof)

/-- Inclusion into the original perfect category is exact on the original maps. -/
theorem inclusion_isExact (hroof : HasDerivedRoofs j) :
    Waldhausen.IsExact (waldhausen j hroof).cof (waldhausen j hroof).weq
      (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).weq (inclusion j) where
  zero h := by
    apply IsZero.of_full_of_faithful_of_isZero
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := U.toRingedSpace)))
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_exact
      (Waldhausen.complexes U.Modules) (complexObjects j) (cofibrationClosed j hroof)).zero h
  cofibration _ h := h
  weak _ h := h
  pushout hi h := by
    apply IsPushout.of_map_of_faithful
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := U.toRingedSpace)))
    exact Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes U.Modules) (complexObjects j) (cofibrationClosed j hroof) hi h

/-- The inherited cofibration is exactly the original ambient perfect cofibration. -/
theorem inclusion_cof_iff (hroof : HasDerivedRoofs j) {A B : Obj j} (f : A ⟶ B) :
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).cof ((inclusion j).map f) ↔
      (waldhausen j hroof).cof f := Iff.rfl

/-- Restriction corestricts exactly, without replacing objects or chain maps. -/
theorem corestrict_isExact (hroof : HasDerivedRoofs j) :
    Waldhausen.IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (waldhausen j hroof).cof (waldhausen j hroof).weq (corestrict j) := by
  let F := (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)
  let P : ObjectProperty (CochainComplex X.Modules ℤ) :=
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero (complexObjects j).ι
    exact F.map_isZero
      ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
        (Waldhausen.complexes X.Modules) P
        (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace)).zero hZ)
  · intro K L f hf
    change Mono (F.map f.hom)
    have : Mono (C := CochainComplex X.Modules ℤ) f.hom := hf
    infer_instance
  · intro K L f hf
    change QuasiIso (F.map f.hom)
    have : QuasiIso (C := X.Modules) f.hom := hf
    infer_instance
  · intro A B D T i f g k hi h
    apply IsPushout.of_map_of_faithful (complexObjects j).ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes X.Modules) P
      (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace) hi h).map F

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_tag "COL-0312",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Structure.lean"
    "adaptation"
    "Ambient monomorphisms and quasi-isomorphisms; exact corestriction given global-model roofs"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.waldhausen
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.inclusion_isExact
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.corestrict_isExact
