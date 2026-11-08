/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Exact
public import Colib.AlgebraicGeometry.Modules.PerfectOppositeJoint
public import Colib.CategoryTheory.Waldhausen.ComplexFunctor

/-! # Actual opposite structure on the honest restriction image

The original image category carries admissible epimorphisms on its literal opposite.
Actual kernel and cokernel membership identify these maps with ambient epis and monos.
The existing ambient-monomorphism Waldhausen structure stays unchanged. The only
geometric input is the explicitly displayed global-perfect-model roof property.

Implementation provenance: `OpenDerivedImage/Structure.lean:42-109` in Quillen's
`AlgebraicGeometry/PerfectComplexes` at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
universe u d

local instance (Z : Scheme.{u}) : HasFiniteBiproducts
    (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} Z.toRingedSpace) ℤ) :=
  Abelian.hasFiniteBiproducts
    (C := CochainComplex (StrictlyPerfect.OXMod.{u, u, u} Z.toRingedSpace) ℤ)

local instance (Z : Scheme.{u}) : HasFiniteBiproducts (CochainComplex Z.Modules ℤ) :=
  Abelian.hasFiniteBiproducts (C := CochainComplex Z.Modules ℤ)

local instance (Z : Scheme.{u}) : ObjectProperty.ContainsZero
    (IsPerfectComplex (X := Z.toRingedSpace)) :=
  isPerfectComplex_containsZero Z.toRingedSpace

local instance (Z : Scheme.{u}) : ObjectProperty.IsClosedUnderIsomorphisms
    (IsPerfectComplex (X := Z.toRingedSpace)) :=
  isPerfectComplex_closedUnderIsomorphisms Z.toRingedSpace

local instance (Z : Scheme.{u}) : (ExactCategory.abelianExactStructure
      (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} Z.toRingedSpace) ℤ)).IsExtensionClosed
    (IsPerfectComplex (X := Z.toRingedSpace)) :=
  isPerfectComplex_extensionClosed Z.toRingedSpace

local instance (Z : Scheme.{u}) : ObjectProperty.IsClosedUnderFiniteProducts
    (IsPerfectComplex (X := Z.toRingedSpace)) :=
  isPerfectComplex_closedUnderFiniteProducts Z.toRingedSpace

local instance (Z : Scheme.{u}) : HasFiniteBiproducts
    (ObjectProperty.FullSubcategory (IsPerfectComplex (X := Z.toRingedSpace))) :=
  ExactSubcategory.subcategoryHasFiniteBiproducts (IsPerfectComplex (X := Z.toRingedSpace))

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j)]

local instance : ObjectProperty.ContainsZero
    (show ObjectProperty (CochainComplex (StrictlyPerfect.OXMod.{u, u, u}
      U.toRingedSpace) ℤ) from complexObjects j) :=
  inferInstanceAs ((complexObjects j).ContainsZero)

local instance : ObjectProperty.IsClosedUnderIsomorphisms
    (show ObjectProperty (CochainComplex (StrictlyPerfect.OXMod.{u, u, u}
      U.toRingedSpace) ℤ) from complexObjects j) :=
  inferInstanceAs ((complexObjects j).IsClosedUnderIsomorphisms)

local instance : (abelianExactStructure (CochainComplex
      (StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) ℤ)).IsExtensionClosed
    (complexObjects j) :=
  inferInstanceAs ((abelianExactStructure (CochainComplex U.Modules ℤ)).IsExtensionClosed
    (complexObjects j))

local instance : ObjectProperty.IsClosedUnderFiniteProducts
    (show ObjectProperty (CochainComplex (StrictlyPerfect.OXMod.{u, u, u}
      U.toRingedSpace) ℤ) from complexObjects j) :=
  inferInstanceAs ((complexObjects j).IsClosedUnderFiniteProducts)


/-- Admissibility is exactly monicity of the original chain map. -/
theorem inflation_iff {K L : Obj j} (f : K ⟶ L) :
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j)).inflation f ↔ Mono f.hom := by
  constructor
  · rintro ⟨Q, p, w, hS⟩
    exact hS.mono_f
  · intro hf
    let : Mono f.hom := hf
    let S := ShortComplex.mk f.hom (cokernel.π f.hom) (cokernel.condition f.hom)
    have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact f.hom }
    exact ⟨⟨cokernel f.hom,
      complexObjects_quotient_of_shortExact j Fact.out hS K.property L.property⟩,
      ObjectProperty.homMk (cokernel.π f.hom),
      ObjectProperty.hom_ext _ (cokernel.condition f.hom), hS⟩

/-- Every ambient epimorphism has its actual kernel in the honest image. -/
theorem deflation_iff {K L : Obj j} (f : K ⟶ L) :
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j)).deflation f ↔ Epi f.hom := by
  constructor
  · rintro ⟨Q, p, w, hS⟩
    exact hS.epi_g
  · intro hf
    let : Epi f.hom := hf
    let S := ShortComplex.mk (kernel.ι f.hom) f.hom (kernel.condition f.hom)
    have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact f.hom }
    exact ⟨⟨kernel f.hom,
      complexObjects_kernel_of_shortExact j Fact.out hS K.property L.property⟩,
      ObjectProperty.homMk (kernel.ι f.hom),
      ObjectProperty.hom_ext _ (kernel.condition f.hom), hS⟩

/-- Admissible epimorphisms on the literal opposite of the original image category. -/
def oppositeWaldhausen : Structure (Obj j)ᵒᵖ := oppositeComplexSubcategory (complexObjects j)

/-- Compatibility with the unchanged ambient-monomorphism image structure. -/
theorem oppositeWaldhausen_compatible :
    IsCompatibleDual (waldhausen j Fact.out) (oppositeWaldhausen j) := by
  apply exactDualStructure_compatible
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j))
    (waldhausen j Fact.out) (complexSubcategoryPullbackGluing (complexObjects j))
  funext K L f
  exact propext (inflation_iff j f).symm

/-- The actual common opposite cylinder supplies image joint data. -/
def oppositeJointData : Fibration.RowFactorization.JointData
    (Fibration.NestedWeakEquivalences.refl (oppositeWaldhausen j)) :=
  oppositeComplexJointData (complexObjects j) (fun _ h => complexObjects_shift j h (-1))

local instance : (show StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace ⥤
    StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace from restrictFunctor j).Additive :=
  inferInstanceAs ((restrictFunctor j).Additive)

local instance : PreservesFiniteLimits
    (show StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace ⥤
      StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace from restrictFunctor j) :=
  inferInstanceAs (PreservesFiniteLimits (restrictFunctor j))

local instance : PreservesFiniteColimits
    (show StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace ⥤
      StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace from restrictFunctor j) :=
  inferInstanceAs (PreservesFiniteColimits (restrictFunctor j))

/-- The unchanged corestriction is exact on the actual opposite structures. -/
theorem corestrict_op_isExact : IsExact
    (perfectComplexesOppositeWaldhausen X.toRingedSpace).cof
    (perfectComplexesOppositeWaldhausen X.toRingedSpace).weq
    (oppositeWaldhausen j).cof (oppositeWaldhausen j).weq (corestrict j).op :=
  complexSubcategoryMap_op_exact
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (complexObjects j)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
