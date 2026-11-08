/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Opposite
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJointMap

/-! # Coherent actual opposite cylinders under image corestriction

The canonical additive biproduct and identity-cone comparison transports through
actual opposite equivalences. All six endpoint equations are retained; independently
chosen cofibers are compared by this natural isomorphism, not by definitional equality.

Adapted from Quillen `AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/JointComparison.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen CategoryTheory.ExactCategory
open AlgebraicGeometry.RingedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
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

/-- The literal restriction intertwines the actual opposite joint-cylinder functors. -/
def corestrictJointIso :
    (perfectComplexesOppositeJointData X.toRingedSpace).joint ⋙
      ExtensionCategory.postcompose (perfectComplexesOppositeWaldhausen X.toRingedSpace)
        (oppositeWaldhausen j)
        (corestrict_op_isExact j) ≅
      (corestrict j).op.mapArrow ⋙
        (oppositeJointData j).joint :=
  oppositeComplexJointDataMapIso
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (complexObjects j)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => complexObjects_shift j h (-1))
    (corestrict_op_isExact j)

variable (f : Arrow (ObjectProperty.FullSubcategory
  (IsPerfectComplex (X := X.toRingedSpace)))ᵒᵖ)

/-- The forward comparison retains the original first endpoint. -/
theorem corestrictJointIso_inl :
    (corestrict j).op.map
        ((perfectComplexesOppositeJointData X.toRingedSpace).inl.app f) ≫
      ((corestrictJointIso j).hom.app f).hom.left =
    (oppositeJointData j).inl.app
      ((corestrict j).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inl
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (complexObjects j)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => complexObjects_shift j h (-1))
    (corestrict_op_isExact j) f

/-- The forward comparison retains the original second endpoint. -/
theorem corestrictJointIso_inr :
    (corestrict j).op.map
        ((perfectComplexesOppositeJointData X.toRingedSpace).inr.app f) ≫
      ((corestrictJointIso j).hom.app f).hom.left =
    (oppositeJointData j).inr.app
      ((corestrict j).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inr
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (complexObjects j)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => complexObjects_shift j h (-1))
    (corestrict_op_isExact j) f

/-- The forward comparison retains the original weak projection. -/
theorem corestrictJointIso_projection :
    ((corestrictJointIso j).hom.app f).hom.right ≫
      (oppositeJointData j).projection.app
        ((corestrict j).op.mapArrow.obj f) =
    (corestrict j).op.map
      ((perfectComplexesOppositeJointData X.toRingedSpace).projection.app f) :=
  oppositeComplexJointDataMapIso_projection
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (complexObjects j)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => complexObjects_shift j h (-1))
    (corestrict_op_isExact j) f

/-- The inverse comparison retains the original first endpoint. -/
theorem corestrictJointIso_inv_inl :
    (oppositeJointData j).inl.app
        ((corestrict j).op.mapArrow.obj f) ≫
      ((corestrictJointIso j).inv.app f).hom.left =
    (corestrict j).op.map
      ((perfectComplexesOppositeJointData X.toRingedSpace).inl.app f) :=
  oppositeComplexJointDataMapIso_inv_inl
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (complexObjects j)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => complexObjects_shift j h (-1))
    (corestrict_op_isExact j) f

/-- The inverse comparison retains the original second endpoint. -/
theorem corestrictJointIso_inv_inr :
    (oppositeJointData j).inr.app
        ((corestrict j).op.mapArrow.obj f) ≫
      ((corestrictJointIso j).inv.app f).hom.left =
    (corestrict j).op.map
      ((perfectComplexesOppositeJointData X.toRingedSpace).inr.app f) :=
  oppositeComplexJointDataMapIso_inv_inr
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (complexObjects j)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => complexObjects_shift j h (-1))
    (corestrict_op_isExact j) f

/-- The inverse comparison retains the original weak projection. -/
theorem corestrictJointIso_inv_projection :
    ((corestrictJointIso j).inv.app f).hom.right ≫
      (corestrict j).op.map
        ((perfectComplexesOppositeJointData X.toRingedSpace).projection.app f) =
    (oppositeJointData j).projection.app
      ((corestrict j).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inv_projection
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} U.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (complexObjects j)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => complexObjects_shift j h (-1))
    (corestrict_op_isExact j) f

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
