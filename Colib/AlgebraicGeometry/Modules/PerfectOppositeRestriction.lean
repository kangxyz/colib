/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOppositeJoint
public import Colib.AlgebraicGeometry.Modules.PerfectOpenRestriction
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJointMap

/-! # Coherent opposite perfect cylinders under actual open restriction

The existing degreewise restriction along an arbitrary open immersion is exact
on the literal opposite perfect categories. The native additive biproduct and
identity-cone comparisons give a natural isomorphism of the actual joint arrows.
Both endpoints and the weak projection satisfy exact equations in both directions.

No separatedness, finiteness, regularity or resolution hypothesis is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen CategoryTheory.ExactCategory
open AlgebraicGeometry.RingedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u

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

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

local instance : (show StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace ⥤
    StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace from restrictFunctor j).Additive :=
  inferInstanceAs ((restrictFunctor j).Additive)

local instance : PreservesFiniteLimits
    (show StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace ⥤
      StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace from restrictFunctor j) :=
  inferInstanceAs (PreservesFiniteLimits (restrictFunctor j))

local instance : PreservesFiniteColimits
    (show StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace ⥤
      StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace from restrictFunctor j) :=
  inferInstanceAs (PreservesFiniteColimits (restrictFunctor j))

/-- The existing actual open restriction is exact for the opposite perfect structures. -/
theorem perfectComplexesRestrictOpenImmersion_op_exact :
    Waldhausen.IsExact (perfectComplexesOppositeWaldhausen X.toRingedSpace).cof
      (perfectComplexesOppositeWaldhausen X.toRingedSpace).weq
      (perfectComplexesOppositeWaldhausen Y.toRingedSpace).cof
      (perfectComplexesOppositeWaldhausen Y.toRingedSpace).weq
      (perfectComplexesRestrictOpenImmersion j).op :=
  complexSubcategoryMap_op_exact
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (IsPerfectComplex (X := Y.toRingedSpace))
    (Complex.isPerfectComplex_restrictOpenImmersion j)

/-- The literal restriction intertwines the actual opposite joint-cylinder functors. -/
def perfectComplexesRestrictOpenImmersionJointIso :
    (perfectComplexesOppositeJointData X.toRingedSpace).joint ⋙
      ExtensionCategory.postcompose (perfectComplexesOppositeWaldhausen X.toRingedSpace)
        (perfectComplexesOppositeWaldhausen Y.toRingedSpace)
        (perfectComplexesRestrictOpenImmersion_op_exact j) ≅
      (perfectComplexesRestrictOpenImmersion j).op.mapArrow ⋙
        (perfectComplexesOppositeJointData Y.toRingedSpace).joint :=
  oppositeComplexJointDataMapIso
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (IsPerfectComplex (X := Y.toRingedSpace))
    (Complex.isPerfectComplex_restrictOpenImmersion j)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => isPerfectComplex_shift Y.toRingedSpace h (-1))
    (perfectComplexesRestrictOpenImmersion_op_exact j)

variable (f : Arrow (ObjectProperty.FullSubcategory
  (IsPerfectComplex (X := X.toRingedSpace)))ᵒᵖ)

/-- The forward comparison retains the original first endpoint. -/
theorem perfectComplexesRestrictOpenImmersionJointIso_inl :
    (perfectComplexesRestrictOpenImmersion j).op.map
        ((perfectComplexesOppositeJointData X.toRingedSpace).inl.app f) ≫
      ((perfectComplexesRestrictOpenImmersionJointIso j).hom.app f).hom.left =
    (perfectComplexesOppositeJointData Y.toRingedSpace).inl.app
      ((perfectComplexesRestrictOpenImmersion j).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inl
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (IsPerfectComplex (X := Y.toRingedSpace))
    (Complex.isPerfectComplex_restrictOpenImmersion j)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => isPerfectComplex_shift Y.toRingedSpace h (-1))
    (perfectComplexesRestrictOpenImmersion_op_exact j) f

/-- The forward comparison retains the original second endpoint. -/
theorem perfectComplexesRestrictOpenImmersionJointIso_inr :
    (perfectComplexesRestrictOpenImmersion j).op.map
        ((perfectComplexesOppositeJointData X.toRingedSpace).inr.app f) ≫
      ((perfectComplexesRestrictOpenImmersionJointIso j).hom.app f).hom.left =
    (perfectComplexesOppositeJointData Y.toRingedSpace).inr.app
      ((perfectComplexesRestrictOpenImmersion j).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inr
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (IsPerfectComplex (X := Y.toRingedSpace))
    (Complex.isPerfectComplex_restrictOpenImmersion j)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => isPerfectComplex_shift Y.toRingedSpace h (-1))
    (perfectComplexesRestrictOpenImmersion_op_exact j) f

/-- The forward comparison retains the original weak projection. -/
theorem perfectComplexesRestrictOpenImmersionJointIso_projection :
    ((perfectComplexesRestrictOpenImmersionJointIso j).hom.app f).hom.right ≫
      (perfectComplexesOppositeJointData Y.toRingedSpace).projection.app
        ((perfectComplexesRestrictOpenImmersion j).op.mapArrow.obj f) =
    (perfectComplexesRestrictOpenImmersion j).op.map
      ((perfectComplexesOppositeJointData X.toRingedSpace).projection.app f) :=
  oppositeComplexJointDataMapIso_projection
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (IsPerfectComplex (X := Y.toRingedSpace))
    (Complex.isPerfectComplex_restrictOpenImmersion j)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => isPerfectComplex_shift Y.toRingedSpace h (-1))
    (perfectComplexesRestrictOpenImmersion_op_exact j) f

/-- The inverse comparison retains the original first endpoint. -/
theorem perfectComplexesRestrictOpenImmersionJointIso_inv_inl :
    (perfectComplexesOppositeJointData Y.toRingedSpace).inl.app
        ((perfectComplexesRestrictOpenImmersion j).op.mapArrow.obj f) ≫
      ((perfectComplexesRestrictOpenImmersionJointIso j).inv.app f).hom.left =
    (perfectComplexesRestrictOpenImmersion j).op.map
      ((perfectComplexesOppositeJointData X.toRingedSpace).inl.app f) :=
  oppositeComplexJointDataMapIso_inv_inl
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (IsPerfectComplex (X := Y.toRingedSpace))
    (Complex.isPerfectComplex_restrictOpenImmersion j)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => isPerfectComplex_shift Y.toRingedSpace h (-1))
    (perfectComplexesRestrictOpenImmersion_op_exact j) f

/-- The inverse comparison retains the original second endpoint. -/
theorem perfectComplexesRestrictOpenImmersionJointIso_inv_inr :
    (perfectComplexesOppositeJointData Y.toRingedSpace).inr.app
        ((perfectComplexesRestrictOpenImmersion j).op.mapArrow.obj f) ≫
      ((perfectComplexesRestrictOpenImmersionJointIso j).inv.app f).hom.left =
    (perfectComplexesRestrictOpenImmersion j).op.map
      ((perfectComplexesOppositeJointData X.toRingedSpace).inr.app f) :=
  oppositeComplexJointDataMapIso_inv_inr
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (IsPerfectComplex (X := Y.toRingedSpace))
    (Complex.isPerfectComplex_restrictOpenImmersion j)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => isPerfectComplex_shift Y.toRingedSpace h (-1))
    (perfectComplexesRestrictOpenImmersion_op_exact j) f

/-- The inverse comparison retains the original weak projection. -/
theorem perfectComplexesRestrictOpenImmersionJointIso_inv_projection :
    ((perfectComplexesRestrictOpenImmersionJointIso j).inv.app f).hom.right ≫
      (perfectComplexesRestrictOpenImmersion j).op.map
        ((perfectComplexesOppositeJointData X.toRingedSpace).projection.app f) =
    (perfectComplexesOppositeJointData Y.toRingedSpace).projection.app
      ((perfectComplexesRestrictOpenImmersion j).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inv_projection
    (C := StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace)
    (D := StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) (restrictFunctor j)
    (IsPerfectComplex (X := X.toRingedSpace)) (IsPerfectComplex (X := Y.toRingedSpace))
    (Complex.isPerfectComplex_restrictOpenImmersion j)
    (fun _ h => isPerfectComplex_shift X.toRingedSpace h (-1))
    (fun _ h => isPerfectComplex_shift Y.toRingedSpace h (-1))
    (perfectComplexesRestrictOpenImmersion_op_exact j) f

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0311",
  colib_ref "quillen" "Quillen/Waldhausen/Fibration/Rows/OppositeComplexJointMap.lean:243-291"
    "adaptation" "Specialization to literal native perfect-complex restriction along any open \
    immersion; exactness and endpoint coherence are proved"]
  AlgebraicGeometry.Scheme.Modules.perfectComplexesRestrictOpenImmersion_op_exact
  AlgebraicGeometry.Scheme.Modules.perfectComplexesRestrictOpenImmersionJointIso
  AlgebraicGeometry.Scheme.Modules.perfectComplexesRestrictOpenImmersionJointIso_inv_inl
  AlgebraicGeometry.Scheme.Modules.perfectComplexesRestrictOpenImmersionJointIso_inv_inr
  AlgebraicGeometry.Scheme.Modules.perfectComplexesRestrictOpenImmersionJointIso_inv_projection
