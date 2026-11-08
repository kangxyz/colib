/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeJoint
public import Colib.AlgebraicGeometry.Modules.PerfectOppositeJoint
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJointInclusion

/-!
# Compatible dual structures and the actual strict-to-perfect joint comparison

Admissible epimorphisms define the opposite Waldhausen structure on the literal opposite of
bounded finite locally free complexes. Native negative shifts give the original opposite
joint cylinder. The actual inclusion into perfect complexes preserves both dual structures.

Both categories use the same ambient cylinder. Its comparison retains the original first
endpoint, second endpoint and projection, rather than postulating their compatibility.
There is no assertion that all epimorphisms between bounded vector-bundle complexes are
admissible, and no derived-image approximation theorem is assumed.

Implementation provenance: the strict-complex part of
`Quillen/AlgebraicGeometry/PerfectComplexes/OppositeJointData.lean:40-100` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

variable (X : Scheme.{u})

local instance : ObjectProperty.ContainsZero
    (show ObjectProperty (CochainComplex X.Modules ℤ) from
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_containsZero X.toRingedSpace

local instance : ObjectProperty.IsClosedUnderIsomorphisms
    (show ObjectProperty (CochainComplex X.Modules ℤ) from
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_closedUnderIsomorphisms X.toRingedSpace

local instance : (ExactCategory.abelianExactStructure
    (CochainComplex X.Modules ℤ)).IsExtensionClosed
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_extensionClosed X.toRingedSpace

local instance : ObjectProperty.IsClosedUnderFiniteProducts
    (show ObjectProperty (CochainComplex X.Modules ℤ) from
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_closedUnderFiniteProducts X.toRingedSpace

/-- Admissible epimorphisms and original quasi-isomorphisms on the literal opposite category. -/
def boundedFiniteLocallyFreeOppositeWaldhausen :
    Waldhausen.Structure (boundedFiniteLocallyFreeComplex X).FullSubcategoryᵒᵖ :=
  Waldhausen.oppositeComplexSubcategory (boundedFiniteLocallyFreeComplex X)

/-- The dual structures retain the actual zero-corner kernel and cokernel squares. -/
theorem boundedFiniteLocallyFreeOppositeWaldhausen_compatible :
    Waldhausen.IsCompatibleDual (boundedFiniteLocallyFreeWaldhausen X)
      (boundedFiniteLocallyFreeOppositeWaldhausen X) :=
  Waldhausen.oppositeComplexSubcategory_compatible (boundedFiniteLocallyFreeComplex X)

/-- The actual inclusion is also exact on the literal opposite categories. -/
theorem boundedFiniteLocallyFreePerfectInclusion_op_isExact :
    Waldhausen.IsExact (boundedFiniteLocallyFreeOppositeWaldhausen X).cof
      (boundedFiniteLocallyFreeOppositeWaldhausen X).weq
      (RingedSpace.perfectComplexesOppositeWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesOppositeWaldhausen X.toRingedSpace).weq
      (boundedFiniteLocallyFreePerfectInclusion X).op :=
  Waldhausen.oppositeSubcategoryInclusion_exact (boundedFiniteLocallyFreeComplex X)
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
    (fun _ h => isPerfectComplex_of_boundedFiniteLocallyFree h)

/-- The original opposite complex cylinder restricts to native bounded vector bundles. -/
def boundedFiniteLocallyFreeOppositeJointData :
    Waldhausen.Fibration.RowFactorization.JointData
      (Waldhausen.Fibration.NestedWeakEquivalences.refl
        (boundedFiniteLocallyFreeOppositeWaldhausen X)) :=
  Waldhausen.oppositeComplexJointData (boundedFiniteLocallyFreeComplex X)
    (fun _ h => boundedFiniteLocallyFreeComplex_shift h (-1))

/-- The strict-to-perfect inclusion preserves the actual common opposite cylinder. -/
@[colib_tag "COL-0313",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/OppositeJointData.lean:75-100"
    "adaptation" "Native bounded vector-bundle inclusion and its unchanged opposite joint maps"]
def boundedFiniteLocallyFreePerfectOppositeJointIso :
    (boundedFiniteLocallyFreeOppositeJointData X).joint ⋙
      Waldhausen.ExtensionCategory.postcompose (boundedFiniteLocallyFreeOppositeWaldhausen X)
        (RingedSpace.perfectComplexesOppositeWaldhausen X.toRingedSpace)
        (boundedFiniteLocallyFreePerfectInclusion_op_isExact X) ≅
    (boundedFiniteLocallyFreePerfectInclusion X).op.mapArrow ⋙
      (RingedSpace.perfectComplexesOppositeJointData X.toRingedSpace).joint :=
  Waldhausen.oppositeComplexJointDataInclusionIso (boundedFiniteLocallyFreeComplex X)
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
    (fun _ h => isPerfectComplex_of_boundedFiniteLocallyFree h)
    (fun _ h => boundedFiniteLocallyFreeComplex_shift h (-1))
    (fun _ h => RingedSpace.isPerfectComplex_shift X.toRingedSpace h (-1))

/-- The comparison preserves the actual first endpoint in the weak-arrow orientation. -/
theorem boundedFiniteLocallyFreePerfectOppositeJointIso_inv_inl
    (f : Arrow (boundedFiniteLocallyFreeComplex X).FullSubcategoryᵒᵖ) :
    (RingedSpace.perfectComplexesOppositeJointData X.toRingedSpace).inl.app
        ((boundedFiniteLocallyFreePerfectInclusion X).op.mapArrow.obj f) ≫
      ((boundedFiniteLocallyFreePerfectOppositeJointIso X).inv.app f).hom.left =
    (boundedFiniteLocallyFreePerfectInclusion X).op.map
      ((boundedFiniteLocallyFreeOppositeJointData X).inl.app f) :=
  Waldhausen.oppositeComplexJointDataInclusionIso_inv_inl
    (boundedFiniteLocallyFreeComplex X)
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
    (fun _ h => isPerfectComplex_of_boundedFiniteLocallyFree h)
    (fun _ h => boundedFiniteLocallyFreeComplex_shift h (-1))
    (fun _ h => RingedSpace.isPerfectComplex_shift X.toRingedSpace h (-1)) f

/-- The comparison preserves the actual second endpoint in the weak-arrow orientation. -/
theorem boundedFiniteLocallyFreePerfectOppositeJointIso_inv_inr
    (f : Arrow (boundedFiniteLocallyFreeComplex X).FullSubcategoryᵒᵖ) :
    (RingedSpace.perfectComplexesOppositeJointData X.toRingedSpace).inr.app
        ((boundedFiniteLocallyFreePerfectInclusion X).op.mapArrow.obj f) ≫
      ((boundedFiniteLocallyFreePerfectOppositeJointIso X).inv.app f).hom.left =
    (boundedFiniteLocallyFreePerfectInclusion X).op.map
      ((boundedFiniteLocallyFreeOppositeJointData X).inr.app f) :=
  Waldhausen.oppositeComplexJointDataInclusionIso_inv_inr
    (boundedFiniteLocallyFreeComplex X)
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
    (fun _ h => isPerfectComplex_of_boundedFiniteLocallyFree h)
    (fun _ h => boundedFiniteLocallyFreeComplex_shift h (-1))
    (fun _ h => RingedSpace.isPerfectComplex_shift X.toRingedSpace h (-1)) f

/-- The comparison retains the original actual quasi-isomorphism projection. -/
theorem boundedFiniteLocallyFreePerfectOppositeJointIso_inv_projection
    (f : Arrow (boundedFiniteLocallyFreeComplex X).FullSubcategoryᵒᵖ) :
    ((boundedFiniteLocallyFreePerfectOppositeJointIso X).inv.app f).hom.right ≫
      (boundedFiniteLocallyFreePerfectInclusion X).op.map
        ((boundedFiniteLocallyFreeOppositeJointData X).projection.app f) =
    (RingedSpace.perfectComplexesOppositeJointData X.toRingedSpace).projection.app
      ((boundedFiniteLocallyFreePerfectInclusion X).op.mapArrow.obj f) :=
  Waldhausen.oppositeComplexJointDataInclusionIso_inv_projection
    (boundedFiniteLocallyFreeComplex X)
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
    (fun _ h => isPerfectComplex_of_boundedFiniteLocallyFree h)
    (fun _ h => boundedFiniteLocallyFreeComplex_shift h (-1))
    (fun _ h => RingedSpace.isPerfectComplex_shift X.toRingedSpace h (-1)) f

end Stacks.Perfect.BoundedLocallyFreeComplexes
