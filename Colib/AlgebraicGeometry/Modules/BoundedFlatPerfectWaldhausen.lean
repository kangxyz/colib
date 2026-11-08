/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectClosure
public import Colib.CategoryTheory.Waldhausen.SubcategoryInclusion
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ComplexRelativeJoint

/-!
# The Bounded Above Flat Perfect Waldhausen Model

The exact structure is inherited from actual short exact sequences. Cofibrations have an
actual quotient in the same class, and weak equivalences are the original quasi-isomorphisms.
The native perfect target uses its existing ambient-monomorphism structure. Actual identity-cone
joint cylinders are constructed, not supplied as a hypothesis.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Basic.lean` and
`Cylinder.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry StrictlyPerfect

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u, u})

instance boundedAboveFlatPerfectHasFiniteBiproducts :
    HasFiniteBiproducts (boundedAboveFlatPerfectComplex X).FullSubcategory :=
  .of_hasFiniteProducts

instance boundedAboveFlatPerfectInclusion_additive :
    (boundedAboveFlatPerfectInclusion X).Additive where
  map_add := by intros; rfl

/-- All inherited ambient short exact sequences give the exact structure. -/
def boundedAboveFlatPerfectExactStructure :
    ExactStructure (boundedAboveFlatPerfectComplex X).FullSubcategory :=
  ExactSubcategory.exactStructure (abelianExactStructure _) (boundedAboveFlatPerfectComplex X)

/-- The actual full-chain model with admissible quotients and quasi-isomorphisms. -/
@[colib_tag "COL-0323",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Basic.lean:49-58"
    "adaptation" "The original bounded-above flat locally-perfect exact chain model"]
def boundedAboveFlatPerfectWaldhausen :
    Waldhausen.Structure (boundedAboveFlatPerfectComplex X).FullSubcategory :=
  Waldhausen.complexSubcategory (boundedAboveFlatPerfectComplex X)

/-- An admissible cofibration has an actual bounded-above flat perfect quotient. -/
theorem boundedAboveFlatPerfectWaldhausen_cof_iff
    {K L : (boundedAboveFlatPerfectComplex X).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectWaldhausen X).cof f ↔
      ∃ (Q : CochainComplex (OXMod.{u, u, u} X) ℤ)
        (_hQ : boundedAboveFlatPerfectComplex X Q) (p : L.obj ⟶ Q) (h : f.hom ≫ p = 0),
        (ShortComplex.mk f.hom p h).ShortExact :=
  ExactSubcategory.inflation_iff (abelianExactStructure _) _ f

/-- Weak equivalence means precisely the original quasi-isomorphism of sheaf complexes. -/
@[simp]
theorem boundedAboveFlatPerfectWaldhausen_weq_iff
    {K L : (boundedAboveFlatPerfectComplex X).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectWaldhausen X).weq f ↔ QuasiIso f.hom := Iff.rfl

/-- The original inclusion into all complexes is exact. -/
theorem boundedAboveFlatPerfect_inclusion_isExact :
    Waldhausen.IsExact (boundedAboveFlatPerfectWaldhausen X).cof
      (boundedAboveFlatPerfectWaldhausen X).weq
      (Waldhausen.complexes (OXMod.{u, u, u} X)).cof
      (Waldhausen.complexes (OXMod.{u, u, u} X)).weq
      (boundedAboveFlatPerfectComplex X).ι :=
  Waldhausen.complexSubcategory_inclusion_exact (boundedAboveFlatPerfectComplex X)

/-- The literal inclusion into the existing native perfect Waldhausen category is exact. -/
theorem boundedAboveFlatPerfectInclusion_isExact :
    Waldhausen.IsExact (boundedAboveFlatPerfectWaldhausen X).cof
      (boundedAboveFlatPerfectWaldhausen X).weq
      (perfectComplexesWaldhausen X).cof (perfectComplexesWaldhausen X).weq
      (boundedAboveFlatPerfectInclusion X) where
  zero h := (boundedAboveFlatPerfectInclusion X).map_isZero h
  cofibration f hf := (boundedAboveFlatPerfect_inclusion_isExact X).cofibration f hf
  weak _ hf := hf
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (ObjectProperty.ι (IsPerfectComplex (X := X)))
    exact (boundedAboveFlatPerfect_inclusion_isExact X).pushout hi h

/-- App1 is literal reflection of the original quasi-isomorphism condition. -/
theorem boundedAboveFlatPerfectInclusion_weq_iff
    {K L : (boundedAboveFlatPerfectComplex X).FullSubcategory} (f : K ⟶ L) :
    (perfectComplexesWaldhausen X).weq ((boundedAboveFlatPerfectInclusion X).map f) ↔
      (boundedAboveFlatPerfectWaldhausen X).weq f := Iff.rfl

/-- Genuine identity-cone joint data for every nested class above quasi-isomorphisms. -/
@[colib_tag "COL-0323",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Cylinder.lean:39-47"
    "adaptation" "Actual joint cylinders on the bounded-above flat native perfect model"]
def boundedAboveFlatPerfectJointData
    (N : Waldhausen.Fibration.NestedWeakEquivalences (boundedAboveFlatPerfectWaldhausen X)) :
    Waldhausen.Fibration.RowFactorization.JointData N :=
  Waldhausen.Fibration.complexJointDataOfNested (boundedAboveFlatPerfectComplex X)
    (fun hK hL f => boundedAboveFlatPerfectComplex_mappingCone hK hL f)
    (fun _ hK => boundedAboveFlatPerfectComplex_shift hK 1) N

/-- The actual second endpoint is a section of the unchanged cylinder projection. -/
theorem boundedAboveFlatPerfectJointData_secondEndpointSection
    (N : Waldhausen.Fibration.NestedWeakEquivalences (boundedAboveFlatPerfectWaldhausen X)) :
    Waldhausen.Fibration.RowFactorization.SecondEndpointSection N
      (boundedAboveFlatPerfectJointData X N) :=
  Waldhausen.Fibration.complexJointDataOfNested_secondEndpointSection
    (boundedAboveFlatPerfectComplex X)
    (fun hK hL f => boundedAboveFlatPerfectComplex_mappingCone hK hL f)
    (fun _ hK => boundedAboveFlatPerfectComplex_shift hK 1) N

end AlgebraicGeometry.RingedSpace
