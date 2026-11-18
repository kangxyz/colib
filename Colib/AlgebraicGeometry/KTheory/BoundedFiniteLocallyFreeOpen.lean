/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFreePullback
public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeJoint
public import Colib.CategoryTheory.Waldhausen.Fibration.ComplexExtension
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeak
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.CoarseJoint
public import Colib.KTheory.Waldhausen.Fibration.LongExactSequence

/-!
# Relative open restriction of bounded vector-bundle complexes

The source is the native category of globally bounded finite locally free complexes.
Keep the native cofibrations and detect weak equivalences by actual termwise open restriction.
The native joint cylinder proves the canonical relative fiber comparison. Its degree-zero
tail identifies the two ranges in the fine K-group of the open, not that whole group.

Adapted from Quillen's `PerfectComplexes/StrictOpenRelative.lean` and
`PerfectComplexes/StrictOpenKZeroImage.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open AlgebraicGeometry Topology Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original quasi-isomorphisms are weak equivalences after actual restriction. -/
def boundedFiniteLocallyFreeOpenNested :
    NestedWeakEquivalences (boundedFiniteLocallyFreeWaldhausen X) :=
  Structure.inverseImageWeakNested (boundedFiniteLocallyFreeRestrict_isExact j)

/-- The genuine weak class detected by open restriction on the same source category. -/
abbrev boundedFiniteLocallyFreeOpenWaldhausen :
    Waldhausen.Structure (boundedFiniteLocallyFreeComplex X).FullSubcategory :=
  (boundedFiniteLocallyFreeOpenNested j).coarse

/-- The same native restriction functor is exact for the larger weak class. -/
theorem boundedFiniteLocallyFreeOpenRestrict_isExact :
    IsExact (boundedFiniteLocallyFreeOpenWaldhausen j).cof
      (boundedFiniteLocallyFreeOpenWaldhausen j).weq
      (boundedFiniteLocallyFreeWaldhausen U).cof (boundedFiniteLocallyFreeWaldhausen U).weq
      (boundedFiniteLocallyFreeRestrict j) :=
  Structure.withInverseImageWeak_exact (boundedFiniteLocallyFreeRestrict_isExact j)

/-- Weakness is detected by genuine quasi-isomorphisms of restricted complexes. -/
instance boundedFiniteLocallyFreeOpenWaldhausen_twoOutOfThree :
    (boundedFiniteLocallyFreeOpenWaldhausen j).weq.HasTwoOutOfThreeProperty := by
  let : (boundedFiniteLocallyFreeWaldhausen U).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs
      (subcategoryWeakEquivalences (boundedFiniteLocallyFreeComplex U)).HasTwoOutOfThreeProperty
  exact Structure.withInverseImageWeak_twoOutOfThree (boundedFiniteLocallyFreeRestrict_isExact j)

/-- The native cone factorization remains a factorization for the relative weak class. -/
def boundedFiniteLocallyFreeOpenFactorization :
    FunctorialFactorization (boundedFiniteLocallyFreeOpenWaldhausen j) := by
  let T := complexSubcategoryFactorization (boundedFiniteLocallyFreeComplex X)
    boundedFiniteLocallyFreeComplex_mappingCone
  exact { T with weak := fun f => (boundedFiniteLocallyFreeOpenNested j).le_weq _ (T.weak f) }

/-- The same native joint cylinder is exact for the coarse class. -/
def boundedFiniteLocallyFreeOpenCoarseJointData :
    RowFactorization.JointData (NestedWeakEquivalences.refl
      (boundedFiniteLocallyFreeOpenWaldhausen j)) := by
  let : (boundedFiniteLocallyFreeOpenNested j).coarse.weq.HasTwoOutOfThreeProperty :=
    boundedFiniteLocallyFreeOpenWaldhausen_twoOutOfThree j
  exact (boundedFiniteLocallyFreeJointData X (boundedFiniteLocallyFreeOpenNested j)).coarseReflexive
    (boundedFiniteLocallyFreeOpenNested j)

/-- Genuine extension follows from the inherited exact structure on the open. -/
theorem boundedFiniteLocallyFreeOpenWaldhausen_extensionAxiom :
    ExtensionAxiom (boundedFiniteLocallyFreeOpenWaldhausen j) :=
  Structure.withInverseImageWeak_extensionAxiom (boundedFiniteLocallyFreeRestrict_isExact j)
    (complexSubcategory_extensionAxiom (boundedFiniteLocallyFreeComplex U))

/-- The canonical relative fiber comparison is a weak homotopy equivalence. -/
theorem boundedFiniteLocallyFreeOpen_canonicalFiberMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (canonicalFiberMap (boundedFiniteLocallyFreeOpenNested j)) := by
  let : (boundedFiniteLocallyFreeOpenNested j).coarse.weq.HasTwoOutOfThreeProperty :=
    boundedFiniteLocallyFreeOpenWaldhausen_twoOutOfThree j
  exact canonicalFiberMap_isWeakHomotopyEquivalence_general (boundedFiniteLocallyFreeOpenNested j)
    (boundedFiniteLocallyFreeOpenWaldhausen_extensionAxiom j)
    (boundedFiniteLocallyFreeJointData X (boundedFiniteLocallyFreeOpenNested j))
    (boundedFiniteLocallyFreeJointData_secondEndpointSection X
      (boundedFiniteLocallyFreeOpenNested j))

/-- The canonical relative restriction lands in fine K-theory of the open. -/
def boundedFiniteLocallyFreeOpenKRestrict (n : ℕ) :
    (boundedFiniteLocallyFreeOpenWaldhausen j).K n →* U.boundedFiniteLocallyFreeK n :=
  KMap (boundedFiniteLocallyFreeOpenRestrict_isExact j) n

/-- The relative factorization retains the unchanged fine restriction homomorphism. -/
theorem boundedFiniteLocallyFreeOpenKRestrict_comp_changeWeak (n : ℕ) :
    (boundedFiniteLocallyFreeOpenKRestrict j n).comp
      (KMap (changeWeak_exact (boundedFiniteLocallyFreeOpenNested j)) n) =
        boundedFiniteLocallyFreeKRestrict j n := by
  exact KMap_comp_KMap (changeWeak_exact (boundedFiniteLocallyFreeOpenNested j))
    (boundedFiniteLocallyFreeOpenRestrict_isExact j) n

/-- Every relative degree-zero class has an original bounded vector-bundle representative. -/
theorem boundedFiniteLocallyFreeOpen_changeWeak_KMap_zero_surjective :
    Function.Surjective (KMap (changeWeak_exact (boundedFiniteLocallyFreeOpenNested j)) 0) :=
  changeWeak_KMap_zero_surjective_of_weak (boundedFiniteLocallyFreeOpenNested j)
    (boundedFiniteLocallyFreeOpen_canonicalFiberMap_isWeakHomotopyEquivalence j)

/-- Relative degree-zero restriction has precisely the original restriction range. -/
theorem range_boundedFiniteLocallyFreeOpenKRestrict_zero :
    (boundedFiniteLocallyFreeOpenKRestrict j 0).range =
      (boundedFiniteLocallyFreeKRestrict j 0).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := boundedFiniteLocallyFreeOpen_changeWeak_KMap_zero_surjective j a
    exact ⟨b, (DFunLike.congr_fun
      (boundedFiniteLocallyFreeOpenKRestrict_comp_changeWeak j 0) b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨KMap (changeWeak_exact (boundedFiniteLocallyFreeOpenNested j)) 0 b,
      DFunLike.congr_fun (boundedFiniteLocallyFreeOpenKRestrict_comp_changeWeak j 0) b⟩

/-- Degree-zero classes in the actual image of fine restriction. -/
abbrev BoundedFiniteLocallyFreeOpenKZeroImage := (boundedFiniteLocallyFreeKRestrict j 0).range

/-- Restrict the codomain of the actual relative map to the original restriction image. -/
def boundedFiniteLocallyFreeOpenKZeroToImage :
    (boundedFiniteLocallyFreeOpenWaldhausen j).K 0 →*
      BoundedFiniteLocallyFreeOpenKZeroImage j :=
  (boundedFiniteLocallyFreeOpenKRestrict j 0).codRestrict
    (BoundedFiniteLocallyFreeOpenKZeroImage j) (fun a => by
      change boundedFiniteLocallyFreeOpenKRestrict j 0 a ∈
        (boundedFiniteLocallyFreeKRestrict j 0).range
      rw [← range_boundedFiniteLocallyFreeOpenKRestrict_zero j]
      exact ⟨a, rfl⟩)

/-- Forgetting membership recovers the actual relative restriction. -/
@[simp] theorem boundedFiniteLocallyFreeOpenKZeroToImage_coe
    (a : (boundedFiniteLocallyFreeOpenWaldhausen j).K 0) :
    (boundedFiniteLocallyFreeOpenKZeroToImage j a : U.boundedFiniteLocallyFreeK 0) =
      boundedFiniteLocallyFreeOpenKRestrict j 0 a := rfl

/-- The relative map surjects onto the honest image, not necessarily the full target. -/
theorem boundedFiniteLocallyFreeOpenKZeroToImage_surjective :
    Function.Surjective (boundedFiniteLocallyFreeOpenKZeroToImage j) := by
  rintro ⟨x, a, rfl⟩
  refine ⟨KMap (changeWeak_exact (boundedFiniteLocallyFreeOpenNested j)) 0 a, ?_⟩
  apply Subtype.ext
  exact DFunLike.congr_fun (boundedFiniteLocallyFreeOpenKRestrict_comp_changeWeak j 0) a

end AlgebraicGeometry.Scheme.Modules
