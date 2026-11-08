/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreePerfect
public import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen
public import Colib.CategoryTheory.Waldhausen.SubcategoryInclusion

/-!
# The actual Waldhausen structure on bounded vector-bundle complexes

The inherited exact structure uses all actual short exact sequences in the native bounded
finite locally free subcategory. Cofibrations are admissible monomorphisms: their actual
quotients must still be bounded finite locally free. They are not all ambient monomorphisms.
Weak equivalences are genuine quasi-isomorphisms of the original complexes.

The full inclusion into native perfect complexes is exact for their existing ambient-mono
Waldhausen structure. No equivalence of K-theory or geometric approximation is asserted.

Implementation provenance: `Quillen/AlgebraicGeometry/PerfectComplexes/Strict.lean` and its
strict-to-perfect inclusion, at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

variable (X : Scheme.{u})

/-- The exact structure inherited from actual short exact sequences of native complexes. -/
def boundedFiniteLocallyFreeExactStructure :
    ExactStructure (boundedFiniteLocallyFreeComplex X).FullSubcategory :=
  ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
    (boundedFiniteLocallyFreeComplex X)

/-- The native full-chain subcategory with admissible cofibrations and quasi-isomorphisms. -/
@[colib_tag "COL-0313",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/Strict.lean:33-36"
    "adaptation" "The actual bounded finite locally free subcategory and its quasi-isomorphisms"]
def boundedFiniteLocallyFreeWaldhausen :
    Waldhausen.Structure (boundedFiniteLocallyFreeComplex X).FullSubcategory :=
  Waldhausen.complexSubcategory (boundedFiniteLocallyFreeComplex X)

/-- The cofibration condition retains the original finite locally free quotient. -/
theorem boundedFiniteLocallyFreeWaldhausen_cof_iff
    {K L : (boundedFiniteLocallyFreeComplex X).FullSubcategory} (f : K ⟶ L) :
    (boundedFiniteLocallyFreeWaldhausen X).cof f ↔
      ∃ (Q : CochainComplex X.Modules ℤ) (_hQ : boundedFiniteLocallyFreeComplex X Q)
        (p : L.obj ⟶ Q) (h : f.hom ≫ p = 0),
        (ShortComplex.mk f.hom p h).ShortExact :=
  ExactSubcategory.inflation_iff (abelianExactStructure _) _ f

/-- The weak-equivalence condition is the original homology-based quasi-isomorphism. -/
@[simp]
theorem boundedFiniteLocallyFreeWaldhausen_weq_iff
    {K L : (boundedFiniteLocallyFreeComplex X).FullSubcategory} (f : K ⟶ L) :
    (boundedFiniteLocallyFreeWaldhausen X).weq f ↔ QuasiIso f.hom := Iff.rfl

/-- The literal inclusion in all complexes preserves the original Waldhausen structure. -/
theorem boundedFiniteLocallyFree_inclusion_isExact :
    Waldhausen.IsExact (boundedFiniteLocallyFreeWaldhausen X).cof
      (boundedFiniteLocallyFreeWaldhausen X).weq
      (Waldhausen.complexes X.Modules).cof (Waldhausen.complexes X.Modules).weq
      (boundedFiniteLocallyFreeComplex X).ι :=
  Waldhausen.complexSubcategory_inclusion_exact (boundedFiniteLocallyFreeComplex X)

/-- The original chain inclusion is exact into the existing native perfect Waldhausen model. -/
@[colib_tag "COL-0313",
  stacks 0F8I "Perfectness input for the actual exact chain inclusion"]
theorem boundedFiniteLocallyFreePerfectInclusion_isExact :
    Waldhausen.IsExact (boundedFiniteLocallyFreeWaldhausen X).cof
      (boundedFiniteLocallyFreeWaldhausen X).weq
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (boundedFiniteLocallyFreePerfectInclusion X) where
  zero h := (boundedFiniteLocallyFreePerfectInclusion X).map_isZero h
  cofibration f hf := (boundedFiniteLocallyFree_inclusion_isExact X).cofibration f hf
  weak _ hf := hf
  pushout hi h := by
    apply IsPushout.of_map_of_faithful
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    exact (boundedFiniteLocallyFree_inclusion_isExact X).pushout hi h

end Stacks.Perfect.BoundedLocallyFreeComplexes
