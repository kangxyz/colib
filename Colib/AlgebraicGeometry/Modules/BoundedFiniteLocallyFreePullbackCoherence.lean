/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreePullback
public import Colib.AlgebraicGeometry.Modules.VectorBundleComplexInclusion
public import Colib.CategoryTheory.Waldhausen.ExactFunctorIso
public import Colib.CategoryTheory.ExactCategory.Functor.Waldhausen

/-!
# Actual pullback, restriction and single-complex comparisons

Native identity and composition isomorphisms lift through the full chain inclusion.
The restriction functor still uses native `restrictFunctor` degree by degree, rather than
being redefined as pullback. Its comparison and the degree-zero vector-bundle comparison
are actual natural isomorphisms, not additional hypotheses.

Implementation provenance: the strict pullback comparisons and vector-bundle inclusion
comparison in Quillen's perfect-complex modules at `c561118b`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

variable {X Y Z : Scheme.{u}}

/-- Native identity pullback on the original full chain subcategory. -/
def boundedFiniteLocallyFreePullbackIdIso (X : Scheme.{u}) :
    boundedFiniteLocallyFreePullback (𝟙 X) ≅
      𝟭 (boundedFiniteLocallyFreeComplex X).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedFiniteLocallyFreeComplex X).ι
    (Functor.isoWhiskerLeft (boundedFiniteLocallyFreeComplex X).ι
      (NatIso.mapHomologicalComplex (Scheme.Modules.pullbackId X) (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso X.Modules (ComplexShape.up ℤ)))

/-- Native composition pullback on the original full chain subcategory. -/
def boundedFiniteLocallyFreePullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedFiniteLocallyFreePullback (f ≫ g) ≅
      boundedFiniteLocallyFreePullback g ⋙ boundedFiniteLocallyFreePullback f :=
  Functor.fullyFaithfulCancelRight (boundedFiniteLocallyFreeComplex X).ι
    (Functor.isoWhiskerLeft (boundedFiniteLocallyFreeComplex Z).ι
      (Functor.mapHomologicalComplexCompIso (Scheme.Modules.pullbackComp f g)
        (ComplexShape.up ℤ)).symm)

/-- Actual termwise native restriction preserves bounded finite locally free complexes. -/
theorem boundedFiniteLocallyFreeComplex_restrict (j : X ⟶ Y) [IsOpenImmersion j]
    {K : CochainComplex Y.Modules ℤ} (hK : boundedFiniteLocallyFreeComplex Y K) :
    boundedFiniteLocallyFreeComplex X
      (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  boundedFiniteLocallyFreeComplex_of_iso
    ((NatIso.mapHomologicalComplex (Scheme.Modules.restrictFunctorIsoPullback j)
      (ComplexShape.up ℤ)).app K).symm (boundedFiniteLocallyFreeComplex_pullback j hK)

/-- The full-subcategory lift of the original native restriction, on objects and chain maps. -/
def boundedFiniteLocallyFreeRestrict (j : X ⟶ Y) [IsOpenImmersion j] :
    (boundedFiniteLocallyFreeComplex Y).FullSubcategory ⥤
      (boundedFiniteLocallyFreeComplex X).FullSubcategory :=
  (boundedFiniteLocallyFreeComplex X).lift
    ((boundedFiniteLocallyFreeComplex Y).ι ⋙
      (Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => boundedFiniteLocallyFreeComplex_restrict j K.property)

/-- The actual restriction and pullback functors are naturally isomorphic. -/
def boundedFiniteLocallyFreeRestrictIsoPullback (j : X ⟶ Y) [IsOpenImmersion j] :
    boundedFiniteLocallyFreeRestrict j ≅ boundedFiniteLocallyFreePullback j :=
  Functor.fullyFaithfulCancelRight (boundedFiniteLocallyFreeComplex X).ι
    (Functor.isoWhiskerLeft (boundedFiniteLocallyFreeComplex Y).ι
      (NatIso.mapHomologicalComplex (Scheme.Modules.restrictFunctorIsoPullback j)
        (ComplexShape.up ℤ)))

/-- The original termwise restriction is Waldhausen-exact. -/
theorem boundedFiniteLocallyFreeRestrict_isExact (j : X ⟶ Y) [IsOpenImmersion j] :
    Waldhausen.IsExact (boundedFiniteLocallyFreeWaldhausen Y).cof
      (boundedFiniteLocallyFreeWaldhausen Y).weq
      (boundedFiniteLocallyFreeWaldhausen X).cof
      (boundedFiniteLocallyFreeWaldhausen X).weq (boundedFiniteLocallyFreeRestrict j) :=
  (boundedFiniteLocallyFreePullback_isExact j).of_iso
    (boundedFiniteLocallyFreeRestrictIsoPullback j).symm

/-- The degree-zero inclusion commutes with every genuine geometric pullback. -/
@[colib_tag "COL-0322",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/VectorBundlePullback.lean:32-39"
    "adaptation" "The actual single-complex comparison under arbitrary native scheme pullback"]
def vectorBundleComplexInclusionPullbackIso (f : X ⟶ Y) :
    vectorBundleComplexInclusion Y ⋙ boundedFiniteLocallyFreePullback f ≅
      Scheme.Modules.vectorBundlePullback f ⋙ vectorBundleComplexInclusion X :=
  Functor.fullyFaithfulCancelRight (boundedFiniteLocallyFreeComplex X).ι
    (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pullback f) (ComplexShape.up ℤ) 0))

end Stacks.Perfect.BoundedLocallyFreeComplexes
