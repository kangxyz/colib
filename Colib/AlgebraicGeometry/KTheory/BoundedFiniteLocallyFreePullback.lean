/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreePullbackCoherence
public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFree
public import Colib.KTheory.Waldhausen.Functoriality

/-!
# Functorial K-pullback for bounded finite locally free complexes

These maps are the canonical chosen-zero-normalized KMaps of actual geometric functors.
They are contravariantly functorial under every scheme morphism, retain actual open
restriction, and commute with degree-zero vector-bundle inclusion. Any commutative square
of open pairs is allowed; its pullback/restriction equation is proved from the actual maps.
All statements include degree zero. They do not claim derived pullback on all perfect
complexes, supported boundary naturality, or a strict-to-perfect K-equivalence.

Implementation provenance: `Quillen/AlgebraicGeometry/PerfectComplexes/Pullback.lean`
and the vector-bundle pullback comparison at `c561118b`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- Actual arbitrary pullback on the existing connective S-construction K-groups. -/
@[colib_tag "COL-0322",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/Pullback.lean:69-95"
    "adaptation"
    "Original strict-perfect K-pullback on native bounded finite locally free complexes"]
def boundedFiniteLocallyFreeKPullback (f : X ⟶ Y) (n : ℕ) :
    Y.boundedFiniteLocallyFreeK n →* X.boundedFiniteLocallyFreeK n :=
  Waldhausen.KMap (boundedFiniteLocallyFreePullback_isExact f) n

@[simp]
theorem boundedFiniteLocallyFreeKPullback_id (X : Scheme.{u}) (n : ℕ) :
    boundedFiniteLocallyFreeKPullback (𝟙 X) n = MonoidHom.id (X.boundedFiniteLocallyFreeK n) :=
  (Waldhausen.KMap_eq_of_iso (boundedFiniteLocallyFreePullback_isExact (𝟙 X))
    (Waldhausen.IsExact.id (boundedFiniteLocallyFreeWaldhausen X).cof
      (boundedFiniteLocallyFreeWaldhausen X).weq)
    (boundedFiniteLocallyFreePullbackIdIso X) n).trans (Waldhausen.KMap_id _ n)

@[simp]
theorem boundedFiniteLocallyFreeKPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    boundedFiniteLocallyFreeKPullback (f ≫ g) n =
      (boundedFiniteLocallyFreeKPullback f n).comp (boundedFiniteLocallyFreeKPullback g n) :=
  (Waldhausen.KMap_eq_of_iso (boundedFiniteLocallyFreePullback_isExact (f ≫ g))
    ((boundedFiniteLocallyFreePullback_isExact g).comp
      (boundedFiniteLocallyFreePullback_isExact f))
    (boundedFiniteLocallyFreePullbackCompIso f g) n).trans
    (Waldhausen.KMap_comp_KMap (boundedFiniteLocallyFreePullback_isExact g)
      (boundedFiniteLocallyFreePullback_isExact f) n).symm

/-- The unchanged native termwise restriction induces this actual canonical K-map. -/
def boundedFiniteLocallyFreeKRestrict (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    Y.boundedFiniteLocallyFreeK n →* X.boundedFiniteLocallyFreeK n :=
  Waldhausen.KMap (boundedFiniteLocallyFreeRestrict_isExact j) n

/-- The arbitrary pullback agrees with that actual restriction on every open immersion. -/
theorem boundedFiniteLocallyFreeKPullback_eq_restrict (j : X ⟶ Y) [IsOpenImmersion j]
    (n : ℕ) : boundedFiniteLocallyFreeKPullback j n = boundedFiniteLocallyFreeKRestrict j n :=
  Waldhausen.KMap_eq_of_iso (boundedFiniteLocallyFreePullback_isExact j)
    (boundedFiniteLocallyFreeRestrict_isExact j)
    (boundedFiniteLocallyFreeRestrictIsoPullback j).symm n

/-- Restriction commutes with pullback for any commutative square of open pairs. -/
@[colib_tag "COL-0322",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/Pullback.lean:97-103"
    "generalization" "The actual native strict restriction square for every commutative open pair"]
theorem boundedFiniteLocallyFreeKRestrict_pullback
    {U V : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (f : X ⟶ Y) (g : U ⟶ V)
    (h : i ≫ f = g ≫ j) (n : ℕ) :
    (boundedFiniteLocallyFreeKRestrict i n).comp (boundedFiniteLocallyFreeKPullback f n) =
      (boundedFiniteLocallyFreeKPullback g n).comp (boundedFiniteLocallyFreeKRestrict j n) := by
  rw [← boundedFiniteLocallyFreeKPullback_eq_restrict,
    ← boundedFiniteLocallyFreeKPullback_eq_restrict,
    ← boundedFiniteLocallyFreeKPullback_comp, ← boundedFiniteLocallyFreeKPullback_comp, h]

/-- The degreewise connective K-group is contravariantly functorial on all schemes. -/
def boundedFiniteLocallyFreeKFunctor (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (X.unop.boundedFiniteLocallyFreeK n)
  map f := GrpCat.ofHom (boundedFiniteLocallyFreeKPullback f.unop n)
  map_id X := by apply GrpCat.hom_ext; exact boundedFiniteLocallyFreeKPullback_id X.unop n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact boundedFiniteLocallyFreeKPullback_comp g.unop f.unop n

/-- Actual single-complex inclusion is natural for the canonical normalized KMaps. -/
@[colib_tag "COL-0322",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/PullbackNaturality.lean:41-49"
    "adaptation" "The actual original S-construction comparison square in every connective degree"]
theorem vectorBundleToBoundedFiniteLocallyFreeKMap_pullback (f : X ⟶ Y) (n : ℕ) :
    (boundedFiniteLocallyFreeKPullback f n).comp
        (vectorBundleToBoundedFiniteLocallyFreeKMap Y n) =
      (vectorBundleToBoundedFiniteLocallyFreeKMap X n).comp
        (Waldhausen.KMap (Modules.vectorBundleExactPullback f).waldhausenExact n) := by
  unfold boundedFiniteLocallyFreeKPullback vectorBundleToBoundedFiniteLocallyFreeKMap
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (vectorBundleComplexInclusionPullbackIso f) n

end AlgebraicGeometry.Scheme
