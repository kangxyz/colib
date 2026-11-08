/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.VectorBundle.Pullback
public import Colib.AlgebraicGeometry.KTheory.Restriction

/-!
# Contravariant vector-bundle K-theory on all schemes

The actual arbitrary-morphism bundle pullback induces `pullbackK`. Its identity
and composition laws follow from the geometric pullback isomorphisms, and on
open immersions it is the existing `restrictK`. This does not assert arbitrary
coherent G-theory pullback or substitute underived pullback for derived
pullback of perfect complexes. The existing native scheme K-groups retain their explicit
small-model universe `u + 1`; no essential-smallness assumption in universe `u` is introduced.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme
variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-- Contravariant pullback on genuine vector-bundle K-theory for every
scheme morphism. -/
def pullbackK (f : X ⟶ Y) (n : ℕ) : K Y n →* K X n :=
  (Modules.vectorBundleExactPullback f).smallKMap.{u + 1} n

/-- The public map uses exactly the actual geometric bundle pullback. -/
@[simp]
theorem pullbackK_eq_smallKMap (f : X ⟶ Y) (n : ℕ) :
    pullbackK f n = (Modules.vectorBundleExactPullback f).smallKMap.{u + 1} n :=
      rfl

/-- Identity pullback is the identity on the original scheme K-groups. -/
@[simp high]
theorem pullbackK_id (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    pullbackK (𝟙 X) n = MonoidHom.id (K X n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso.{u + 1}
    (F := Modules.vectorBundleExactPullback (𝟙 X))
    (G := ExactFunctor.id
      (Modules.vectorBundleExactStructure X))
    (Modules.vectorBundlePullbackIdIso X) n).trans
    (ExactFunctor.smallKMap_id.{u + 1} _ n)

/-- Actual bundle pullback is strictly contravariantly functorial on K-groups. -/
@[simp high]
theorem pullbackK_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    pullbackK (f ≫ g) n = (pullbackK f n).comp (pullbackK g n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso.{u + 1}
    (F := Modules.vectorBundleExactPullback (f ≫ g))
    (G := (Modules.vectorBundleExactPullback g).comp
      (Modules.vectorBundleExactPullback f))
    (Modules.vectorBundlePullbackCompIso f g) n).trans
    (ExactFunctor.smallKMap_comp.{u + 1} _ _ n)

/-- On an open immersion, the new pullback is exactly the existing geometric
open-restriction K-map. -/
theorem pullbackK_eq_restrictK (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    pullbackK j n = restrictK j n :=
  ExactFunctor.smallKMap_eq_of_natIso.{u + 1}
    (F := Modules.vectorBundleExactPullback j)
    (G := Modules.vectorBundleExactRestrict j)
    (Modules.vectorBundleRestrictIsoPullback j).symm n

/-- The vector-bundle K-group in each nonnegative degree forms a
contravariant functor on the full category of schemes. -/
def KFunctor (n : ℕ) : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (K X.unop n)
  map f := GrpCat.ofHom (pullbackK f.unop n)
  map_id X := by
    apply GrpCat.hom_ext
    exact pullbackK_id X.unop n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact pullbackK_comp g.unop f.unop n

/-- The functor retains the canonical pullback on each map. -/
@[simp]
theorem KFunctor_map {X Y : AlgebraicGeometry.Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) : ((KFunctor n).map f).hom = pullbackK f.unop n := rfl

/-- A scheme isomorphism induces inverse K-theory pullbacks. -/
theorem pullbackK_iso_hom_inv (e : X ≅ Y) (n : ℕ) :
    (pullbackK e.hom n).comp (pullbackK e.inv n) = MonoidHom.id (K X n) := by
  rw [← pullbackK_comp, e.hom_inv_id, pullbackK_id]

end AlgebraicGeometry.Scheme

attribute [colib_tag "COL-0322",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/Scheme/Pullback.lean:37-99"
    "adaptation"
    "Actual arbitrary native vector-bundle pullback on the original small-model K-groups"]
  AlgebraicGeometry.Scheme.pullbackK
  AlgebraicGeometry.Scheme.pullbackK_comp
  AlgebraicGeometry.Scheme.pullbackK_eq_restrictK
  AlgebraicGeometry.Scheme.KFunctor
