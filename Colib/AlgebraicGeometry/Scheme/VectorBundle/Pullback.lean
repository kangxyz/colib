/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Restriction
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackLocallySplit

/-!
# Exact pullback of native vector bundles along arbitrary scheme morphisms

The functor lifts the actual native module pullback to `Scheme.Vect`. Its exactness uses
local splitting of a short exact sequence with finite locally free quotient, not flatness
of the scheme morphism or a splitting on the whole scheme. Identity, composition and open
restriction comparisons retain the actual native module isomorphisms.

Implementation provenance: the vector-bundle pullback used by
`Quillen/AlgebraicGeometry/Scheme/Pullback.lean` at `c561118b` and the native Stacks
`shortExact_map_pullback_of_isFiniteLocallyFree` theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The actual geometric pullback on native finite locally free module sheaves. -/
def vectorBundlePullback (f : X ⟶ Y) : Y.Vect ⥤ X.Vect :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ pullback f)
    (fun M => SheafOfModules.IsFiniteLocallyFree.pullback_scheme f M.obj M.property)

instance vectorBundlePullback_additive (f : X ⟶ Y) :
    (vectorBundlePullback f).Additive := by
  dsimp [vectorBundlePullback]
  infer_instance

@[simp]
theorem vectorBundlePullback_obj (f : X ⟶ Y) (M : Y.Vect) :
    ((vectorBundlePullback f).obj M).obj = (pullback f).obj M.obj := rfl

@[simp]
theorem vectorBundlePullback_map (f : X ⟶ Y) {M N : Y.Vect} (g : M ⟶ N) :
    ((vectorBundlePullback f).map g).hom = (pullback f).map g.hom := rfl

/-- Every inherited vector-bundle conflation stays short exact under arbitrary pullback. -/
@[colib_tag "COL-0322",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/Scheme/Pullback.lean:37-47"
    "adaptation" "The actual native exact vector-bundle pullback used by the original K-map"]
def vectorBundleExactPullback (f : X ⟶ Y) :
    ExactFunctor (vectorBundleExactStructure Y) (vectorBundleExactStructure X) where
  toFunctor := vectorBundlePullback f
  map_conflation S hS := by
    let : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (S.map (ObjectProperty.ι _)).X₃ := S.X₃.property
    exact shortExact_map_pullback_of_isFiniteLocallyFree f
      (S.map (ObjectProperty.ι _)) hS

/-- The native identity comparison lifted through the full inclusion. -/
def vectorBundlePullbackIdIso (X : Scheme.{u}) :
    vectorBundlePullback (𝟙 X) ≅ 𝟭 X.Vect :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _) (pullbackId X))

/-- The native composition comparison lifted through the full inclusion. -/
def vectorBundlePullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    vectorBundlePullback (f ≫ g) ≅ vectorBundlePullback g ⋙ vectorBundlePullback f :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _) (pullbackComp f g).symm)

/-- Actual open restriction agrees with arbitrary pullback along that open immersion. -/
def vectorBundleRestrictIsoPullback (j : X ⟶ Y) [IsOpenImmersion j] :
    vectorBundleRestrict j ≅ vectorBundlePullback j :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _) (restrictFunctorIsoPullback j))

end AlgebraicGeometry.Scheme.Modules
