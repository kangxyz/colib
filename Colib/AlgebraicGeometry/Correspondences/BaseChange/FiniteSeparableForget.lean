/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.ForgetBase
public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.Composition
public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.Graph
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The actual finite separable forget-base functor

The objects keep their schemes and morphisms are native signed pushforwards.
Composition is the existing incidence Tor pairing and identity is the full
componentwise diagonal, including empty or disconnected sources.
Adapted from `Motivic/AlgebraicGeometry/Correspondences/BaseChange/FiniteSeparableForget.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local notation "r" => SmoothSite.finiteSeparableBaseMap k L
local notation "F" => SmoothSite.finiteSeparableForgetBase k L

/-- Forget a finite separable ground extension in the actual correspondence category. -/
def finiteSeparableForgetBase : Cor L ⥤ Cor k where
  obj X := ⟨(F).obj X.toSmoothSite⟩
  map {X Y} a := finiteCorrespondencesForgetBase r X.toSmoothSite.hom Y.toSmoothSite.hom a
  map_id X := by
    exact finiteCorrespondencesForgetBase_graph r X.toSmoothSite.hom X.toSmoothSite.hom
      (𝟙 X.toSmoothSite.left) (Category.id_comp _) (finite_genericPoints L X)
  map_comp {X Y Z} a b :=
    finiteCorrespondencesForgetBase_incidenceTorPairing r
      X.toSmoothSite.hom Y.toSmoothSite.hom Z.toSmoothSite.hom a b

instance finiteSeparableForgetBase_additive : (finiteSeparableForgetBase k L).Additive where
  map_add := by
    intro X Y a b
    exact map_add (finiteCorrespondencesForgetBase r X.toSmoothSite.hom Y.toSmoothSite.hom) a b

/-- The functor's morphism action is the existing finite pushforward. -/
@[simp]
theorem finiteSeparableForgetBase_map {X Y : Cor L} (a : X ⟶ Y) :
    (finiteSeparableForgetBase k L).map a =
      finiteCorrespondencesForgetBase r X.toSmoothSite.hom Y.toSmoothSite.hom a := rfl

/-- Every ordinary graph retains its full native componentwise graph cycle. -/
theorem finiteSeparableForgetBase_graph {X Y : SmoothSite (Spec (.of L))} (a : X ⟶ Y) :
    (finiteSeparableForgetBase k L).map ((graphFunctor L).map a) =
      (graphFunctor k).map ((F).map a) :=
  finiteCorrespondencesForgetBase_graph r X.hom Y.hom a.left
    (MorphismProperty.Over.w a) (finite_genericPoints L (Cor.mk X))

/-- Bundle the same actual forget-base functor with its additive structure. -/
def finiteSeparableForgetBaseAdditiveFunctor : Cor L ⥤+ Cor k :=
  AdditiveFunctor.of (finiteSeparableForgetBase k L)

end AlgebraicGeometry.Cor
