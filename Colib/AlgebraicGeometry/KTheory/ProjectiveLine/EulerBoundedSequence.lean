/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.EulerCoefficientExact
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BoundedBelowTensor

/-! # The Euler sequence of bounded-below functors

The actual coordinate arrows induce natural transformations after termwise tensor.
The Euler sequence is pointwise short exact even when the input terms are not flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.SheafOfModules.Tensor

namespace AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

universe u

variable {Y : Scheme.{u}}

local instance : MonoidalCategory Y.Modules :=
  SheafOfModules.monoidalCategorySheafTensor Y.sheaf

local instance : MonoidalPreadditive Y.Modules := by
  let := Abelian.hasFiniteBiproducts (C := Y.Modules)
  exact SheafOfModules.monoidalPreadditiveSheafTensor Y.sheaf

local notation "c" => ComplexShape.up ℤ

/-- A morphism of vector bundles acts on the coefficient of the right tensor functor. -/
def tensorVectorBundleRightMap {L M : Y.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] (f : L ⟶ M) :
    tensorVectorBundleRight L ⟶ tensorVectorBundleRight M where
  app K := ObjectProperty.homMk
    ((((curriedTensor Y.Modules).flip.map f).mapHomologicalComplex c).app K.obj)
  naturality {K J} g := by
    apply ObjectProperty.hom_ext
    exact (((curriedTensor Y.Modules).flip.map f).mapHomologicalComplex c).naturality g.hom

/-- An isomorphism of vector bundles induces the actual coefficient natural isomorphism. -/
def tensorVectorBundleRightIso {L M : Y.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] (e : L ≅ M) :
    tensorVectorBundleRight L ≅ tensorVectorBundleRight M :=
  let E := NatIso.mapHomologicalComplex ((curriedTensor Y.Modules).flip.mapIso e) c
  NatIso.ofComponents (fun K => ObjectProperty.isoMk (P := objects Y) (E.app K.obj))
    (fun {_ _} f => by
      apply ObjectProperty.hom_ext
      exact E.hom.naturality f.hom)

/-- Associativity of the literal tensor functors, after passing to complexes. -/
def tensorVectorBundleRightTensorIso {L M N : Y.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (e : L ⊗ M ≅ N) :
    tensorVectorBundleRight L ⋙ tensorVectorBundleRight M ≅ tensorVectorBundleRight N := by
  let E : tensorRight L ⋙ tensorRight M ≅ tensorRight N :=
    (tensorRightTensor L M).symm ≪≫ (curriedTensor Y.Modules).flip.mapIso e
  let F := Functor.mapHomologicalComplexCompIso E c
  exact NatIso.ofComponents (fun K => ObjectProperty.isoMk (P := objects Y) (F.app K.obj))
    (fun {_ _} f => by
      apply ObjectProperty.hom_ext
      exact F.hom.naturality f.hom)

/-- Right tensor by a module isomorphic to the structure sheaf is the identity. -/
def tensorVectorBundleRightUnitIso {L : Y.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]
    (e : L ≅ 𝟙_ Y.Modules) : tensorVectorBundleRight L ≅ 𝟭 (Obj Y) := by
  let E : tensorRight L ≅ 𝟭 Y.Modules :=
    (curriedTensor Y.Modules).flip.mapIso e ≪≫ rightUnitorNatIso Y.Modules
  let F := NatIso.mapHomologicalComplex E c ≪≫ Functor.mapHomologicalComplexIdIso _ c
  exact NatIso.ofComponents (fun K => ObjectProperty.isoMk (P := objects Y) (F.app K.obj))
    (fun {_ _} f => by
      apply ObjectProperty.hom_ext
      exact F.hom.naturality f.hom)

/-- The vector-bundle Euler arrows still compose to zero on complexes. -/
theorem tensorVectorBundleRightMap_comp_eq_zero {L M N : Y.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
    {f : L ⟶ M} {g : M ⟶ N} (h : f ≫ g = 0) :
    tensorVectorBundleRightMap f ≫ tensorVectorBundleRightMap g = 0 := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  apply HomologicalComplex.Hom.ext
  funext i
  change ((curriedTensor Y.Modules).obj (K.obj.X i)).map f ≫
    ((curriedTensor Y.Modules).obj (K.obj.X i)).map g = 0
  rw [← Functor.map_comp, h, Functor.map_zero]

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "S" => projectiveLineEulerSequence X

local instance : SymmetricCategory (P).Modules :=
  SheafOfModules.symmetricCategorySheafTensor (P).sheaf

/-- The actual Euler arrows tensored with a bounded-below perfect complex. -/
def projectiveLineEulerBoundedSequence (K : Obj P) : ShortComplex (Obj P) :=
  ShortComplex.mk ((tensorVectorBundleRightMap (projectiveLineEulerSequence X).f).app K)
    ((tensorVectorBundleRightMap (projectiveLineEulerSequence X).g).app K)
    (NatTrans.congr_app (tensorVectorBundleRightMap_comp_eq_zero (S).zero) K)

/-- The Euler sequence has the inherited conflation property on native complexes. -/
theorem projectiveLineEulerBoundedSequence_shortExact (K : Obj P) :
    ((projectiveLineEulerBoundedSequence X K).map (objects P).ι).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  change ((S).map ((curriedTensor (P).Modules).obj (K.obj.X i))).ShortExact
  let e := BraidedCategory.tensorLeftIsoTensorRight (K.obj.X i)
  let E := ShortComplex.mapNatIso (S) e
  exact ShortComplex.shortExact_of_iso E.symm
    (projectiveLineEulerSequence_tensor_shortExact X (K.obj.X i))

end AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect
