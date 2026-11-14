/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSimplicialPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Packaging the actual simplicial integral tensor pairing

Both naturality squares are supplied by the verified
ordinary-source pairing, on actual product maps. No chain product or tensor
comparison is supplied as a hypothesis.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry.Scheme
open scoped Simplicial TensorProduct
universe u v
namespace AlgebraicGeometry.PresheafWithTransfers

/-- Canonical integer modules on the same abelian groups and the same maps. -/
def intModuleSectionsFunctor : AddCommGrpCat.{v} ⥤ ModuleCat.{v} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id A := by ext a; rfl
  map_comp f g := by ext a; rfl

variable (k : Type u) [Field k]

/-- The actual ordinary reduced torus presheaf with its canonical Z-module action. -/
def reducedTorusIntPresheaf (q : ℕ) :
    (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ :=
  ((toPresheaf k).obj (reducedTorus k q)) ⋙ intModuleSectionsFunctor

/-- The existing literal U × Δ singular simplicial object, not another complex model. -/
def reducedTorusIntSimplicial (q : ℕ) :
    SimplicialObject ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) :=
  AlgebraicSimplex.simplicialPresheaf k (reducedTorusIntPresheaf k q)

/-- Ordinary tensor naturality, established on pure tensors of actual sections. -/
theorem reducedTorusSectionTensorMap_naturality (q : ℕ)
    {V U : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U) :
    (reducedTorusSectionTensorMap k V q).comp (TensorProduct.map
        (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f)).hom.toIntLinearMap
        (transfer (reducedTorus k 1) ((Cor.graphFunctor k).map f)).hom.toIntLinearMap) =
    ((transfer (reducedTorus k (q + 1)) ((Cor.graphFunctor k).map f)).hom.toIntLinearMap).comp
      (reducedTorusSectionTensorMap k U q) := by
  ext s b
  exact (reducedTorusSectionPairing_naturality k U q f s b).symm

/-- The actual degreewise tensor map, natural both in the smooth source and
in every simplex operator, including degeneracies. -/
def reducedTorusSimplicialTensorProduct (q : ℕ) :
    reducedTorusIntSimplicial k q ⊗ reducedTorusIntSimplicial k 1 ⟶
      reducedTorusIntSimplicial k (q + 1) where
  app n :=
    { app U := ModuleCat.ofHom (reducedTorusSectionTensorMap k
        (SmoothSite.product U.unop ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n.unop)) q)
      naturality U V f := by
        apply ModuleCat.hom_ext
        exact reducedTorusSectionTensorMap_naturality k q
          (SmoothSite.productMap f.unop (𝟙 _)) }
  naturality n m θ := by
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    exact reducedTorusSectionTensorMap_naturality k q
      (SmoothSite.productMap (𝟙 U.unop)
        ((AlgebraicSimplex.cosimplicialSmoothSite k).map θ.unop))

end AlgebraicGeometry.PresheafWithTransfers
