/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSimplicialTensor
public import Colib.AlgebraicGeometry.Simplex.SheafifiedChains
public import Colib.AlgebraicGeometry.Simplex.CoefficientChange
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Topology
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # The underlying abelian singular chains of the integral reduced torus

Forgetting the canonical integer action preserves the actual simplex maps and
alternating differentials, not merely the isomorphism class of their homology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicSimplex
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The canonical integer action forgets to the identical abelian group. -/
def intModuleSectionsForgetIso :
    intModuleSectionsFunctor.{u} ⋙
      forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat ≅ 𝟭 AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Forgetting the canonical integer action recovers the original simplicial presheaf. -/
def ordinaryIntSimplicialUnderlyingIso
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    ((SimplicialObject.whiskering _ _).obj
      ((Functor.whiskeringRight _ _ _).obj
        (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat))).obj
          (simplicialPresheaf k (P ⋙ intModuleSectionsFunctor)) ≅
      simplicialPresheaf k P :=
  simplicialPresheafWhiskerIso k (P ⋙ intModuleSectionsFunctor) _ ≪≫
    (simplicialPresheafFunctor k).mapIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft P intModuleSectionsForgetIso ≪≫ Functor.rightUnitor P)

/-- The underlying alternating complex is the original ordinary singular complex. -/
def reducedTorusIntChainsUnderlyingIso (q : ℕ) :
    (((Functor.whiskeringRight _ _ _).obj
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat)).mapHomologicalComplex (.down ℕ)).obj
        ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q)) ≅
      (singularChainsFunctor k).obj ((toPresheaf k).obj (reducedTorus k q)) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    ((Functor.whiskeringRight _ _ _).obj
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat))).app
        (reducedTorusIntSimplicial k q) ≪≫
    (alternatingFaceMapComplex _).mapIso (ordinaryIntSimplicialUnderlyingIso k
      ((toPresheaf k).obj (reducedTorus k q)))

/-- Canonical sheafification commutes with forgetting the integer action. -/
def reducedTorusIntSheafChainsUnderlyingIso (q : ℕ) :
    ((sheafCompose (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat)).mapHomologicalComplex (.down ℕ)).obj
        ((sheafifiedSingularChainsFunctor k
          (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))).obj
            (reducedTorusIntPresheaf k q)) ≅
      (sheafifiedSingularChainsFunctor k
        (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))).obj
          ((toPresheaf k).obj (reducedTorus k q)) := by
  let J := SmoothSite.etaleTopology (Spec (CommRingCat.of k))
  let F := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat
  let e := sheafComposeNatIso J F
    (sheafificationAdjunction J (ModuleCat.{u + 1} ℤ))
    (sheafificationAdjunction J AddCommGrpCat.{u + 1})
  exact ((Functor.mapHomologicalComplexCompIso e (.down ℕ)).app
      ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q))).symm ≪≫
    ((presheafToSheaf J AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)).mapIso
      (reducedTorusIntChainsUnderlyingIso k q)

end AlgebraicGeometry.PresheafWithTransfers
