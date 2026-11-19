/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusIntegralParameter

/-! # Étale sheafification of the actual integral parameter square

The reindexed target remains sheafification of the reindexed presheaf complex.
No assertion that sheafification commutes isomorphically with torus sections is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The native coefficient/sheafification comparison on arbitrary integral chains. -/
def integralEtaleChainsForgetIso
    (K : ChainComplex ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤
      ModuleCat.{u + 1} ℤ) ℕ) :
    let J := SmoothSite.etaleTopology (Spec (CommRingCat.of k))
    let F := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat
    let U := ((Functor.whiskeringRight _ _ _).obj F).mapHomologicalComplex (.down ℕ)
    let M := (presheafToSheaf J (ModuleCat.{u + 1} ℤ)).mapHomologicalComplex (.down ℕ)
    let A := (presheafToSheaf J AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)
    let H := (sheafCompose J F).mapHomologicalComplex (.down ℕ)
    H.obj (M.obj K) ≅ A.obj (U.obj K) := by
  intro J F U M A H
  exact ((Functor.mapHomologicalComplexCompIso
    (sheafComposeNatIso J F (sheafificationAdjunction J (ModuleCat.{u + 1} ℤ))
      (sheafificationAdjunction J AddCommGrpCat.{u + 1})) (.down ℕ)).app K).symm

/-- Naturality of the actual integral sheafification comparison. -/
theorem integralEtaleChainsForgetIso_naturality
    {K L : ChainComplex ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤
      ModuleCat.{u + 1} ℤ) ℕ} (f : K ⟶ L) :
    let J := SmoothSite.etaleTopology (Spec (CommRingCat.of k))
    let F := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat
    let U := ((Functor.whiskeringRight _ _ _).obj F).mapHomologicalComplex (.down ℕ)
    let M := (presheafToSheaf J (ModuleCat.{u + 1} ℤ)).mapHomologicalComplex (.down ℕ)
    let A := (presheafToSheaf J AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)
    let H := (sheafCompose J F).mapHomologicalComplex (.down ℕ)
    H.map (M.map f) ≫ (integralEtaleChainsForgetIso k L).hom =
      (integralEtaleChainsForgetIso k K).hom ≫ A.map (U.map f) := by
  intro J F U M A H
  exact (Functor.mapHomologicalComplexCompIso
    (sheafComposeNatIso J F (sheafificationAdjunction J (ModuleCat.{u + 1} ℤ))
      (sheafificationAdjunction J AddCommGrpCat.{u + 1})) (.down ℕ)).inv.naturality f

/-- Étale sheafification of the actual chain insertion/pairing square.
The coefficient comparison is native and the original parameter map is unchanged. -/
theorem reducedTorusEtaleParameterSquare (q : ℕ) :
    let J := SmoothSite.etaleTopology (Spec (CommRingCat.of k))
    let F := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat
    let M := (presheafToSheaf J (ModuleCat.{u + 1} ℤ)).mapHomologicalComplex (.down ℕ)
    let A := (presheafToSheaf J AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)
    let H := (sheafCompose J F).mapHomologicalComplex (.down ℕ)
    let G := SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
    let T := (AlgebraicSimplex.parameterReindex k
      (A := AddCommGrpCat.{u + 1}) G).mapHomologicalComplex (.down ℕ)
    let T' := (AlgebraicSimplex.parameterReindex k
      (A := ModuleCat.{u + 1} ℤ) G).mapHomologicalComplex (.down ℕ)
    let K := (alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q)
    let L := T'.obj ((alternatingFaceMapComplex _).obj
      (reducedTorusIntSimplicial k (q + 1)))
    H.map (M.map (reducedTorusChainCoordinateInsertion k q ≫
      T'.map (reducedTorusPresheafChainPairing k q))) ≫
        (integralEtaleChainsForgetIso k L).hom ≫
          A.map (T.map (reducedTorusIntChainsUnderlyingIso k (q + 1)).hom) =
    (integralEtaleChainsForgetIso k K).hom ≫
      A.map (reducedTorusIntChainsUnderlyingIso k q).hom ≫
        A.map (reducedTorusSingularParameterProduct k q) := by
  intro J F M A H G T T' K L
  rw [← Category.assoc, integralEtaleChainsForgetIso_naturality]
  rw [Category.assoc, ← A.map_comp, reducedTorusIntChainsUnderlyingIso_parameter]
  rw [A.map_comp]

end AlgebraicGeometry.PresheafWithTransfers
