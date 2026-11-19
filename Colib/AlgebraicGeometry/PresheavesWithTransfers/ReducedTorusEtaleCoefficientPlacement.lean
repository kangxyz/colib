/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleParameterReindex
public import Colib.Algebra.Homology.SignedParameterTransport
public import Colib.Algebra.Homology.ParameterExtensionTransport

/-! # Native coefficient comparison before signed weight placement

This keeps the actual integral singular complex and its native extension.
Recovered comparison declarations from the retained signed-comparison source.
It does not identify the inverse-AW roof with the derived tensor parameter map.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor AlgebraicTopology AlgebraicSimplex
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
local instance coefficientSignedForget_additive :
    (sheafCompose (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat)).Additive where
  map_add := by intros; rfl

/-- The native coefficient/reindex comparison, with explicit components. -/
def integralEtaleCoefficientParameterComparison :
    let J := SmoothSite.etaleTopology (Spec (CommRingCat.of k))
    let R := SmoothSite.Contraction.parameterProduct
      (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
    let E := sheafCompose J (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat)
    R.sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ) J J ⋙ E ⟶
      E ⋙ R.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J J where
  app X := 𝟙 _
  naturality X Y f := by
    change _ ≫ (𝟙 _) = (𝟙 _) ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl

/-- The native complex comparison includes the standard composition isomorphisms. -/
def integralEtaleCoefficientComplexComparison :
    let J := SmoothSite.etaleTopology (Spec (CommRingCat.of k))
    let R := SmoothSite.Contraction.parameterProduct
      (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
    let E := sheafCompose J (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat)
    (R.sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ) J J).mapHomologicalComplex (.up ℤ) ⋙
        E.mapHomologicalComplex (.up ℤ) ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙
        (R.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J J).mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).hom ≫
    NatTrans.mapHomologicalComplex (integralEtaleCoefficientParameterComparison k) (.up ℤ) ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).inv

instance integralEtaleCoefficientComplexComparison_commShift :
    NatTrans.CommShift (integralEtaleCoefficientComplexComparison k) ℤ := by
  unfold integralEtaleCoefficientComplexComparison
  infer_instance

/-- The actual chain comparison is the pre-existing underlying-sheaf isomorphism. -/
theorem integralEtaleChainsForgetIso_reducedTorus (q : ℕ) :
    (integralEtaleChainsForgetIso k
      ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q))).hom ≫
      ((presheafToSheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
        AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)).map
          (reducedTorusIntChainsUnderlyingIso k q).hom =
      (reducedTorusIntSheafChainsUnderlyingIso k q).hom := rfl

/-- Forgetting coefficients on the original extended integral chains. -/
def reducedTorusIntegralCoefficientExtendIso (q : ℕ) :
    let J := SmoothSite.etaleTopology (Spec (CommRingCat.of k))
    let E := sheafCompose J (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat)
    let e := ComplexShape.embeddingUpIntLE 0
    let M := (sheafifiedSingularChainsFunctor k J).obj (reducedTorusIntPresheaf k q)
    (E.mapHomologicalComplex (.up ℤ)).obj (M.extend e) ≅
      ((sheafifiedSingularChainsFunctor k J).obj
        ((toPresheaf k).obj (reducedTorus k q))).extend e :=
  (Stacks.DerivedIndexing.mapExtendIso _ _ _).symm ≪≫
    ((ComplexShape.embeddingUpIntLE 0).extendFunctor _).mapIso
      (reducedTorusIntSheafChainsUnderlyingIso k q)

/-- Sheafify the original integral coordinate insertion and pairing, then use
its native one-way parameter reindexing comparison. -/
def reducedTorusIntegralEtaleParameterMap (q : ℕ) :
    let J := SmoothSite.etaleTopology (Spec (CommRingCat.of k))
    let R := SmoothSite.Contraction.parameterProduct
      (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
    let K := (sheafifiedSingularChainsFunctor k J).obj (reducedTorusIntPresheaf k q)
    let L := (sheafifiedSingularChainsFunctor k J).obj (reducedTorusIntPresheaf k (q + 1))
    K ⟶ ((R.sheafPushforwardContinuous
      (ModuleCat.{u + 1} ℤ) J J).mapHomologicalComplex (.down ℕ)).obj L := by
  intro J R K L
  exact R.sheafifyReindexComplexMap J J _ (.down ℕ)
    (reducedTorusChainCoordinateInsertion k q ≫
      (Functor.mapHomologicalComplex (parameterReindex k (A := ModuleCat.{u + 1} ℤ)
        (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))))
          (.down ℕ)).map (reducedTorusPresheafChainPairing k q))

end AlgebraicGeometry.PresheafWithTransfers
