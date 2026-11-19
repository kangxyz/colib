/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleTensor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusOrdinaryTermFlat
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusIntegralEtaleSignedPlacement

/-! # The native ordinary and signed sheafified endpoints

This comparison commutes exact sheafification past extension by zero, and changes
only the equal embeddings `n ↦ -n` and `n ↦ 0 - n`. Its signed specialization uses
the existing shift functor, without a new sign convention. No parameter/topology
comparison is inverted, and no product or motivic beta identification is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

/-- The two native nonpositive embeddings differ only by `zero_sub`. -/
theorem reducedTorus_embeddingDownNat_eq_upIntLE_zero :
    ComplexShape.embeddingDownNat = ComplexShape.embeddingUpIntLE 0 := by
  have embedding_ext {e e' : ComplexShape.Embedding (.down ℕ) (.up ℤ)}
      (h : e.f = e'.f) : e = e' := by
    cases e
    cases e'
    cases h
    rfl
  apply embedding_ext
  funext n
  change -(n : ℤ) = 0 - (n : ℤ)
  exact (zero_sub (n : ℤ)).symm

variable (k : Type u) [Field k]

local notation "P" => SmoothEtaleIntegralPresheaves k
local notation "S" => SmoothEtaleIntegralSheaves k
local notation "a" => smoothEtaleIntegralSheafify k

/-- Natural endpoint comparison retaining the original extension/sheafification iso. -/
def smoothEtaleIntegralNativeExtensionIso :
    ComplexShape.embeddingDownNat.extendFunctor P ⋙ (a).mapHomologicalComplex (.up ℤ) ≅
      (a).mapHomologicalComplex (.down ℕ) ⋙
        (ComplexShape.embeddingUpIntLE 0).extendFunctor S :=
  (Stacks.DerivedIndexing.mapExtendNatIso a ComplexShape.embeddingDownNat).symm ≪≫
    Functor.isoWhiskerLeft ((a).mapHomologicalComplex (.down ℕ))
      (eqToIso (congrArg
        (fun e : ComplexShape.Embedding (.down ℕ) (.up ℤ) => e.extendFunctor S)
        reducedTorus_embeddingDownNat_eq_upIntLE_zero))

/-- The endpoint comparison is natural for the original chain map, not just its objects. -/
theorem smoothEtaleIntegralNativeExtensionIso_naturality
    {K L : ChainComplex P ℕ} (f : K ⟶ L) :
    ((a).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat) ≫
      ((smoothEtaleIntegralNativeExtensionIso k).app L).hom =
    ((smoothEtaleIntegralNativeExtensionIso k).app K).hom ≫
      HomologicalComplex.extendMap (((a).mapHomologicalComplex (.down ℕ)).map f)
        (ComplexShape.embeddingUpIntLE 0) :=
  (smoothEtaleIntegralNativeExtensionIso k).hom.naturality f

/-- The actual weight-q ordinary tensor model has the original native parameter endpoint. -/
def reducedTorusEtaleNativeOrdinaryEndpointIso (q : ℕ) :
    ((a).mapHomologicalComplex (.up ℤ)).obj (reducedTorusOrdinaryIntegralCochains k q) ≅
      reducedTorusIntegralEtaleOrdinaryCochain k q :=
  (smoothEtaleIntegralNativeExtensionIso k).app (reducedTorusOrdinaryIntegralChains k q)

/-- Native negative weight placement, without changing any differential sign by hand. -/
def reducedTorusEtaleNativeSignedEndpointIso (q : ℕ) :
    (((a).mapHomologicalComplex (.up ℤ)).obj
        (reducedTorusOrdinaryIntegralCochains k q))⟦-(q : ℤ)⟧ ≅
      reducedTorusIntegralEtaleOrdinarySigned k q :=
  (shiftFunctor _ (-(q : ℤ))).mapIso (reducedTorusEtaleNativeOrdinaryEndpointIso k q)

end AlgebraicGeometry.PresheafWithTransfers
