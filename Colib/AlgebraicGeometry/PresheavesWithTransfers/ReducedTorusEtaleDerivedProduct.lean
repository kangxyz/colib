/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleFixedDerivedTensor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSignedTotalRoof

/-! # The original AW roof in the smooth étale sheaf derived category

Exact sheafification preserves the quasi-isomorphism of the actual AW leg.
The product below inverts precisely that leg and keeps the original pairing.
The fixed-factor derived source is supplied by the concrete K-flat computation,
not by assuming an abstract product comparison. No identification with a separate
motivic beta operation or two-variable derived tensor is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

attribute [local instance] smoothEtaleIntegral_isMonoidal_W Sheaf.monoidalCategory
  Sheaf.monoidalPreadditive etaleKFlat_tensorAdditive etaleKFlat_tensorObjAdditive
  etaleKFlat_hasMapBifunctor

local notation "P" => SmoothEtaleIntegralPresheaves k
local notation "S" => SmoothEtaleIntegralSheaves k
local notation "a" => smoothEtaleIntegralSheafify k

/-- Exact sheafification sends the extended original AW leg to a quasi-isomorphism. -/
instance reducedTorusEtaleAW_quasiIso (q : ℕ) :
    QuasiIso (((a).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap (reducedTorusPresheafAW k q)
        ComplexShape.embeddingDownNat)) := by
  let : (a).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels a
  infer_instance

variable [HasDerivedCategory.{v} (SmoothEtaleIntegralSheaves k)]

/-- Extend the original presheaf chains, sheafify, then localize. -/
def integralEtaleChainToDerived : ChainComplex P ℕ ⥤ DerivedCategory S :=
  ComplexShape.embeddingDownNat.extendFunctor _ ⋙
    (a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The actual sheafified AW leg, not a replacement map, is invertible after localization. -/
instance reducedTorusEtaleDerivedAW_isIso (q : ℕ) :
    IsIso ((integralEtaleChainToDerived k).map (reducedTorusPresheafAW k q)) := by
  change IsIso (DerivedCategory.Q.map (((a).mapHomologicalComplex (.up ℤ)).map
    (HomologicalComplex.extendMap (reducedTorusPresheafAW k q)
      ComplexShape.embeddingDownNat)))
  infer_instance

/-- The literal sheafified AW roof with its original ordinary tensor source. -/
def reducedTorusEtaleOrdinaryDerivedProduct (q : ℕ) :
    (integralEtaleChainToDerived k).obj (HomologicalComplex.tensorObj
        (reducedTorusOrdinaryIntegralChains k q)
        (reducedTorusOrdinaryIntegralChains k 1)) ⟶
      (integralEtaleChainToDerived k).obj (reducedTorusOrdinaryIntegralChains k (q + 1)) :=
  inv ((integralEtaleChainToDerived k).map (reducedTorusPresheafAW k q)) ≫
    (integralEtaleChainToDerived k).map (reducedTorusPresheafChainPairing k q)

/-- Precomposing the roof with its actual AW leg recovers the original pairing. -/
theorem reducedTorusEtaleOrdinaryDerivedProduct_fac (q : ℕ) :
    (integralEtaleChainToDerived k).map (reducedTorusPresheafAW k q) ≫
        reducedTorusEtaleOrdinaryDerivedProduct k q =
      (integralEtaleChainToDerived k).map (reducedTorusPresheafChainPairing k q) := by
  simp [reducedTorusEtaleOrdinaryDerivedProduct]

/-- The concrete fixed-factor derived source compared with the literal AW roof source. -/
def reducedTorusEtaleDerivedProductSourceIso (q : ℕ) :
    (reducedTorusEtaleFixedDerivedTensor k).obj
        (DerivedCategory.Q.obj (reducedTorusEtaleOrdinaryCochains k q)) ≅
      (integralEtaleChainToDerived k).obj (HomologicalComplex.tensorObj
        (reducedTorusOrdinaryIntegralChains k q)
        (reducedTorusOrdinaryIntegralChains k 1)) :=
  (reducedTorusEtaleFixedDerivedTensorSheafifyIso k q).trans
    (DerivedCategory.Q.mapIso
      (((a).mapHomologicalComplex (.up ℤ)).mapIso (reducedTorusSignedTotalChainIso k q)))

/-- The original AW/pairing product with the concrete fixed-factor derived source. -/
def reducedTorusEtaleFixedDerivedProduct (q : ℕ) :
    (reducedTorusEtaleFixedDerivedTensor k).obj
        (DerivedCategory.Q.obj (reducedTorusEtaleOrdinaryCochains k q)) ⟶
      (integralEtaleChainToDerived k).obj (reducedTorusOrdinaryIntegralChains k (q + 1)) :=
  (reducedTorusEtaleDerivedProductSourceIso k q).hom ≫
    reducedTorusEtaleOrdinaryDerivedProduct k q

/-- Transporting the actual AW leg to the derived source recovers the same pairing. -/
theorem reducedTorusEtaleFixedDerivedProduct_fac (q : ℕ) :
    ((integralEtaleChainToDerived k).map (reducedTorusPresheafAW k q) ≫
        (reducedTorusEtaleDerivedProductSourceIso k q).inv) ≫
      reducedTorusEtaleFixedDerivedProduct k q =
        (integralEtaleChainToDerived k).map (reducedTorusPresheafChainPairing k q) := by
  simp [reducedTorusEtaleFixedDerivedProduct, Category.assoc,
    reducedTorusEtaleOrdinaryDerivedProduct_fac]

end AlgebraicGeometry.PresheafWithTransfers
