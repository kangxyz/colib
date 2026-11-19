/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleKFlat
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleTensorTotal
public import StacksFrontier.Homology.DerivedTensor.KFlatDescent

/-! # Fixed-factor derived tensor on smooth étale integral sheaves

The right factor is the actual sheafified weight-one complex. Its proved K-flatness
permits descent in the left variable. The computation comparison identifies the
value on the weight-q complex with the sheafification of the original ordinary
signed total, localized in the sheaf category. This is neither a two-variable
derived tensor construction nor an assertion about the beta/AW product map.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

attribute [local instance] smoothEtaleIntegral_isMonoidal_W Sheaf.monoidalCategory
  Sheaf.monoidalPreadditive etaleKFlat_tensorAdditive etaleKFlat_tensorObjAdditive
  etaleKFlat_hasMapBifunctor

local notation "S" => SmoothEtaleIntegralSheaves k
local notation "a" => smoothEtaleIntegralSheafify k

/-- The original sheafified weight-one cochains satisfy the descent obligation. -/
instance reducedTorusEtaleWeightOne_isKFlat :
    Stacks.DerivedTensor.IsKFlat (curriedTensor S)
      (reducedTorusEtaleOrdinaryCochains k 1) where
  acyclic_totRight := reducedTorusEtaleOrdinaryCochains_kFlat k 1

variable [HasDerivedCategory.{v} (SmoothEtaleIntegralSheaves k)]

/-- The actual fixed-right-factor tensor descended to the sheaf derived category. -/
def reducedTorusEtaleFixedDerivedTensor : DerivedCategory S ⥤ DerivedCategory S :=
  Stacks.DerivedTensor.derivedTensor (curriedTensor S)
    (reducedTorusEtaleOrdinaryCochains k 1)

/-- Its value on the actual weight-q complex is computed by the native signed total. -/
def reducedTorusEtaleFixedDerivedTensorObjIso (q : ℕ) :
    (reducedTorusEtaleFixedDerivedTensor k).obj
        (DerivedCategory.Q.obj (reducedTorusEtaleOrdinaryCochains k q)) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor
        (reducedTorusEtaleOrdinaryCochains k q)
        (reducedTorusEtaleOrdinaryCochains k 1) (curriedTensor S) (.up ℤ)) :=
  (Stacks.DerivedTensor.derivedTensorQIso (curriedTensor S)
    (reducedTorusEtaleOrdinaryCochains k 1)).app (reducedTorusEtaleOrdinaryCochains k q)

/-- The same derived value is the localized sheafification of the original signed total. -/
def reducedTorusEtaleFixedDerivedTensorSheafifyIso (q : ℕ) :
    (reducedTorusEtaleFixedDerivedTensor k).obj
        (DerivedCategory.Q.obj (reducedTorusEtaleOrdinaryCochains k q)) ≅
      DerivedCategory.Q.obj (((a).mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.mapBifunctor
          (reducedTorusOrdinaryIntegralCochains k q)
          (reducedTorusOrdinaryIntegralCochains k 1)
          (curriedTensor (SmoothEtaleIntegralPresheaves k)) (.up ℤ))) :=
  (reducedTorusEtaleFixedDerivedTensorObjIso k q).trans
    (DerivedCategory.Q.mapIso (reducedTorusEtaleTensorTotalIso k q)).symm

/-- Returning across the ordinary sheafification comparison gives the canonical computation. -/
theorem reducedTorusEtaleFixedDerivedTensorSheafifyIso_fac (q : ℕ) :
    (reducedTorusEtaleFixedDerivedTensorSheafifyIso k q).hom ≫
        (DerivedCategory.Q.mapIso (reducedTorusEtaleTensorTotalIso k q)).hom =
      (reducedTorusEtaleFixedDerivedTensorObjIso k q).hom := by
  simp [reducedTorusEtaleFixedDerivedTensorSheafifyIso]

end AlgebraicGeometry.PresheafWithTransfers
