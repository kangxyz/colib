/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitEdge

/-!
# Actual zero coefficients in degreewise tensor

The original additive sheaf tensor in its coefficient argument makes tensor by an actual zero
module an actual zero complex. Its unique zero isomorphisms form a natural isomorphism, retaining
all original tensor objects and arrows.

No flatness hypothesis is needed. The current consumer is the first coefficient quotient row of
the restricted tensor-unit construction on bounded-flat perfect complexes.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped ZeroObject
universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance complexTensorZeroMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace
local instance complexTensorZeroPreadditive (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidalPreadditive X.toRingedSpace

/-- The actual tensor by any zero coefficient is zero in every original complex degree. -/
@[colib_ref "quillen" "Quillen c561118b: TensorZero.lean:30"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
theorem complexTensorLeft_isZero_of_coefficient {X : Scheme.{u}} {L : X.Modules} (hL : IsZero L)
    (K : CochainComplex X.Modules ℤ) : IsZero (((MonoidalCategory.tensorLeft
      L).mapHomologicalComplex (.up ℤ)).obj K) := by
  rw [IsZero.iff_id_eq_zero]
  ext n : 1
  exact ((MonoidalCategory.tensorRight (K.X n)).map_isZero hL).eq_of_src _ _

/-- The genuine tensor-zero objects and arrows identify naturally with the original zero complex. -/
@[colib_ref "quillen" "Quillen c561118b: TensorZero.lean:37"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
def complexTensorLeftZeroIso (X : Scheme.{u}) :
    (MonoidalCategory.tensorLeft (0 : X.Modules)).mapHomologicalComplex (.up ℤ) ≅ (Functor.const
      (CochainComplex X.Modules ℤ)).obj 0 :=
  NatIso.ofComponents
    (fun K => (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K).iso (isZero_zero _))
    (by
      intro K L f
      exact (complexTensorLeft_isZero_of_coefficient (isZero_zero _) K).eq_of_src _ _)

end AlgebraicGeometry.Scheme.Modules
