/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.ParameterProduct
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The unit-section kernel of the motivic parameter map

The original parameter projection splits evaluation at one. The signed
weight-raising cochain map factors through the kernel of that evaluation,
with the same map to the reindexed cochains.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ

/-- Pullback along the original projection to the smooth scheme. -/
def torusParameterSheafConstant :
    𝟭 (Sheaf Jₖ AddCommGrpCat.{u + 1}) ⟶ torusParameterSheafFunctor k where
  app P := ⟨SmoothSite.Contraction.constant P.obj (SmoothSite.multiplicativeGroupObject Sₖ)⟩
  naturality P Q f := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    let G := SmoothSite.multiplicativeGroupObject Sₖ
    let p := (SmoothSite.Contraction.projection G).app U.unop
    exact (f.hom.naturality p.op).symm

/-- The original projection splits evaluation at the original unit section. -/
theorem torusParameterSheafConstant_unit :
    torusParameterSheafConstant k ≫ torusParameterSheafUnit k =
      𝟙 (𝟭 (Sheaf Jₖ AddCommGrpCat.{u + 1})) := by
  apply NatTrans.ext
  funext P
  apply ObjectProperty.hom_ext
  change SmoothSite.Contraction.constant P.obj (SmoothSite.multiplicativeGroupObject Sₖ) ≫
      SmoothSite.Contraction.unit P.obj = 𝟙 P.obj
  exact SmoothSite.Contraction.constant_unit P.obj

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))
  AddCommGrpCat.{u + 1}]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- The signed coefficient map factors through the actual unit-section kernel. -/
def motivicSheafParameterProductToUnitKernel (q : ℕ) :
    motivicSheafComplex k q ⟶ kernel ((torusParameterSheafComplexUnit k (.up ℤ)).app
      ((motivicSheafComplex k (q + 1))⟦(1 : ℤ)⟧)) :=
  kernel.lift _ (motivicSheafParameterProduct k q) (motivicSheafParameterProduct_unit k q)

/-- The kernel factorization recovers the original weight-raising map. -/
@[reassoc]
theorem motivicSheafParameterProductToUnitKernel_ι (q : ℕ) :
    motivicSheafParameterProductToUnitKernel k q ≫
      kernel.ι ((torusParameterSheafComplexUnit k (.up ℤ)).app
        ((motivicSheafComplex k (q + 1))⟦(1 : ℤ)⟧)) =
      motivicSheafParameterProduct k q :=
  kernel.lift_ι _ _ _

end AlgebraicGeometry.PresheafWithTransfers
