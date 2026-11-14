/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.DerivedCategory.AcyclicCechTriangle
public import Colib.AlgebraicGeometry.Scheme.Modules.TwoOpenCech
public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic

/-!
# The relative derived Čech triangle of two opens

For a quasi-coherent module and a two-open affine cover over an affine base,
the signed Čech differential represents the two acyclic terms of the
derived direct image, with the original connecting morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace AlgebraicGeometry.Scheme.Modules

local instance (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : X.Opens)
  (M : X.Modules) [M.IsQuasicoherent]

private theorem acyclic_restrictPush (W : X.Opens) [IsAffineHom W.ι]
    [IsAffineHom (W.ι ≫ f)] :
    (pushforward f).rightAcyclic ((restrictPushMod W).obj M) := by
  let N : W.toScheme.Modules := M.restrict W.ι
  let : N.IsQuasicoherent := isQuasicoherent_restrictFunctor W.ι M
  exact Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_comp W.ι f N

variable [IsAffineHom U.ι] [IsAffineHom V.ι] [IsAffineHom (U ⊓ V).ι]
  [IsAffineHom (U.ι ≫ f)] [IsAffineHom (V.ι ≫ f)] [IsAffineHom ((U ⊓ V).ι ≫ f)]

omit [IsAffineHom (U ⊓ V).ι] [IsAffineHom ((U ⊓ V).ι ≫ f)] in
/-- The two chart terms are acyclic for the relative pushforward. -/
theorem acyclic_twoOpenCech_middle :
    (pushforward f).rightAcyclic (twoOpenCech U V M).X₂ :=
  Stacks.RightAcyclicProduct.rightAcyclic_biprod _
    (acyclic_restrictPush f M U) (acyclic_restrictPush f M V)

omit [IsAffineHom U.ι] [IsAffineHom V.ι] [IsAffineHom (U.ι ≫ f)] [IsAffineHom (V.ι ≫ f)] in
/-- The overlap term is acyclic for the relative pushforward. -/
theorem acyclic_twoOpenCech_overlap :
    (pushforward f).rightAcyclic (twoOpenCech U V M).X₃ :=
  acyclic_restrictPush f M (U ⊓ V)

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
attribute [local instance] Functor.isTriangulated_rightDerivedFunctorPlus

variable (hUV : U ⊔ V = ⊤)

/-- The relative Čech triangle with the literal signed differential on chart images. -/
def twoOpenDerivedCechTriangle : Triangle (DerivedCategory.Plus Y.Modules) :=
  (pushforward f).rightDerivedAcyclicTriangle (twoOpenCech_shortExact U V M hUV)
    (acyclic_twoOpenCech_middle f U V M) (acyclic_twoOpenCech_overlap f U V M)

/-- Comparison with the canonical derived triangle of the actual signed short complex. -/
def twoOpenDerivedCechTriangleIso :
    twoOpenDerivedCechTriangle f U V M hUV ≅
      (pushforward f).rightDerivedSingleTriangle (twoOpenCech_shortExact U V M hUV) :=
  (pushforward f).rightDerivedAcyclicTriangleIso (twoOpenCech_shortExact U V M hUV)
    (acyclic_twoOpenCech_middle f U V M) (acyclic_twoOpenCech_overlap f U V M)

set_option linter.unusedSectionVars false in
/-- The relative Čech differential is the original signed direct-image differential. -/
theorem twoOpenDerivedCechTriangle_mor₂ :
    (twoOpenDerivedCechTriangle f U V M hUV).mor₂ =
      (DerivedCategory.Plus.singleFunctor Y.Modules 0).map
        ((pushforward f).map (twoOpenCech U V M).g) := rfl

/-- The relative Čech triangle is distinguished. -/
theorem twoOpenDerivedCechTriangle_distinguished :
    twoOpenDerivedCechTriangle f U V M hUV ∈ distTriang (DerivedCategory.Plus Y.Modules) :=
  (pushforward f).rightDerivedAcyclicTriangle_distinguished (twoOpenCech_shortExact U V M hUV)
    (acyclic_twoOpenCech_middle f U V M) (acyclic_twoOpenCech_overlap f U V M)

end AlgebraicGeometry.Scheme.Modules
