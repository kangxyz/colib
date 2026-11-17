/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Tensor.MonoidalLocalization
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Tensor.ParameterTorusComparison
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.NativeParameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.PushforwardExactness
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Represented parameters for the actual Nisnevich convolution tensor

The strong tensorator and original sheafification counit identify tensoring
with a represented smooth parameter with its actual sheafified coend.
The torus specialization is the original torus tensor, not a second model.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local instance representedParameterCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- A represented smooth right factor gives the original sheafified parameter coend. -/
def nisnevichConvolutionRepresentedParameterIso
    (P : SheafWithTransfers.{u + 1} k) (X : Cor k) :
    letI := nisnevichConvolutionMonoidalCategory k
    P ⊗ (transferRepresentable k).obj X ≅ (nisnevichSheafify k).obj
      ((coendPushforward (tensorRight X)).obj ((forget k).obj P)) := by
  letI := nisnevichConvolutionMonoidalCategory k
  exact nisnevichConvolutionSheafifiedRightIso k P ((representableLarge k).obj X) ≪≫
    (nisnevichSheafify k).mapIso
      ((convolutionParameterNatIso (curriedTensor (Cor k)) X).app ((forget k).obj P))

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))

/-- The descended tensor with the represented torus is the original torus tensor. -/
def nisnevichConvolutionTorusIso (P : SheafWithTransfers.{u + 1} k) :
    letI := nisnevichConvolutionMonoidalCategory k
    P ⊗ (transferRepresentable k).obj (Cor.mk Gₘ) ≅ (torusTensorFunctor k).obj P := by
  letI := nisnevichConvolutionMonoidalCategory k
  exact nisnevichConvolutionRepresentedParameterIso k P (Cor.mk Gₘ) ≪≫
    (nisnevichSheafify k).mapIso
      ((coendPushforwardNatIso (tensorRight (Cor.mk Gₘ))
        (Cor.tensorRightIsoParameterProduct Gₘ)).app ((forget k).obj P)) ≪≫
    (torusCoendSheafIso k).app P

end AlgebraicGeometry.SheafWithTransfers
