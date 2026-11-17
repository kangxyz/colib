/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Tensor.ParameterLocalEquivalences
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentablePresentation
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionCoproducts
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionMonoidal
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionParameter
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Native

import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Convolution preserves Nisnevich local equivalences

For a represented right coefficient, the actual parameter-sections adjunction
proves stability. Colimit preservation and the canonical two-step presentation
extend it to every transfer presheaf. The native correspondence monoidal
structure is available over an arbitrary field. No flatness, geometric integrality
or homotopy-invariance assumption on the coefficients is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Fix the coefficient universe using the existing sheafification theorem. -/
local instance convolutionCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local notation "F" => curriedTensor (Cor k)
local notation "PST" => TransferCoefficients k

/-- Convolution with an actual representable preserves Nisnevich local equivalences. -/
theorem isIso_sheafify_convolution_map_representable
    {P P' : PST} (f : P ⟶ P') [IsIso ((nisnevichSheafify.{u} k).map f)] (X : Cor k) :
    IsIso ((nisnevichSheafify.{u} k).map
      (((convolutionBifunctor F).map f).app ((representableLarge k).obj X))) := by
  let e := Functor.isoWhiskerRight (convolutionParameterNatIso F X) (nisnevichSheafify.{u} k)
  apply (NatIso.isIso_map_iff e f).2
  exact isIso_sheafify_parameterPushforward_map
    (Cor.graphFunctorCompTensorRightIso X.toSmoothSite) f

/-- Convolution in the first input preserves Nisnevich local equivalences for
an arbitrary second coefficient, via its actual representable presentation. -/
theorem isIso_sheafify_convolution_map_left
    {P P' : PST} (f : P ⟶ P') [IsIso ((nisnevichSheafify.{u} k).map f)] (Q : PST) :
    IsIso ((nisnevichSheafify.{u} k).map (((convolutionBifunctor F).map f).app Q)) := by
  let : HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfSize.{u + 1, u + 1, u + 1}
  let : PreservesColimitsOfSize.{u + 1, u + 1} ((convolutionBifunctor F).obj P) := by
    constructor
    intro J hJ
    let : Category.{u + 1} J := hJ
    exact convolution_preservesColimitsOfShape_right F P J
  let : PreservesColimitsOfSize.{u + 1, u + 1} ((convolutionBifunctor F).obj P') := by
    constructor
    intro J hJ
    let : Category.{u + 1} J := hJ
    exact convolution_preservesColimitsOfShape_right F P' J
  let α := Functor.whiskerRight ((convolutionBifunctor F).map f) (nisnevichSheafify.{u} k)
  exact isIso_app_of_isIso_representable α
    (fun X => isIso_sheafify_convolution_map_representable f X) Q

/-- Convolution in the second input preserves Nisnevich local equivalences,
using the actual convolution symmetry rather than a second presentation proof. -/
theorem isIso_sheafify_convolution_map_right
    (P : PST) {Q Q' : PST} (f : Q ⟶ Q') [IsIso ((nisnevichSheafify.{u} k).map f)] :
    IsIso ((nisnevichSheafify.{u} k).map (((convolutionBifunctor F).obj P).map f)) := by
  let e := Functor.isoWhiskerRight
    ((convolutionSwap F (BraidedCategory.curriedBraidingNatIso (Cor k))
      curriedCorrespondenceBraiding_involutive).app P) (nisnevichSheafify.{u} k)
  exact (NatIso.isIso_map_iff e f).2 (isIso_sheafify_convolution_map_left f P)

end AlgebraicGeometry.SheafWithTransfers
