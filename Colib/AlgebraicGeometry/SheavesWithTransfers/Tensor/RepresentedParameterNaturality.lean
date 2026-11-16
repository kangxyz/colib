/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Tensor.RepresentedParameter
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Natural represented-parameter and torus tensor comparisons

Whisker the original sheafification counit and the existing strong tensorator.
This packages the represented-parameter comparisons as natural functor
isomorphisms. Transport of the original torus adjunction then records its
unit and counit without choosing another adjunction independently.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

local instance representedNaturalityCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance : MonoidalCategory (TransferCoefficients k) := convolutionMonoidalCategory
local instance : SymmetricCategory (TransferCoefficients k) := convolutionSymmetricCategory
local instance : MonoidalCategory (SheafWithTransfers.{u + 1} k) :=
  nisnevichConvolutionMonoidalCategory k

/-- Naturality of the already constructed strong tensorator in the first input. -/
def nisnevichSheafificationTensorRightIso (Q : TransferCoefficients k) :
    nisnevichSheafify k ⋙ tensorRight ((nisnevichSheafify k).obj Q) ≅
      tensorRight Q ⋙ nisnevichSheafify k :=
  NatIso.ofComponents (fun P => (nisnevichConvolutionSheafificationCoreMonoidal k).μIso P Q)
    (fun f => (nisnevichConvolutionSheafificationCoreMonoidal k).μIso_hom_natural_left f Q)

/-- Tensor with a sheafified coefficient, natural in the original sheaf input. -/
def nisnevichConvolutionSheafifiedRightNatIso (Q : TransferCoefficients k) :
    tensorRight ((nisnevichSheafify k).obj Q) ≅
      forget k ⋙ tensorRight Q ⋙ nisnevichSheafify k :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (nisnevichSheafificationAdjunction k).counit).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (forget k) (nisnevichSheafificationTensorRightIso k Q)

/-- The represented smooth parameter comparison respects all coefficient maps. -/
@[colib_tag "COL-1295"]
def nisnevichConvolutionRepresentedParameterNatIso (X : Cor k) :
    tensorRight ((transferRepresentable k).obj X) ≅
      forget k ⋙ coendPushforward (tensorRight X) ⋙ nisnevichSheafify k :=
  nisnevichConvolutionSheafifiedRightNatIso k ((representableLarge k).obj X) ≪≫
    Functor.isoWhiskerLeft (forget k)
      (Functor.isoWhiskerRight (convolutionParameterNatIso (curriedTensor (Cor k)) X)
        (nisnevichSheafify k))

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))

/-- The actual descended torus tensor is naturally the original torus tensor. -/
@[colib_tag "COL-1295"]
def nisnevichConvolutionTorusNatIso :
    tensorRight ((transferRepresentable k).obj (Cor.mk Gₘ)) ≅ torusTensorFunctor k :=
  nisnevichConvolutionRepresentedParameterNatIso k (Cor.mk Gₘ) ≪≫
    Functor.isoWhiskerLeft (forget k)
      (Functor.isoWhiskerRight
        (coendPushforwardNatIso (tensorRight (Cor.mk Gₘ))
          (Cor.tensorRightIsoParameterProduct Gₘ)) (nisnevichSheafify k)) ≪≫
    torusCoendSheafIso k

/-- Use the original torus adjunction along the explicit natural tensor comparison. -/
@[colib_tag "COL-1295"]
def nisnevichConvolutionTorusAdjunction :
    tensorRight ((transferRepresentable k).obj (Cor.mk Gₘ)) ⊣
      (torusSectionsFunctor k : SheafWithTransfers.{u + 1} k ⥤ _) :=
  (torusTensorAdjunction k).ofNatIsoLeft (nisnevichConvolutionTorusNatIso k).symm

/-- The natural tensor comparison carries the transported unit to the original unit. -/
@[reassoc]
@[colib_tag "COL-1295"]
theorem nisnevichConvolutionTorusNatIso_unit (P : SheafWithTransfers.{u + 1} k) :
    (nisnevichConvolutionTorusAdjunction k).unit.app P ≫
      (torusSectionsFunctor k).map ((nisnevichConvolutionTorusNatIso k).hom.app P) =
        (torusTensorAdjunction k).unit.app P := by
  simp [nisnevichConvolutionTorusAdjunction, Adjunction.ofNatIsoLeft, ← Functor.map_comp]

/-- The natural tensor comparison preserves the original torus counit. -/
@[reassoc]
@[colib_tag "COL-1295"]
theorem nisnevichConvolutionTorusNatIso_counit (P : SheafWithTransfers.{u + 1} k) :
    (nisnevichConvolutionTorusNatIso k).hom.app ((torusSectionsFunctor k).obj P) ≫
      (torusTensorAdjunction k).counit.app P =
        (nisnevichConvolutionTorusAdjunction k).counit.app P := rfl

end AlgebraicGeometry.SheafWithTransfers
