/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.Tensor.RepresentedParameterNaturality
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! Client checks for the generic integral coend, PST specialization and NST descent.
All field-dependent interfaces below deliberately assume only `Field`.
-/

open CategoryTheory MonoidalCategory

universe u

noncomputable section

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

-- The PST construction uses the generic integral Hom-group coend literally.
example (F : Cor k ⥤ Cor k ⥤ Cor k) (P Q : TransferCoefficients k) (X : Cor k) :
    convolutionSections F P Q X =
      CategoryTheory.Preadditive.Convolution.sections.{u + 1, u, 0} F P.obj Q.obj X := rfl

end AlgebraicGeometry.PresheafWithTransfers

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local instance : HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance : MonoidalCategory (TransferCoefficients k) := convolutionMonoidalCategory
local instance : SymmetricCategory (TransferCoefficients k) := convolutionSymmetricCategory
local instance : MonoidalCategory (SheafWithTransfers.{u + 1} k) :=
  nisnevichConvolutionMonoidalCategory k

example : SymmetricCategory (SheafWithTransfers.{u + 1} k) :=
  nisnevichConvolutionSymmetricCategory k

example : (nisnevichSheafify k).CoreMonoidal :=
  nisnevichConvolutionSheafificationCoreMonoidal k

example (X : Cor k) :
    tensorRight ((transferRepresentable k).obj X) ≅
      forget k ⋙ coendPushforward (tensorRight X) ⋙ nisnevichSheafify k :=
  nisnevichConvolutionRepresentedParameterNatIso k X

-- The general tensor retains the original torus adjunction, not just its objects.
example (P : SheafWithTransfers.{u + 1} k) :
    (nisnevichConvolutionTorusAdjunction k).unit.app P ≫
      (torusSectionsFunctor k).map ((nisnevichConvolutionTorusNatIso k).hom.app P) =
        (torusTensorAdjunction k).unit.app P :=
  nisnevichConvolutionTorusNatIso_unit k P

example (P : SheafWithTransfers.{u + 1} k) :
    (nisnevichConvolutionTorusNatIso k).hom.app ((torusSectionsFunctor k).obj P) ≫
      (torusTensorAdjunction k).counit.app P =
        (nisnevichConvolutionTorusAdjunction k).counit.app P :=
  nisnevichConvolutionTorusNatIso_counit k P

end AlgebraicGeometry.SheafWithTransfers
