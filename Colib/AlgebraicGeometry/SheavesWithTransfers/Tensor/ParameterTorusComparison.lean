/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Tensor.ParameterAdjunction
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Comparison with the original torus tensor

The graph-compatible sheafified coend specializes to the original torus
tensor. The comparison is the unique adjunction comparison for the original
torus-sections right adjoint, so it preserves its original unit and counit.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))

local instance parameterTorusCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The general coend adjunction, using exactly the original torus-sections functor. -/
def torusCoendSheafAdjunction :
    (forget k ⋙ coendPushforward (Cor.parameterProduct Gₘ) ⋙ nisnevichSheafify k) ⊣
      (torusSectionsFunctor k : SheafWithTransfers.{u + 1} k ⥤ _) :=
  (parameterSheafPushforwardAdjunction (Cor.parameterProductGraphIso Gₘ)).ofNatIsoRight
    (parameterSectionsOfGraphIsoIntegral Gₘ ≪≫ parameterSectionsFunctorTorusIso k)

/-- The general ordinary coend construction recovers the original torus tensor. -/
def torusCoendSheafIso :
    (forget k ⋙ coendPushforward (Cor.parameterProduct Gₘ) ⋙ nisnevichSheafify k) ≅
      torusTensorFunctor k :=
  (torusCoendSheafAdjunction k).leftAdjointUniq (torusTensorAdjunction k)

/-- The comparison carries the coend unit to the original torus tensor unit. -/
@[reassoc]
theorem torusCoendSheafIso_unit (P : SheafWithTransfers.{u + 1} k) :
    (torusCoendSheafAdjunction k).unit.app P ≫
      (torusSectionsFunctor k).map ((torusCoendSheafIso k).hom.app P) =
        (torusTensorAdjunction k).unit.app P :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ P

/-- The comparison preserves the original torus tensor counit. -/
@[reassoc]
theorem torusCoendSheafIso_counit (P : SheafWithTransfers.{u + 1} k) :
    (torusCoendSheafIso k).hom.app ((torusSectionsFunctor k).obj P) ≫
      (torusTensorAdjunction k).counit.app P =
        (torusCoendSheafAdjunction k).counit.app P :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ P

end AlgebraicGeometry.SheafWithTransfers
