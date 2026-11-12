/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Representable
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsFunctor
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Torus tensor and torus sections on Nisnevich sheaves

The left adjoint applies the original parameter tensor to the underlying
transfer presheaf and sheafifies. Restrict the presheaf adjunction along the
fully faithful inclusion using the actual sheaf of torus sections.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))

/-- The literal reindexing after forgetting the sheaf condition. -/
def torusSectionsUnderlyingIso :
    forget k ⋙ (withParameterFunctor Gₘ :
      PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k) ≅
      torusSectionsFunctor k ⋙ forget k :=
  Iso.refl _

/-- Tensor with the original torus and then apply Nisnevich sheafification. -/
def torusTensorFunctor : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k :=
  forget k ⋙ parameterTensorFunctor Gₘ ⋙ nisnevichSheafify k

/-- The actual torus tensor is left adjoint to the original torus sections. -/
def torusTensorAdjunction :
    torusTensorFunctor k ⊣ (torusSectionsFunctor k :
      SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k) := by
  let adj := (parameterTensorAdjunction Gₘ).comp (nisnevichSheafificationAdjunction k)
  exact adj.restrictFullyFaithful
    (PresheafWithTransfers.IsNisnevichSheaf.{u + 1} k).fullyFaithfulι
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor (torusTensorFunctor k)).symm
    (Functor.leftUnitor _ ≪≫ torusSectionsUnderlyingIso k)

/-- The two original tensor functors commute with Nisnevich sheafification. -/
def torusTensorSheafificationIso :
    nisnevichSheafify k ⋙ torusTensorFunctor k ≅
      parameterTensorFunctor Gₘ ⋙ nisnevichSheafify k :=
  ((nisnevichSheafificationAdjunction k).comp (torusTensorAdjunction k)).leftAdjointUniq
    (((parameterTensorAdjunction Gₘ).comp (nisnevichSheafificationAdjunction k)).ofNatIsoRight
      (torusSectionsUnderlyingIso k))

/-- The tensor of the sheafified representable is represented by the actual torus product. -/
def torusTensorRepresentableIso (X : Cor k) :
    (torusTensorFunctor k).obj ((nisnevichSheafify k).obj ((representableLarge k).obj X)) ≅
      (nisnevichSheafify k).obj ((representableLarge k).obj ((Cor.parameterProduct Gₘ).obj X)) :=
  (torusTensorSheafificationIso k).app ((representableLarge k).obj X) ≪≫
    (nisnevichSheafify k).mapIso (parameterTensorRepresentableIso Gₘ X)

end AlgebraicGeometry.SheafWithTransfers
