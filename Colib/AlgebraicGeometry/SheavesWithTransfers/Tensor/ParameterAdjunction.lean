/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Tensor.ParameterLocalEquivalences
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# The ordinary sheaf adjunction for a graph-compatible parameter

Restrict the existing coend pushforward adjunction to the original Nisnevich
sheaves with transfers. The right adjoint retains the actual parameter
sections and restrictions. No geometric integrality or perfectness is needed.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable {k : Type u} [Field k]
  {T : SmoothSite (Spec (.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

local instance parameterAdjunctionCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The original sheafified coend pushforward is left adjoint to actual
parameter sections on Nisnevich sheaves with transfers. -/
def parameterSheafPushforwardAdjunction :
    (forget k ⋙ coendPushforward F ⋙ nisnevichSheafify k) ⊣
      parameterSectionsOfGraphIso e := by
  let adj := (coendPushforwardAdjunction F).comp (nisnevichSheafificationAdjunction k)
  exact adj.restrictFullyFaithful
    (PresheafWithTransfers.IsNisnevichSheaf.{u + 1} k).fullyFaithfulι
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ parameterSectionsUnderlyingIso e)

/-- Sheafification commutes with the original graph-compatible coend
pushforward, using the same parameter-sections right adjoint. -/
def parameterSheafPushforwardSheafificationIso :
    nisnevichSheafify k ⋙ (forget k ⋙ coendPushforward F ⋙ nisnevichSheafify k) ≅
      coendPushforward F ⋙ nisnevichSheafify k :=
  ((nisnevichSheafificationAdjunction k).comp
    (parameterSheafPushforwardAdjunction e)).leftAdjointUniq
      (parameterPushforwardSheafificationAdjunction e)

end AlgebraicGeometry.SheafWithTransfers
