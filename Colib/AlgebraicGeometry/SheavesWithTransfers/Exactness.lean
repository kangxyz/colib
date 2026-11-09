/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Limits
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Sheafification
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
Implementation adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Sheaf/Exactness.lean`, blob `08c4251df0a4eb6500cf9c973d51dd9456d64dcc`.

# Abelian Nisnevich sheaves with transfers

The actual category of additive presheaves on finite correspondences is abelian.
Transfer-preserving Nisnevich sheafification is a left exact reflection, so its
category of sheaves is abelian as well. The ordinary underlying sheaf functor
preserves limits. Colimits of transfer sheaves require sheafification; no claim
that their values are computed objectwise is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w w'

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

namespace PresheafWithTransfers

section Colimits

variable (J : Type w) [Category.{w'} J] [HasColimitsOfShape J AddCommGrpCat.{v}]

/-- Graph restriction preserves colimits of actual additive transfer presheaves. -/
instance : PreservesColimitsOfShape J (toPresheaf.{v} k) := by
  dsimp [toPresheaf, restrictAlong]
  infer_instance

end Colimits

variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- Actual transfer sheafification preserves finite limits. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Sheaf/Exactness.lean:53-62"
  "adaptation" "Native additive functors and the actual transfer sheafification reflection"]
instance nisnevichSheafify_preservesFiniteLimits : PreservesFiniteLimits (nisnevichSheafify k) := by
  let U : SheafWithTransfers.{u + 1} k ⥤ (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    SheafWithTransfers.forget k ⋙ PresheafWithTransfers.forget
  have : PreservesFiniteLimits (nisnevichSheafify k ⋙ U) := by
    change PreservesFiniteLimits
      (PresheafWithTransfers.forget ⋙
        presheafToSheaf (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} ⋙
        sheafToPresheaf (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (nisnevichSheafify k) U

end PresheafWithTransfers

namespace SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

section Limits

variable (J : Type w) [Category.{w'} J] [HasLimitsOfShape J AddCommGrpCat.{v}]

/-- Forgetting transfers preserves limits in the actual ordinary sheaf category. -/
instance toSheaf_preservesLimitsOfShape : PreservesLimitsOfShape J (toSheaf.{v} k) := by
  have : PreservesLimitsOfShape J
      (toSheaf.{v} k ⋙ sheafToPresheaf
        (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{v}) :=
    preservesLimitsOfShape_of_natIso (toSheafCompSheafToPresheafIso k).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves (toSheaf k)
    (sheafToPresheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat)

end Limits

instance toSheaf_preservesFiniteLimits : PreservesFiniteLimits (toSheaf.{v} k) :=
  ⟨fun _ _ _ => inferInstance⟩

variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- Genuine Nisnevich sheaves with transfers form an abelian category. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Sheaf/Exactness.lean:93-103"
  "adaptation" "Native additive functors and the actual transfer sheafification reflection"]
instance abelian : Abelian (SheafWithTransfers.{u + 1} k) := by
  let : HasFiniteProducts (SheafWithTransfers.{u + 1} k) := ⟨fun n => by
    let : HasLimitsOfShape (Discrete (Fin n)) (PresheafWithTransfers.{u + 1} k) :=
      hasLimitsOfShape_of_closedUnderLimits (Discrete (Fin n))
        (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})
    exact hasLimitsOfShape_of_closedUnderLimits (Discrete (Fin n))
      (PresheafWithTransfers.IsNisnevichSheaf.{u + 1} k)⟩
  let adj : PresheafWithTransfers.nisnevichSheafify k ⊣ forget.{u + 1} k :=
    PresheafWithTransfers.nisnevichSheafificationAdjunction k
  exact abelianOfAdjunction (forget k) (PresheafWithTransfers.nisnevichSheafify k)
    (asIso adj.counit) adj

end SheafWithTransfers

attribute [colib_tag "COL-0381"]
  SheafWithTransfers.abelian

end AlgebraicGeometry
