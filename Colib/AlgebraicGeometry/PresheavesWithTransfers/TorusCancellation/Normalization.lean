/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation

/-!
# Signed representatives of the torus cancellation comparison

The actual projection from the torus to the base splits the unit-section
quotient. The section of the quotient takes the exterior comparison to
the difference of the original exterior product and its constant part.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "Bₖ" => SmoothSite.base Sₖ

/-- The torus projection in the same coordinates as the unit correspondence. -/
abbrev torusProjectionCorrespondence (X : Cor k) :
    (Cor.parameterProduct Gₘ).obj X ⟶ (Cor.parameterProduct Bₖ).obj X :=
  (Cor.parameterProductMap (toBase Gₘ)).app X

@[reassoc]
theorem torusUnitCorrespondence_projection (X : Cor k) :
    torusUnitCorrespondence k X ≫ torusProjectionCorrespondence k X = 𝟙 _ := by
  change (Cor.graphFunctor k).map
      (SmoothSite.productMap (𝟙 X.toSmoothSite) (SmoothSite.torusOne Sₖ)) ≫
    (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) (toBase Gₘ)) = 𝟙 _
  have h : SmoothSite.torusOne Sₖ ≫ toBase Gₘ = 𝟙 Bₖ := by
    rw [comp_toBase]
    rfl
  rw [← Functor.map_comp, ← SmoothSite.productMap_comp, Category.id_comp, h,
    SmoothSite.productMap_id]
  exact (Cor.graphFunctor k).map_id _

/-- The constant unit correspondence on the torus product. -/
def torusUnitProjector (X : Cor k) :
    (Cor.parameterProduct Gₘ).obj X ⟶ (Cor.parameterProduct Gₘ).obj X :=
  torusProjectionCorrespondence k X ≫ torusUnitCorrespondence k X

/-- The constant part is the graph of the original projection followed by the unit. -/
theorem torusUnitProjector_eq_graph (X : Cor k) :
    torusUnitProjector k X = (Cor.graphFunctor k).map
      (SmoothSite.productFst X.toSmoothSite Gₘ ≫ unitSection.app X.toSmoothSite) := by
  change (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) (toBase Gₘ)) ≫
    (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) (SmoothSite.torusOne Sₖ)) =
      (Cor.graphFunctor k).map
        (SmoothSite.productFst X.toSmoothSite Gₘ ≫ unitSection.app X.toSmoothSite)
  rw [← (Cor.graphFunctor k).map_comp]
  apply (Cor.graphFunctor k).congr_map
  rw [← productMap_toBase, ← baseProduct_unit]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

@[reassoc]
theorem torusUnitProjector_idempotent (X : Cor k) :
    torusUnitProjector k X ≫ torusUnitProjector k X = torusUnitProjector k X := by
  unfold torusUnitProjector
  rw [Category.assoc, torusUnitCorrespondence_projection_assoc]

@[reassoc]
theorem torusUnitProjector_naturality {X Y : Cor k} (α : X ⟶ Y) :
    (Cor.parameterProduct Gₘ).map α ≫ torusUnitProjector k Y =
      torusUnitProjector k X ≫ (Cor.parameterProduct Gₘ).map α := by
  unfold torusUnitProjector
  rw [← Category.assoc, (Cor.parameterProductMap (toBase Gₘ)).naturality α,
    Category.assoc, (Cor.parameterProductMap (SmoothSite.torusOne Sₖ)).naturality α,
    ← Category.assoc]

private theorem torusUnitRepresentable_retraction (Y : Cor k) :
    (representableLarge k).map (torusUnitCorrespondence k Y) ≫
      (representableLarge k).map (torusProjectionCorrespondence k Y) = 𝟙 _ := by
  rw [← Functor.map_comp, torusUnitCorrespondence_projection]
  exact (representableLarge k).map_id _

/-- The canonical representative of the split target quotient. -/
@[no_expose]
def torusCancellationCoefficientSection (Y : Cor k) :
    torusCancellationCoefficients k Y ⟶
      (representableLarge k).obj ((Cor.parameterProduct Gₘ).obj Y) :=
  (splitCokernelIsoKernel ((representableLarge k).map (torusUnitCorrespondence k Y))
    ((representableLarge k).map (torusProjectionCorrespondence k Y))
    (torusUnitRepresentable_retraction k Y)).hom ≫ kernel.ι _

@[reassoc]
theorem toTorusCancellationCoefficients_section (Y : Cor k) :
    toTorusCancellationCoefficients k Y ≫ torusCancellationCoefficientSection k Y =
      𝟙 _ - (representableLarge k).map (torusUnitProjector k Y) := by
  rw [torusCancellationCoefficientSection, torusUnitProjector, Functor.map_comp]
  exact splitCokernelIsoKernel_hom_ι _ _ (torusUnitRepresentable_retraction k Y)

@[reassoc]
theorem torusCancellationCoefficientSection_π (Y : Cor k) :
    torusCancellationCoefficientSection k Y ≫ toTorusCancellationCoefficients k Y = 𝟙 _ := by
  apply (cancel_epi (toTorusCancellationCoefficients k Y)).mp
  rw [← Category.assoc, toTorusCancellationCoefficients_section, Preadditive.sub_comp,
    Category.id_comp, Category.comp_id, torusUnitProjector, Functor.map_comp, Category.assoc,
    cokernel.condition, comp_zero, sub_zero]

theorem torusCancellationCoefficientSection_quotient_app_apply (Y U : Cor k)
    (z : U ⟶ (Cor.parameterProduct Gₘ).obj Y) :
    (torusCancellationCoefficientSection k Y).hom.app (op U)
      ((toTorusCancellationCoefficients k Y).hom.app (op U) (ULift.up z)) =
        ULift.up (z - z ≫ torusUnitProjector k Y) := by
  let R := representableLarge k
  let F := Cor.parameterProduct Gₘ
  let b : sections (R.obj (F.obj Y)) U := ULift.up z
  have h := congrArg
    (fun f : R.obj (F.obj Y) ⟶ R.obj (F.obj Y) ↦ f.hom.app (op U) b)
    (toTorusCancellationCoefficients_section k Y)
  change (torusCancellationCoefficientSection k Y).hom.app (op U)
      ((toTorusCancellationCoefficients k Y).hom.app (op U) b) =
    b - (R.map (torusUnitProjector k Y)).hom.app (op U) b at h
  change (torusCancellationCoefficientSection k Y).hom.app (op U)
      ((toTorusCancellationCoefficients k Y).hom.app (op U) b) = _
  rw [h]
  dsimp [b]
  rw [representableLarge_map_app_apply]
  rfl

/-- Include the source unit kernel and take the representative of the target quotient. -/
def torusCancellationLift (Y : Cor k) :
    torusCancellationTarget k Y ⟶
      torusSections ((representableLarge k).obj ((Cor.parameterProduct Gₘ).obj Y)) :=
  kernel.ι (torusUnit (torusCancellationCoefficients k Y)) ≫
    withParameterMap (torusCancellationCoefficientSection k Y) Gₘ

/-- Impose the target unit quotient and project to the source unit kernel. -/
def torusCancellationProjection (Y : Cor k) :
    torusSections ((representableLarge k).obj ((Cor.parameterProduct Gₘ).obj Y)) ⟶
      torusCancellationTarget k Y :=
  withParameterMap (toTorusCancellationCoefficients k Y) Gₘ ≫
    contractionKernelProjection (torusCancellationCoefficients k Y)

@[reassoc]
theorem torusCancellationLift_projection (Y : Cor k) :
    torusCancellationLift k Y ≫ torusCancellationProjection k Y = 𝟙 _ := by
  let P := torusCancellationCoefficients k Y
  have h : withParameterMap (torusCancellationCoefficientSection k Y) Gₘ ≫
      withParameterMap (toTorusCancellationCoefficients k Y) Gₘ = 𝟙 (torusSections P) := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    exact congrArg
      (fun f : P ⟶ P ↦ f.hom.app (op ((Cor.parameterProduct Gₘ).obj X.unop)))
      (torusCancellationCoefficientSection_π k Y)
  have hi : kernel.ι (torusUnit P) ≫ contractionKernelProjection P =
      𝟙 (kernel (torusUnit P)) := by
    apply (cancel_mono (kernel.ι (torusUnit P))).mp
    rw [Category.assoc, contractionKernelProjection_ι, Preadditive.comp_sub,
      Category.comp_id, Category.id_comp, ← Category.assoc, kernel.condition,
      zero_comp, sub_zero]
  unfold torusCancellationLift torusCancellationProjection
  change kernel.ι (torusUnit P) ≫
    (withParameterMap (torusCancellationCoefficientSection k Y) Gₘ ≫
      (withParameterMap (toTorusCancellationCoefficients k Y) Gₘ ≫
        contractionKernelProjection P)) = 𝟙 (contractionKernel P)
  rw [← Category.assoc (withParameterMap (torusCancellationCoefficientSection k Y) Gₘ),
    h, Category.id_comp, hi]
  rfl

/-- The signed representative of the comparison is exterior product
with the constant-unit part subtracted. -/
@[colib_tag "COL-1039"]
theorem torusCancellationLift_map_app_apply (Y X : Cor k) (α : X ⟶ Y) :
    (torusCancellationLift k Y).hom.app (op X)
      ((torusCancellationMap k Y).hom.app (op X) (ULift.up α)) =
        ULift.up ((Cor.parameterProduct Gₘ).map α -
          (Cor.parameterProduct Gₘ).map α ≫ torusUnitProjector k Y) := by
  let F := Cor.parameterProduct Gₘ
  let R := representableLarge k
  have hcomp : torusCancellationMap k Y ≫ torusCancellationLift k Y =
      torusCancellationParameterMap k Y ≫
        withParameterMap (torusCancellationCoefficientSection k Y) Gₘ := by
    unfold torusCancellationLift
    rw [torusCancellationMap_ι_assoc]
  have h := congrArg
    (fun f : R.obj Y ⟶ torusSections (R.obj (F.obj Y)) ↦
      f.hom.app (op X) (ULift.up α)) hcomp
  change (torusCancellationLift k Y).hom.app (op X)
    ((torusCancellationMap k Y).hom.app (op X) (ULift.up α)) =
      (torusCancellationCoefficientSection k Y).hom.app (op (F.obj X))
        ((torusCancellationParameterMap k Y).hom.app (op X) (ULift.up α)) at h
  rw [h, torusCancellationParameterMap_app_apply]
  exact torusCancellationCoefficientSection_quotient_app_apply k Y (F.obj X) (F.map α)

/-- The representative of the actual projection of a signed correspondence
removes the two constant-unit parts. -/
theorem torusCancellationProjection_lift_app_apply (Y X : Cor k)
    (z : (Cor.parameterProduct Gₘ).obj X ⟶ (Cor.parameterProduct Gₘ).obj Y) :
    (torusCancellationLift k Y).hom.app (op X)
      ((torusCancellationProjection k Y).hom.app (op X) (ULift.up z)) =
        ULift.up
          ((𝟙 _ - torusUnitProjector k X) ≫ z ≫ (𝟙 _ - torusUnitProjector k Y)) := by
  let F := Cor.parameterProduct Gₘ
  let Q := torusCancellationCoefficients k Y
  let q := toTorusCancellationCoefficients k Y
  let d := contractionKernelProjection Q
  let j := kernel.ι (torusUnit Q)
  let a : sections Q (F.obj X) := q.hom.app (op (F.obj X)) (ULift.up z)
  have hs := congrArg
    (fun f : torusSections Q ⟶ torusSections Q ↦ f.hom.app (op X) a)
    (contractionKernelProjection_ι Q)
  change j.hom.app (op X) (d.hom.app (op X) a) =
    a - transfer Q (torusProjectionCorrespondence k X)
      (transfer Q (torusUnitCorrespondence k X) a) at hs
  rw [← ConcreteCategory.comp_apply, ← transfer_comp] at hs
  have ht := ConcreteCategory.congr_hom
    (transfer_naturality q (torusUnitProjector k X)) (ULift.up z)
  change q.hom.app (op (F.obj X))
      (transfer ((representableLarge k).obj (F.obj Y)) (torusUnitProjector k X)
        (ULift.up z)) = transfer Q (torusUnitProjector k X) a at ht
  change j.hom.app (op X) (d.hom.app (op X) a) =
    a - transfer Q (torusUnitProjector k X) a at hs
  rw [← ht, representableLarge_transfer_apply] at hs
  have hq : j.hom.app (op X) (d.hom.app (op X) a) =
      q.hom.app (op (F.obj X)) (ULift.up (z - torusUnitProjector k X ≫ z)) := by
    let R := representableLarge k
    let b : sections (R.obj (F.obj Y)) (F.obj X) := ULift.up z
    let c : sections (R.obj (F.obj Y)) (F.obj X) :=
      ULift.up (torusUnitProjector k X ≫ z)
    rw [hs]
    change q.hom.app (op (F.obj X)) b - q.hom.app (op (F.obj X)) c =
      q.hom.app (op (F.obj X)) (b - c)
    exact (map_sub (q.hom.app (op (F.obj X))).hom b c).symm
  change (torusCancellationCoefficientSection k Y).hom.app (op (F.obj X))
    (j.hom.app (op X) (d.hom.app (op X) a)) = _
  rw [hq, torusCancellationCoefficientSection_quotient_app_apply]
  have hleft : (𝟙 (F.obj X) - torusUnitProjector k X) ≫ z =
      z - torusUnitProjector k X ≫ z := by
    rw [Preadditive.sub_comp, Category.id_comp]
  rw [← Category.assoc, hleft, Preadditive.comp_sub, Category.comp_id]

theorem torusCancellationLift_projection_app_apply (Y X : Cor k)
    (a : sections (torusCancellationTarget k Y) X) :
    (torusCancellationProjection k Y).hom.app (op X)
      ((torusCancellationLift k Y).hom.app (op X) a) = a :=
  congrArg (fun f : torusCancellationTarget k Y ⟶ torusCancellationTarget k Y ↦
    f.hom.app (op X) a) (torusCancellationLift_projection k Y)

theorem torusCancellationLift_app_injective (Y X : Cor k) :
    Function.Injective ((torusCancellationLift k Y).hom.app (op X)) :=
  Function.LeftInverse.injective (torusCancellationLift_projection_app_apply k Y X)

/-- The signed representatives are exactly the correspondences fixed by
the two complementary unit projectors. -/
theorem exists_torusCancellationLift_app_eq_iff (Y X : Cor k)
    (z : (Cor.parameterProduct Gₘ).obj X ⟶ (Cor.parameterProduct Gₘ).obj Y) :
    (∃ a : sections (torusCancellationTarget k Y) X,
      (torusCancellationLift k Y).hom.app (op X) a = ULift.up z) ↔
        z = (𝟙 _ - torusUnitProjector k X) ≫ z ≫ (𝟙 _ - torusUnitProjector k Y) := by
  constructor
  · rintro ⟨a, ha⟩
    have h := torusCancellationProjection_lift_app_apply k Y X z
    rw [← ha, torusCancellationLift_projection_app_apply, ha] at h
    exact ULift.up.inj h
  · intro h
    refine ⟨(torusCancellationProjection k Y).hom.app (op X) (ULift.up z), ?_⟩
    exact (torusCancellationProjection_lift_app_apply k Y X z).trans (congrArg ULift.up h.symm)

end AlgebraicGeometry.PresheafWithTransfers
