/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Contraction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.CategoryTheory.Preadditive.SplitCokernelKernel

/-!
# The genuine unit kernel of homotopy-invariant transfer coefficients

The constant and unit maps are natural for all signed correspondences. For HI
coefficients the exact Laurent cokernel is the unit kernel. The forward map
subtracts the actual constant component; the inverse is inclusion then quotient.
Adapted from `Motivic/Transfers/Presheaf/ContractionHI.lean:34-161`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction

variable {k : Type u} [Field k]

instance base_geometricallyIntegral :
    GeometricallyIntegral (SmoothSite.base (Spec (.of k))).hom := by
  change GeometricallyIntegral (𝟙 (Spec (.of k)))
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  exact IsIntegral.of_isIso (inv (pullback.snd (𝟙 (Spec (.of k))) y))

/-- Base-product coefficients before applying the actual first-projection comparison. -/
abbrev baseSections (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  withParameter P (SmoothSite.base (Spec (.of k)))

/-- The genuine constant Laurent component, with base-product coordinates. -/
def torusConstant (P : PresheafWithTransfers.{v} k) : baseSections P ⟶ torusSections P :=
  parameterPullback P (toBase (SmoothSite.multiplicativeGroupObject (Spec (.of k))))

/-- Restriction along the original positive unit, retaining all transfer naturality. -/
def torusUnit (P : PresheafWithTransfers.{v} k) : torusSections P ⟶ baseSections P :=
  parameterPullback P (SmoothSite.torusOne (Spec (.of k)))

/-- The genuine affine projection in base-product coordinates. -/
def affineLineConstant (P : PresheafWithTransfers.{v} k) :
    baseSections P ⟶ affineLineSections P :=
  parameterPullback P (toBase (SmoothSite.additiveGroupObject (Spec (.of k))))

@[reassoc (attr := simp)]
theorem torusConstant_unit (P : PresheafWithTransfers.{v} k) :
    torusConstant P ≫ torusUnit P = 𝟙 (baseSections P) := by
  rw [torusConstant, torusUnit, ← parameterPullback_comp]
  have h : SmoothSite.torusOne (Spec (.of k)) ≫
      toBase (SmoothSite.multiplicativeGroupObject (Spec (.of k))) =
      𝟙 (SmoothSite.base (Spec (.of k))) := by
    rw [comp_toBase]
    rfl
  rw [h, parameterPullback_id]

@[reassoc (attr := simp)]
theorem affineLineConstant_restriction (P : PresheafWithTransfers.{v} k) :
    affineLineConstant P ≫ contractionRestriction P = torusConstant P := by
  rw [affineLineConstant, contractionRestriction, ← parameterPullback_comp, comp_toBase]
  rfl

/-- Constants vanish in the actual Laurent quotient without a HI hypothesis. -/
@[reassoc (attr := simp)]
theorem torusConstant_toContraction (P : PresheafWithTransfers.{v} k) :
    torusConstant P ≫ toContraction P = 0 := by
  rw [← affineLineConstant_restriction, Category.assoc,
    contractionRestriction_toContraction, comp_zero]

/-- The displayed coordinate change gives the actual coefficient affine projection. -/
@[reassoc]
theorem affineLineConstant_app_projection (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    transfer P ((Cor.graphFunctor k).map (productBaseIso X.toSmoothSite).hom) ≫
      (affineLineConstant P).hom.app (op X) =
        A1.projectionPullback (.of k) ((toPresheaf k).obj P) X.toSmoothSite := by
  change transfer P ((Cor.graphFunctor k).map (productBaseIso X.toSmoothSite).hom) ≫
    transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 _) (toBase _))) = _
  rw [← transfer_comp, ← Functor.map_comp, productMap_toBase]
  rfl

/-- Coefficient HI makes this precise affine constant map invertible. -/
theorem affineLineConstant_isIso (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) : IsIso (affineLineConstant P) := by
  have : ∀ X, IsIso ((affineLineConstant P).hom.app X) := by
    intro X
    let e := P.obj.mapIso ((Cor.graphFunctor k).mapIso
      (productBaseIso X.unop.toSmoothSite)).op
    have : IsIso (e.hom ≫ (affineLineConstant P).hom.app X) := by
      change IsIso (transfer P ((Cor.graphFunctor k).map
        (productBaseIso X.unop.toSmoothSite).hom) ≫ _)
      rw [affineLineConstant_app_projection]
      exact hP X.unop.toSmoothSite
    exact IsIso.of_isIso_comp_left e.hom _
  have h : IsIso (affineLineConstant P).hom := NatIso.isIso_of_isIso_app _
  exact (ObjectProperty.isIso_hom_iff (affineLineConstant P)).mp h

/-- The actual kernel in the additive-functor category, not an assumed transfer action. -/
def contractionKernel (P : PresheafWithTransfers.{v} k) : PresheafWithTransfers.{v} k :=
  kernel (torusUnit P)

/-- Project away from the genuine unit-constant component. -/
def contractionKernelProjection (P : PresheafWithTransfers.{v} k) :
    torusSections P ⟶ contractionKernel P :=
  splitKernelProjection (torusConstant P) (torusUnit P) (torusConstant_unit P)

@[reassoc (attr := simp)]
theorem contractionKernelProjection_ι (P : PresheafWithTransfers.{v} k) :
    contractionKernelProjection P ≫ kernel.ι (torusUnit P) =
      𝟙 (torusSections P) - torusUnit P ≫ torusConstant P :=
  splitKernelProjection_ι _ _ _

/-- HI is used only to identify the affine image with the constant summand. -/
theorem contractionRestriction_kernelProjection (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) :
    contractionRestriction P ≫ contractionKernelProjection P = 0 := by
  have : IsIso (affineLineConstant P) := affineLineConstant_isIso P hP
  have : Epi (affineLineConstant P) := IsIso.epi_of_iso _
  apply (cancel_epi (affineLineConstant P)).mp
  rw [← Category.assoc, affineLineConstant_restriction, comp_zero]
  exact comp_splitKernelProjection _ _ _

/-- The genuine quotient-to-kernel isomorphism with explicit canonical maps. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/ContractionHI.lean:102-112,138-153"
  "adaptation" "Native additive-functor quotient, actual unit, signed transfers and coefficients"]
def contractionIsoKernel (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    contraction P ≅ contractionKernel P where
  hom := contractionDesc P (contractionKernelProjection P)
    (contractionRestriction_kernelProjection P hP)
  inv := kernel.ι (torusUnit P) ≫ toContraction P
  hom_inv_id := by
    have : Epi (toContraction P) :=
      inferInstanceAs (Epi (cokernel.π (contractionRestriction P)))
    apply (cancel_epi (toContraction P)).mp
    simp only [← Category.assoc, toContraction_desc, Category.comp_id]
    rw [contractionKernelProjection_ι, Preadditive.sub_comp,
      Category.id_comp, Category.assoc, torusConstant_toContraction, comp_zero, sub_zero]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (torusUnit P))).mp
    simp only [Category.assoc, toContraction_desc_assoc, contractionKernelProjection_ι,
      Category.id_comp]
    simp only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      kernel.condition, zero_comp, sub_zero]

/-- Its inverse is exactly kernel inclusion followed by the actual quotient. -/
@[reassoc, simp]
theorem contractionIsoKernel_inv_quotient (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) :
    (contractionIsoKernel P hP).inv = kernel.ι (torusUnit P) ≫ toContraction P := rfl

/-- Its forward map subtracts precisely the actual constant summand. -/
@[reassoc]
theorem contractionIsoKernel_hom_projection (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) :
    toContraction P ≫ (contractionIsoKernel P hP).hom ≫ kernel.ι (torusUnit P) =
      𝟙 (torusSections P) - torusUnit P ≫ torusConstant P := by
  simp [contractionIsoKernel]

/-- The coefficient group decomposes as its actual constant and contraction summands. -/
theorem contraction_split_identity (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) :
    torusUnit P ≫ torusConstant P +
      toContraction P ≫ (contractionIsoKernel P hP).hom ≫ kernel.ι (torusUnit P) =
        𝟙 (torusSections P) := by
  rw [contractionIsoKernel_hom_projection, add_comm, sub_add_cancel]

/-- Base coordinates identify the unit map with the genuine native section into `X`. -/
theorem torusUnit_app_actual (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    (torusUnit P).hom.app (op X) ≫
      transfer P ((Cor.graphFunctor k).map (productBaseIso X.toSmoothSite).inv) =
        transfer P ((Cor.graphFunctor k).map (unitSection.app X.toSmoothSite)) := by
  change transfer P ((Cor.graphFunctor k).map
      (SmoothSite.productMap (𝟙 X.toSmoothSite) (SmoothSite.torusOne (Spec (.of k))))) ≫
    transfer P ((Cor.graphFunctor k).map (productBaseIso X.toSmoothSite).inv) = _
  rw [← transfer_comp, ← Functor.map_comp, baseProduct_unit]

/-- Objectwise the kernel is precisely the kernel of restriction to the native unit section. -/
def contractionSectionsIsoUnitKernel (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) (X : Cor k) :
    sections (contraction P) X ≅
      kernel (transfer P ((Cor.graphFunctor k).map (unitSection.app X.toSmoothSite))) := by
  let E := forget ⋙ (CategoryTheory.evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X)
  let e := P.obj.mapIso ((Cor.graphFunctor k).mapIso
    (productBaseIso X.toSmoothSite)).symm.op
  exact E.mapIso (contractionIsoKernel P hP) ≪≫
    PreservesKernel.iso E (torusUnit P) ≪≫
    (kernelCompMono ((torusUnit P).hom.app (op X)) e.hom).symm ≪≫
    kernelIsoOfEq (torusUnit_app_actual P X)

end AlgebraicGeometry.PresheafWithTransfers
