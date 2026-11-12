/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FiniteFrames

/-!
# A single coefficient restriction for two pairs of boundary frames

The two compactification diagrams use the same affine base neighborhood.
The frame on each full boundary is the restriction of its original
invertible module to the entire inverse image of that neighborhood.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Ample
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- Both marked boundary pairs admit frames on one original coefficient open. -/
theorem exists_commonPrincipalPairedBoundaryFrames
    {S D₁ Z₁ D₂ Z₂ : Scheme.{u}} [IsAffine S]
    (bD₁ : D₁ ⟶ S) [IsFinite bD₁] (bZ₁ : Z₁ ⟶ S) [IsFinite bZ₁]
    (bD₂ : D₂ ⟶ S) [IsFinite bD₂] (bZ₂ : Z₂ ⟶ S) [IsFinite bZ₂]
    (MD₁ : D₁.Modules) [IsInvertibleModule D₁ MD₁]
    (MZ₁ : Z₁.Modules) [IsInvertibleModule Z₁ MZ₁]
    (MD₂ : D₂.Modules) [IsInvertibleModule D₂ MD₂]
    (MZ₂ : Z₂.Modules) [IsInvertibleModule Z₂ MZ₂]
    (x : S) (W : S.Opens) (hxW : x ∈ W) :
    ∃ r : Γ(S, ⊤), x ∈ S.basicOpen r ∧ S.basicOpen r ≤ W ∧
      Nonempty (MD₁.restrict (bD₁ ⁻¹ᵁ S.basicOpen r).ι ≅
        SheafOfModules.unit (bD₁ ⁻¹ᵁ S.basicOpen r).toScheme.ringCatSheaf) ∧
      Nonempty (MZ₁.restrict (bZ₁ ⁻¹ᵁ S.basicOpen r).ι ≅
        SheafOfModules.unit (bZ₁ ⁻¹ᵁ S.basicOpen r).toScheme.ringCatSheaf) ∧
      Nonempty (MD₂.restrict (bD₂ ⁻¹ᵁ S.basicOpen r).ι ≅
        SheafOfModules.unit (bD₂ ⁻¹ᵁ S.basicOpen r).toScheme.ringCatSheaf) ∧
      Nonempty (MZ₂.restrict (bZ₂ ⁻¹ᵁ S.basicOpen r).ι ≅
        SheafOfModules.unit (bZ₂ ⁻¹ᵁ S.basicOpen r).toScheme.ringCatSheaf) := by
  obtain ⟨t, hxt, htW, ⟨eD₁⟩, ⟨eZ₁⟩⟩ :=
    exists_commonPrincipalBoundaryFrames bD₁ bZ₁ MD₁ MZ₁ x W hxW
  obtain ⟨r, hxr, hrt, eD₂, eZ₂⟩ :=
    exists_commonPrincipalBoundaryFrames bD₂ bZ₂ MD₂ MZ₂ x (S.basicOpen t) hxt
  refine ⟨r, hxr, hrt.trans htW, ?_, ?_, eD₂, eZ₂⟩
  · exact ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE MD₁ (fun _ hx ↦ hrt hx) eD₁⟩
  · exact ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE MZ₁ (fun _ hx ↦ hrt hx) eZ₁⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
