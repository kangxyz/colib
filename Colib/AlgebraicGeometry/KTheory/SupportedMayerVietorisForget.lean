/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietoris
public import Colib.AlgebraicGeometry.KTheory.SupportedMayerVietorisMaps
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenFineForget

/-!
# Forgetting auxiliary support in Mayer–Vietoris

For a two-open cover, forgetting auxiliary support commutes with the actual
excision inverse and hence with the signed Mayer–Vietoris boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.SupportedMayerVietoris

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

local notation "i" => T.ι
local notation "b" => (j ⁻¹ᵁ T).ι
local notation "Z'" => j ⁻¹ᵁ Z

/-- The excision restriction commutes with forgetting auxiliary support. -/
theorem fiberEquiv_comp_forget (n : ℕ) :
    (perfectSupportedUnionForgetKMap b Z' n).comp
        (fiberEquiv j T Z hcover n).toMonoidHom =
      (perfectSupportedKRestrict j T n).comp
        (perfectSupportedUnionForgetKMap i Z n) := by
  rw [fiberEquiv_toMonoidHom]
  unfold perfectSupportedUnionForgetKMap perfectSupportedKRestrict
  rw [KMap_comp_KMap, KMap_comp_KMap]
  apply KMap_eq_of_iso _ _
  apply Functor.fullyFaithfulCancelRight ((perfectSupported b).ι)
  exact perfectSupportedRestrictCongrCompInclusion j
    (Z ⊔ i.opensRange) (fiberOpen_eq j T Z)

/-- The actual excision inverse also commutes with forgetting auxiliary support. -/
@[colib_tag "COL-0336",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/MayerVietorisForget.lean:52-68"
    "adaptation" "The inverse of the actual support excision map retains forgetfulness"]
theorem fiberEquiv_symm_comp_forget (n : ℕ) :
    (perfectSupportedUnionForgetKMap i Z n).comp
        (fiberEquiv j T Z hcover n).symm.toMonoidHom =
      (perfectSupportedExcisionKEquiv j T hcover n).symm.toMonoidHom.comp
        (perfectSupportedUnionForgetKMap b Z' n) := by
  refine MonoidHom.ext fun x ↦ ?_
  apply (perfectSupportedExcisionKEquiv j T hcover n).injective
  have h := DFunLike.congr_fun (fiberEquiv_comp_forget j T Z hcover n)
    ((fiberEquiv j T Z hcover n).symm x)
  change perfectSupportedUnionForgetKMap b Z' n
    (fiberEquiv j T Z hcover n ((fiberEquiv j T Z hcover n).symm x)) =
      perfectSupportedKRestrict j T n
        (perfectSupportedUnionForgetKMap i Z n ((fiberEquiv j T Z hcover n).symm x)) at h
  rw [MulEquiv.apply_symm_apply] at h
  change perfectSupportedKRestrict j T n
    (perfectSupportedUnionForgetKMap i Z n ((fiberEquiv j T Z hcover n).symm x)) =
      perfectSupportedExcisionKEquiv j T hcover n
        ((perfectSupportedExcisionKEquiv j T hcover n).symm
          (perfectSupportedUnionForgetKMap b Z' n x))
  rw [MulEquiv.apply_symm_apply]
  exact h.symm

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] [QuasiSeparatedSpace V]
  [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme] (hZ : IsCompact (Z : Set X))

/-- Forgetting auxiliary support commutes with the two-open boundary, including (K_1	o K_0). -/
@[colib_tag "COL-0336",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/MayerVietorisForget.lean:77-129"
    "adaptation" "Forget auxiliary support in the actual two-open Mayer–Vietoris boundary"]
theorem connectingHom_forget (n : ℕ) :
    (perfectSupportedKMap Z.ι n).comp (connectingHom j T Z hcover hZ n) =
      (PerfectMayerVietoris.connectingHom j T hcover n).comp
        (perfectSupportedKMap (b ⁻¹ᵁ Z').ι (n + 1)) := by
  refine MonoidHom.ext fun x ↦ ?_
  let hV := (isCompact_range b.continuous).union (j.isCompact_preimage hZ)
  let δ := perfectSupportedConnectingHomOfUnionCompact b Z' hV n
  let e := fiberEquiv j T Z hcover n
  let e' := perfectSupportedExcisionKEquiv j T hcover n
  have h₁ := DFunLike.congr_fun (perfectSupportedUnionKMap_comp_forget i Z n)
    (e.symm (δ x))
  have h₂ := DFunLike.congr_fun (fiberEquiv_symm_comp_forget j T Z hcover n) (δ x)
  have h₃ := DFunLike.congr_fun (perfectSupportedConnectingHomOfUnionCompact_forget b Z' hV n) x
  simpa only [connectingHom, lowerBoundary, PerfectMayerVietoris.connectingHom,
    PerfectMayerVietoris.lowerBoundary, MonoidHom.comp_apply] using
    h₁.trans ((congrArg (perfectSupportedKMap i n) h₂).trans
      (congrArg (fun y ↦ perfectSupportedKMap i n (e'.symm y)) h₃))

end AlgebraicGeometry.Scheme.Modules.SupportedMayerVietoris
