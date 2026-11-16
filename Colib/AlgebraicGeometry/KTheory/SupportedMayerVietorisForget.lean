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

local notation "I₀" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "Z'" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) Z
local notation "i" => Scheme.Opens.ι T
local notation "b" => Scheme.Opens.ι I₀

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
    (Z ⊔ (i).opensRange) (fiberOpen_eq j T Z)

private theorem inverseForgetSquare {A B C D : Type*}
    [Monoid A] [Monoid B] [Monoid C] [Monoid D]
    (e : A ≃* B) (f : C ≃* D) (g : A →* C) (h : B →* D)
    (square : h.comp e.toMonoidHom = f.toMonoidHom.comp g) :
    g.comp e.symm.toMonoidHom = f.symm.toMonoidHom.comp h := by
  ext x
  apply f.injective
  change f (g (e.symm x)) = f (f.symm (h x))
  have hx := DFunLike.congr_fun square (e.symm x)
  change h (e (e.symm x)) = f (g (e.symm x)) at hx
  rw [e.apply_symm_apply] at hx
  rw [f.apply_symm_apply]
  exact hx.symm

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
  exact inverseForgetSquare (fiberEquiv j T Z hcover n)
    (perfectSupportedExcisionKEquiv j T hcover n)
    (perfectSupportedUnionForgetKMap i Z n)
    (perfectSupportedUnionForgetKMap b Z' n)
    (fiberEquiv_comp_forget j T Z hcover n)

variable [QuasiSeparatedSpace X] [CompactSpace V] [QuasiSeparatedSpace V]
  [CompactSpace (j ⁻¹ᵁ T).toScheme] (hZ : IsCompact (Z : Set X))

set_option maxHeartbeats 800000 in
/-- Forgetting auxiliary support commutes with the two-open boundary, including K₁ to K₀. -/
@[colib_tag "COL-0336",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/MayerVietorisForget.lean:77-129"
    "adaptation" "Forget auxiliary support in the actual two-open Mayer–Vietoris boundary"]
theorem connectingHom_forget (n : ℕ) :
    (perfectSupportedKMap Z.ι n).comp (connectingHom j T Z hcover hZ n) =
      (PerfectMayerVietoris.connectingHom j T hcover n).comp
        (perfectSupportedKMap (b ⁻¹ᵁ Z').ι (n + 1)) := by
  let hV := (isCompact_range (b).continuous).union (j.isCompact_preimage hZ)
  let δ := perfectSupportedConnectingHomOfUnionCompact b Z' hV n
  let e := (fiberEquiv j T Z hcover n).symm.toMonoidHom
  let e' := (perfectSupportedExcisionKEquiv j T hcover n).symm.toMonoidHom
  let forgetX := perfectSupportedUnionForgetKMap i Z n
  let forgetV := perfectSupportedUnionForgetKMap b Z' n
  let forgetI := perfectSupportedKMap (b ⁻¹ᵁ Z').ι (n + 1)
  let U : Scheme.{u} := (j ⁻¹ᵁ T).toScheme
  let standard : HasDerivedCategory U.Modules := HasDerivedCategory.standard _
  let fine := Scheme.Modules.hasDerivedCategory U
  let δ' := @perfectQcqsConnectingHom U V _ _ _ b _ standard n
  let δFine := @perfectQcqsConnectingHom U V _ _ _ b _ fine n
  let incl := perfectSupportedKMap i n
  have h₁ :
      (perfectSupportedKMap Z.ι n).comp (perfectSupportedUnionKMap i Z n) =
        incl.comp forgetX :=
    perfectSupportedUnionKMap_comp_forget i Z n
  have h₂ : forgetX.comp e = e'.comp forgetV :=
    fiberEquiv_symm_comp_forget j T Z hcover n
  have hδ : δFine = δ' :=
    @perfectQcqsConnectingHom_unique U V _ _ _ b _ standard n δFine
      (@perfectQcqsConnectingHom_comp_relative U V _ _ _ b _ fine n)
  have h₃ : forgetV.comp δ = δ'.comp forgetI := by
    rw [← hδ]
    exact perfectSupportedConnectingHomOfUnionCompact_forget b Z' hV n
  unfold connectingHom lowerBoundary
    PerfectMayerVietoris.connectingHom PerfectMayerVietoris.lowerBoundary
  change (perfectSupportedKMap Z.ι n).comp ((perfectSupportedUnionKMap i Z n).comp
    (e.comp δ)) = (incl.comp (e'.comp δ')).comp forgetI
  calc
    _ = (incl.comp forgetX).comp (e.comp δ) :=
      congrArg (fun k ↦ k.comp (e.comp δ)) h₁
    _ = incl.comp ((forgetX.comp e).comp δ) := rfl
    _ = incl.comp ((e'.comp forgetV).comp δ) :=
      congrArg (fun k ↦ incl.comp (k.comp δ)) h₂
    _ = incl.comp (e'.comp (forgetV.comp δ)) := rfl
    _ = incl.comp (e'.comp (δ'.comp forgetI)) :=
      congrArg (fun k ↦ incl.comp (e'.comp k)) h₃
    _ = _ := rfl

end AlgebraicGeometry.Scheme.Modules.SupportedMayerVietoris
