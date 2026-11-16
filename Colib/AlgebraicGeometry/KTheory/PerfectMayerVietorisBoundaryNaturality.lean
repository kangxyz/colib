/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietoris

/-! # Naturality of the actual excision-defined Mayer–Vietoris boundary -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris

universe u

variable {V X V' X' : Scheme.{u}}
  [CompactSpace V] [QuasiSeparatedSpace V]
  [CompactSpace V'] [QuasiSeparatedSpace V']
  (j : V ⟶ X) (j' : V' ⟶ X') [IsOpenImmersion j] [IsOpenImmersion j']
  (T : X.Opens) (T' : X'.Opens)
  [CompactSpace (j ⁻¹ᵁ T).toScheme] [CompactSpace (j' ⁻¹ᵁ T').toScheme]
  (hc : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
  (hc' : ∀ x : X', x ∈ Set.range j' ∨ x ∈ T')

attribute [local instance] HasDerivedCategory.standard

/-- Naturality of restriction, support forgetting and the localization boundary
implies naturality of the canonical Mayer–Vietoris connecting map. -/
theorem connectingHom_natural_of_support_squares (n : ℕ)
    (s : PerfectSupportedK T.ι n →* PerfectSupportedK T'.ι n)
    (t : PerfectSupportedK (j ⁻¹ᵁ T).ι n →* PerfectSupportedK (j' ⁻¹ᵁ T').ι n)
    (f : perfectK X n →* perfectK X' n)
    (g : perfectK (j ⁻¹ᵁ T).toScheme (n + 1) →* perfectK (j' ⁻¹ᵁ T').toScheme (n + 1))
    (hres : (perfectSupportedKRestrict j' T' n).comp s =
      t.comp (perfectSupportedKRestrict j T n))
    (hforget : (perfectSupportedKMap T'.ι n).comp s = f.comp (perfectSupportedKMap T.ι n))
    (hδ : (perfectQcqsConnectingHom (j' ⁻¹ᵁ T').ι n).comp g =
      t.comp (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n)) :
    (connectingHom j' T' hc' n).comp g = f.comp (connectingHom j T hc n) := by
  refine MonoidHom.ext fun a => ?_
  let e := perfectSupportedExcisionKEquiv j T hc n
  let e' := perfectSupportedExcisionKEquiv j' T' hc' n
  let δ := perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n
  let δ' := perfectQcqsConnectingHom (j' ⁻¹ᵁ T').ι n
  have he : e'.symm (δ' (g a)) = s (e.symm (δ a)) := by
    apply e'.injective
    rw [MulEquiv.apply_symm_apply]
    have ha := DFunLike.congr_fun hres (e.symm (δ a))
    change e' (s (e.symm (δ a))) = t (e (e.symm (δ a))) at ha
    rw [MulEquiv.apply_symm_apply] at ha
    exact (DFunLike.congr_fun hδ a).trans ha.symm
  change perfectSupportedKMap T'.ι n (e'.symm (δ' (g a))) =
    f (perfectSupportedKMap T.ι n (e.symm (δ a)))
  rw [he]
  exact DFunLike.congr_fun hforget (e.symm (δ a))

end AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris
