/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenForget
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenFineLocalization
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectiveLocalization

/-!
# Forgetting auxiliary support in fine localization

The actual supported positive inverse and fine boundary commute with forgetting the
auxiliary support. Both the source open and its union with the auxiliary open are compact:
the ordinary comparison needs the former, and the supported comparison needs the latter.
The degree-zero boundary is the K₁-to-K₀ map, not an inverse on full target K₀.
These are group-level squares, not coherent prespectrum naturality.

Adapted from Quillen SupportedOpen/GlobalLocalization.lean:172-207 at
c561118b7795eb9780be9ed391c3251d6a4d0afd, with the native ordinary restriction equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))

/-- Forgetting auxiliary support commutes with the actual positive restriction inverse. -/
theorem perfectSupportedOpenKEquivOfUnionCompact_symm_forget (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1)) :
    perfectSupportedOpenKForget j T (n + 1)
        ((perfectSupportedOpenKEquivOfUnionCompact j T hW n).symm x) =
      (letI : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
        ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
       (OpenDerivedImage.relativeKRestrictEquiv j
         (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n).symm
         (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1) x)) := by
  let : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
    ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
  apply (OpenDerivedImage.relativeKRestrictEquiv j
    (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n).injective
  change perfectOpenKRestrict j (n + 1)
    (perfectSupportedOpenKForget j T (n + 1)
      ((perfectSupportedOpenKEquivOfUnionCompact j T hW n).symm x)) = _
  have hs := DFunLike.congr_fun (perfectSupportedOpenKForget_comp_restrict j T (n + 1))
    ((perfectSupportedOpenKEquivOfUnionCompact j T hW n).symm x)
  simp only [MonoidHom.comp_apply] at hs
  rw [hs]
  change perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1)
    (perfectSupportedOpenKEquivOfUnionCompact j T hW n
      ((perfectSupportedOpenKEquivOfUnionCompact j T hW n).symm x)) = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- The fine boundary square retains the original coarse boundary and its sign. -/
theorem perfectSupportedConnectingHomOfUnionCompact_forget (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp
        (perfectSupportedConnectingHomOfUnionCompact j T hW n) =
      (perfectQcqsConnectingHom j n).comp
        (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1)) := by
  ext x
  obtain ⟨a, rfl⟩ :=
    (perfectSupportedOpenKRestrict_succ_bijective_of_union_compact j T hW n).surjective x
  have h₁ := DFunLike.congr_fun
    (perfectSupportedConnectingHomOfUnionCompact_comp_relative j T hW n) a
  have h₂ := DFunLike.congr_fun (perfectSupportedOpenConnectingHom_forget j T n) a
  have h₃ := DFunLike.congr_fun (perfectSupportedOpenKForget_comp_restrict j T (n + 1)) a
  have h₄ := DFunLike.congr_fun (perfectQcqsConnectingHom_comp_relative j n)
    (perfectSupportedOpenKForget j T (n + 1) a)
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ h₄ ⊢
  rw [h₁, h₂, ← h₃, h₄]

/-- Original compact-open hypotheses imply the supported positive inverse square. -/
theorem qcqsPerfectSupportedOpenKEquiv_symm_forget (hT : IsCompact (T : Set X))
    (n : ℕ) (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1)) :
    perfectSupportedOpenKForget j T (n + 1)
        ((perfectSupportedOpenKEquivOfUnionCompact j T
          (isCompact_supportedUnion j T hT) n).symm x) =
      (letI : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
        ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
       (OpenDerivedImage.relativeKRestrictEquiv j
         (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n).symm
         (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1) x)) :=
  perfectSupportedOpenKEquivOfUnionCompact_symm_forget j T (isCompact_supportedUnion j T hT) n x

/-- Original compact-open hypotheses imply the boundary square, including K₁ to K₀. -/
theorem qcqsPerfectSupportedConnectingHom_forget (hT : IsCompact (T : Set X)) (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp
        (perfectSupportedConnectingHomOfUnionCompact j T (isCompact_supportedUnion j T hT) n) =
      (perfectQcqsConnectingHom j n).comp
        (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1)) :=
  perfectSupportedConnectingHomOfUnionCompact_forget j T (isCompact_supportedUnion j T hT) n

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0336",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/GlobalLocalization.lean:172-207"
    "adaptation"
    "Actual positive inverse and fine boundary under auxiliary-support forgetting"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedOpenKEquivOfUnionCompact_symm_forget
  AlgebraicGeometry.Scheme.Modules.perfectSupportedConnectingHomOfUnionCompact_forget
  AlgebraicGeometry.Scheme.Modules.qcqsPerfectSupportedOpenKEquiv_symm_forget
  AlgebraicGeometry.Scheme.Modules.qcqsPerfectSupportedConnectingHom_forget
