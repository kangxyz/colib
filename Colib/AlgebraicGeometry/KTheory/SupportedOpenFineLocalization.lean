/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.SupportedOpenQcqsComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenLongExactSequence

/-!
# Fixed-pair supported fine connective localization

The actual positive restriction equivalence transports the existing coarse boundary.
All three range/kernel positions include the K-one to K-zero tail. Union compactness
suffices, without an extra compactness assumption on the source open. No full-target
K-zero surjectivity, arbitrary-pair naturality or coherent prespectrum transport is asserted.

Adapted from Quillen SupportedOpen/GlobalLocalization.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd; support-forgetting naturality is separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))

include hW

/-- Genuine supported boundary from original perfect K-theory of the compact open. -/
def perfectSupportedConnectingHomOfUnionCompact (n : ℕ) :
    PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1) →*
      PerfectSupportedK (T ⊔ j.opensRange).ι n :=
  (perfectSupportedOpenConnectingHom j T n).comp
    (perfectSupportedOpenKEquivOfUnionCompact j T hW n).symm.toMonoidHom

/-- The transported boundary retains the entire original relative boundary homomorphism. -/
theorem perfectSupportedConnectingHomOfUnionCompact_comp_relative (n : ℕ) :
    (perfectSupportedConnectingHomOfUnionCompact j T hW n).comp
      (perfectSupportedOpenKRestrict j T (n + 1)) =
    perfectSupportedOpenConnectingHom j T n := by
  ext a
  change perfectSupportedOpenConnectingHom j T n
    ((perfectSupportedOpenKEquivOfUnionCompact j T hW n).symm
      ((perfectSupportedOpenKEquivOfUnionCompact j T hW n) a)) =
      _
  rw [MulEquiv.symm_apply_apply]

/-- Exactness at original perfect K-theory on the qcqs base, including degree zero. -/
theorem range_perfectSupportedUnionKMap_eq_ker_perfectSupportedKRestrict (n : ℕ) :
    (perfectSupportedUnionKMap j T n).range =
      (perfectSupportedKRestrict j T n).ker := by
  rw [range_perfectSupportedUnionKMap_eq_ker_perfectSupportedOpenKMap]
  ext x
  change perfectSupportedOpenKMap j T n x = 1 ↔
    perfectSupportedKRestrict j T n x = 1
  have he := DFunLike.congr_fun
    (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T n) x
  constructor
  · intro hx
    rw [← he, MonoidHom.comp_apply, hx, map_one]
  · intro hx
    apply perfectSupportedOpenKRestrict_injective_of_union_compact j T hW n
    exact he.trans (hx.trans (map_one _).symm)

/-- The new boundary has exactly the original relative boundary image. -/
theorem range_perfectSupportedConnectingHomOfUnionCompact (n : ℕ) :
    (perfectSupportedConnectingHomOfUnionCompact j T hW n).range =
      (perfectSupportedOpenConnectingHom j T n).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(perfectSupportedOpenKEquivOfUnionCompact j T hW n).symm a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨perfectSupportedOpenKEquivOfUnionCompact j T hW n a, ?_⟩
    exact DFunLike.congr_fun (perfectSupportedConnectingHomOfUnionCompact_comp_relative j T hW n) a

/-- Exactness at original supported perfect K-theory, including its degree-zero group. -/
theorem range_perfectSupportedConnectingHomOfUnionCompact_eq_ker_perfectSupportedUnionKMap (n : ℕ) :
    (perfectSupportedConnectingHomOfUnionCompact j T hW n).range =
      (perfectSupportedUnionKMap j T n).ker := by
  rw [range_perfectSupportedConnectingHomOfUnionCompact,
    range_perfectSupportedOpenConnectingHom_eq_ker_perfectSupportedUnionKMap]

/-- Exactness at positive original perfect K-theory of the compact open. -/
theorem range_perfectSupportedKRestrict_eq_ker_perfectSupportedConnectingHomOfUnionCompact (n : ℕ) :
    (perfectSupportedKRestrict j T (n + 1)).range =
      (perfectSupportedConnectingHomOfUnionCompact j T hW n).ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change perfectSupportedConnectingHomOfUnionCompact j T hW n
      (perfectSupportedKRestrict j T (n + 1) a) = 1
    rw [← DFunLike.congr_fun
      (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T (n + 1)) a]
    change ((perfectSupportedConnectingHomOfUnionCompact j T hW n).comp
      (perfectSupportedOpenKRestrict j T (n + 1)))
      (perfectSupportedOpenKMap j T (n + 1) a) = 1
    rw [perfectSupportedConnectingHomOfUnionCompact_comp_relative]
    have hm : perfectSupportedOpenKMap j T (n + 1) a ∈
        (perfectSupportedOpenKMap j T (n + 1)).range := ⟨a, rfl⟩
    rw [range_perfectSupportedOpenKMap_eq_ker_perfectSupportedOpenConnectingHom] at hm
    exact hm
  · intro hx
    have hm : (perfectSupportedOpenKEquivOfUnionCompact j T hW n).symm x ∈
        (perfectSupportedOpenConnectingHom j T n).ker := hx
    rw [← range_perfectSupportedOpenKMap_eq_ker_perfectSupportedOpenConnectingHom] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [← DFunLike.congr_fun
      (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T (n + 1)) a]
    change perfectSupportedOpenKEquivOfUnionCompact j T hW n
      (perfectSupportedOpenKMap j T (n + 1) a) = x
    rw [ha, MulEquiv.apply_symm_apply]

/-- All recurring positions of the actual qcqs open connective localization sequence. -/
theorem perfectSupported_positiveLongExactSequence_of_union_compact (n : ℕ) :
    (perfectSupportedKRestrict j T (n + 1)).range =
      (perfectSupportedConnectingHomOfUnionCompact j T hW n).ker ∧
    (perfectSupportedConnectingHomOfUnionCompact j T hW n).range =
      (perfectSupportedUnionKMap j T n).ker ∧
    (perfectSupportedUnionKMap j T n).range =
      (perfectSupportedKRestrict j T n).ker :=
  ⟨range_perfectSupportedKRestrict_eq_ker_perfectSupportedConnectingHomOfUnionCompact j T hW n,
    range_perfectSupportedConnectingHomOfUnionCompact_eq_ker_perfectSupportedUnionKMap j T hW n,
    range_perfectSupportedUnionKMap_eq_ker_perfectSupportedKRestrict j T hW n⟩

/-- The actual K₁(open) → K₀(support) → K₀(base) → K₀(open) exact tail. -/
theorem perfectSupported_zeroTail_of_union_compact :
    (perfectSupportedKRestrict j T 1).range =
      (perfectSupportedConnectingHomOfUnionCompact j T hW 0).ker ∧
    (perfectSupportedConnectingHomOfUnionCompact j T hW 0).range =
      (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range =
      (perfectSupportedKRestrict j T 0).ker :=
  perfectSupported_positiveLongExactSequence_of_union_compact j T hW 0

/-- Compatibility with the unchanged relative boundary determines this endpoint uniquely. -/
theorem perfectSupportedConnectingHomOfUnionCompact_unique (n : ℕ)
    (δ : PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1) →* PerfectSupportedK (T ⊔ j.opensRange).ι n)
    (hδ : δ.comp (perfectSupportedOpenKRestrict j T (n + 1)) = perfectSupportedOpenConnectingHom j T
      n) :
    δ = perfectSupportedConnectingHomOfUnionCompact j T hW n := by
  ext x
  obtain ⟨a, rfl⟩ := (perfectSupportedOpenKEquivOfUnionCompact j T hW n).surjective x
  exact DFunLike.congr_fun
    (hδ.trans (perfectSupportedConnectingHomOfUnionCompact_comp_relative j T hW
    n).symm) a

end AlgebraicGeometry.Scheme.Modules
