/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Group.MayerVietoris
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedExcision
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectiveLocalization
public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackCompatibility
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectingNaturality
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula

/-!
# The canonical maps for two-open Mayer–Vietoris in perfect K-theory

For a compact two-open cover of a quasi-separated scheme, the overlap boundary
is the genuine connective localization boundary followed by support excision
and forgetting support. The first-minus-second overlap convention is fixed.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/MayerVietoris.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris

/-- The canonical perfect K-group used by the restriction maps. -/
abbrev perfectK (Y : Scheme.{u}) (n : ℕ) :=
  (perfectComplexesWaldhausen Y.toRingedSpace).K n

local notation "𝒦(" Y ", " n ")" => perfectK Y n
local notation "resK(" j ", " n ")" =>
  Waldhausen.KMap (perfectComplexesRestrictOpenImmersion_isExact j) n
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  [QuasiSeparatedSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens) [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ
    T).toScheme]
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

attribute [local instance] HasDerivedCategory.standard

local instance : IsOpenImmersion (j.resLE T (j ⁻¹ᵁ T) le_rfl) := by
  let : IsOpenImmersion (j.resLE T (j ⁻¹ᵁ T) le_rfl ≫ T.ι) := by
    rw [j.resLE_comp_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ T.ι

/-- The commutative structure on original perfect K-groups supplied by additivity. -/
local instance (Y : Scheme.{u}) (n : ℕ) : CommGroup (𝒦(Y, n)) :=
  Waldhausen.Additivity.KCommGroup (perfectComplexesWaldhausen Y.toRingedSpace) n

/-- The original restriction pair, with the T factor first. -/
def restrictionPair (n : ℕ) : 𝒦(X, n) →* 𝒦(T.toScheme, n) × 𝒦(V, n) :=
  GroupMayerVietoris.pair (resK(T.ι, n)) (resK(j, n))

/-- The original overlap difference is the T-restriction times the inverse
of the V-restriction. This fixes the Mayer–Vietoris sign convention. -/
def overlapDifference (n : ℕ) : 𝒦(T.toScheme, n) × 𝒦(V, n) →*
    𝒦((j ⁻¹ᵁ T).toScheme, n) :=
  GroupMayerVietoris.difference
    (resK((j.resLE T (j ⁻¹ᵁ T) le_rfl), n))
    (resK((j ⁻¹ᵁ T).ι, n))

/-- The lower original localization boundary, transported through actual
support excision and retaining the existing supported group on X. -/
def lowerBoundary (n : ℕ) : 𝒦((j ⁻¹ᵁ T).toScheme, (n+1)) →* PerfectSupportedK T.ι n :=
  (perfectSupportedExcisionKEquiv j T hcover n).symm.toMonoidHom.comp
    (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n)

/-- The genuine original boundary into K(X), with no new choice of endpoint map. -/
def connectingHom (n : ℕ) : 𝒦((j ⁻¹ᵁ T).toScheme, (n+1)) →* 𝒦(X, n) :=
  (perfectSupportedKMap T.ι n).comp (lowerBoundary j T hcover n)

omit [QuasiSeparatedSpace X] [QuasiSeparatedSpace V] [CompactSpace (j ⁻¹ᵁ T).toScheme] in
/-- The actual two restriction routes agree by the original resLE square. -/
lemma restriction_square (n : ℕ) :
    (resK((j.resLE T (j ⁻¹ᵁ T) le_rfl), n)).comp (resK(T.ι, n)) =
      (resK((j ⁻¹ᵁ T).ι, n)).comp (resK(j, n)) := by
  rw [← perfectKPullback_eq_restrict, ← perfectKPullback_eq_restrict,
    ← perfectKPullback_eq_restrict, ← perfectKPullback_eq_restrict,
    ← perfectKPullback_comp, ← perfectKPullback_comp]
  rw [j.resLE_comp_ι]

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T.toScheme] in
/-- Exactness of the transported lower boundary at the original support group. -/
lemma range_lowerBoundary (n : ℕ) :
    (lowerBoundary j T hcover n).range =
      ((resK(j, n)).comp (perfectSupportedKMap T.ι n)).ker := by
  have hs := perfectSupportedKRestrict_comp_forget j T n
  have hs' (a : PerfectSupportedK T.ι n) :
      perfectSupportedKMap (j ⁻¹ᵁ T).ι n (perfectSupportedKRestrict j T n a) =
        resK(j, n) (perfectSupportedKMap T.ι n a) := DFunLike.congr_fun hs a
  have he := (perfectQcqs_positiveLongExactSequence (j ⁻¹ᵁ T).ι n).2.1
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    have hx : perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n x ∈
        (perfectSupportedKMap (j ⁻¹ᵁ T).ι n).ker :=
      he ▸ (show perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n x ∈
        (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n).range from ⟨x,rfl⟩)
    change resK(j, n) (perfectSupportedKMap T.ι n _) = 1
    rw [← hs']
    change perfectSupportedKMap (j ⁻¹ᵁ T).ι n
      ((perfectSupportedExcisionKEquiv j T hcover n)
        ((perfectSupportedExcisionKEquiv j T hcover n).symm
          (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n x))) = 1
    rw [MulEquiv.apply_symm_apply]
    exact hx
  · intro ha
    have hm : perfectSupportedKRestrict j T n a ∈
        (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n).range := by
      rw [he]
      change perfectSupportedKMap (j ⁻¹ᵁ T).ι n (perfectSupportedKRestrict j T n a) = 1
      rw [hs']
      exact ha
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, ?_⟩
    change (perfectSupportedExcisionKEquiv j T hcover n).symm
      (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n x) = a
    rw [hx]
    exact (perfectSupportedExcisionKEquiv j T hcover n).symm_apply_apply a

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T.toScheme] in
include hcover in
/-- The common support image is the lower restriction kernel, because its
actual excision comparison is surjective even in degree zero. -/
lemma range_restrict_comp_support (n : ℕ) :
    ((resK(j, n)).comp (perfectSupportedKMap T.ι n)).range =
      (resK((j ⁻¹ᵁ T).ι, n)).ker := by
  rw [← perfectSupportedKRestrict_comp_forget]
  rw [← (perfectQcqs_positiveLongExactSequence (j ⁻¹ᵁ T).ι n).2.2]
  ext d
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨perfectSupportedKRestrict j T n a,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,hb⟩ := (perfectSupportedExcisionKEquiv j T hcover n).surjective a
    exact ⟨b, congrArg (perfectSupportedKMap (j ⁻¹ᵁ T).ι n) hb⟩

/-- Exactness at original K(X) in every connective degree, including zero. -/
lemma range_connectingHom_eq_ker_restrictionPair (n : ℕ) :
    (connectingHom j T hcover n).range = (restrictionPair j T n).ker :=
  GroupMayerVietoris.range_boundary_eq_ker_pair _ _ _ _
    ((perfectQcqs_positiveLongExactSequence T.ι n).2.2)
    (range_lowerBoundary j T hcover n)

/-- The normalized lower boundary is compatible with the entire original
upper localization boundary, including the boundary into supported K-zero. -/
lemma lowerBoundary_comp_overlap (n : ℕ) :
    (lowerBoundary j T hcover n).comp
        (resK((j.resLE T (j ⁻¹ᵁ T) le_rfl), (n+1))) =
      perfectQcqsConnectingHom T.ι n := by
  have h := @perfectQcqsConnectingHom_pullback _ _
    (inferInstanceAs (QuasiSeparatedSpace V)) (inferInstanceAs (QuasiSeparatedSpace X))
    (inferInstanceAs (CompactSpace (j ⁻¹ᵁ T).toScheme))
    (inferInstanceAs (CompactSpace T.toScheme)) inferInstance inferInstance
    (qcSupportRestrictionPair j T) n
  change (perfectSupportedKPullback (qcSupportRestrictionPair j T) n).comp
      (perfectQcqsConnectingHom T.ι n) =
    (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n).comp
      (perfectKPullback (j.resLE T (j ⁻¹ᵁ T) le_rfl) (n+1)) at h
  rw [← perfectSupportedKRestrict_eq_pullback, perfectKPullback_eq_restrict] at h
  ext x
  have hx : perfectSupportedKRestrict j T n (perfectQcqsConnectingHom T.ι n x) =
      perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n
        (resK((j.resLE T (j ⁻¹ᵁ T) le_rfl), (n+1)) x) :=
    DFunLike.congr_fun h x
  apply (perfectSupportedExcisionKEquiv j T hcover n).injective
  change (perfectSupportedExcisionKEquiv j T hcover n)
    ((perfectSupportedExcisionKEquiv j T hcover n).symm
      (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n
        (resK((j.resLE T (j ⁻¹ᵁ T) le_rfl), (n+1)) x))) =
    perfectSupportedKRestrict j T n (perfectQcqsConnectingHom T.ι n x)
  rw [MulEquiv.apply_symm_apply]
  exact hx.symm

/-- Exactness at the positive original overlap group. -/
lemma range_overlapDifference_eq_ker_connectingHom (n : ℕ) :
    (overlapDifference j T (n+1)).range = (connectingHom j T hcover n).ker :=
  GroupMayerVietoris.range_difference_eq_ker_boundary _ _ _ _ _
    ((perfectQcqs_positiveLongExactSequence T.ι n).2.1)
    (by
      rw [(perfectQcqs_positiveLongExactSequence (j ⁻¹ᵁ T).ι n).1]
      ext x
      change perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n x = 1 ↔
        (perfectSupportedExcisionKEquiv j T hcover n).symm
          (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n x) = 1
      exact ((perfectSupportedExcisionKEquiv j T hcover n).symm.map_eq_one_iff).symm)
    (lowerBoundary_comp_overlap j T hcover n)

include hcover in
/-- Exactness at the pair of positive original local groups. This theorem
requires n+1 and asserts no final-pair degree-zero gluing statement. -/
lemma range_restrictionPair_eq_ker_overlapDifference (n : ℕ) :
    (restrictionPair j T (n+1)).range = (overlapDifference j T (n+1)).ker :=
  GroupMayerVietoris.range_pair_eq_ker_difference _ _ _ _ _ _ _
    ((perfectQcqs_positiveLongExactSequence T.ι (n + 1)).2.2)
    (range_restrict_comp_support j T hcover (n+1))
    ((perfectQcqs_positiveLongExactSequence T.ι n).1)
    (by
      rw [(perfectQcqs_positiveLongExactSequence (j ⁻¹ᵁ T).ι n).1]
      ext x
      change perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n x = 1 ↔
        (perfectSupportedExcisionKEquiv j T hcover n).symm
          (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n x) = 1
      exact ((perfectSupportedExcisionKEquiv j T hcover n).symm.map_eq_one_iff).symm)
    (restriction_square j T (n+1)) (lowerBoundary_comp_overlap j T hcover n)


end AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris
