/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.SupportedMayerVietorisBoundary
public import Colib.Util.References

/-! # Two-open Mayer–Vietoris with prescribed auxiliary support -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.SupportedMayerVietoris

universe u

variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  [QuasiSeparatedSpace V] (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
  (hZ : IsCompact (Z : Set X)) [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]

local notation "I₀" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "Z'" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) Z
local notation "i" => Scheme.Opens.ι T
local notation "b" => Scheme.Opens.ι I₀
local notation "hX" => IsCompact.union (isCompact_range (Scheme.Hom.continuous i)) hZ
local notation "hV" =>
  IsCompact.union (isCompact_range (Scheme.Hom.continuous b))
    (Scheme.Hom.isCompact_preimage j hZ)
local notation:max "u[" n "]" => KMap (SupportedOpenDerivedImage.overlapRestrict_exact j T Z) n
local notation:max "f[" n "]" => perfectSupportedKRestrict i Z n
local notation:max "g[" n "]" => perfectSupportedKRestrict j Z n
local notation:max "v[" n "]" => perfectSupportedKRestrict b Z' n
local notation:max "p[" n "]" => perfectSupportedConnectingHomOfUnionCompact i Z hX n
local notation:max "d[" n "]" => perfectSupportedConnectingHomOfUnionCompact b Z' hV n
local notation:max "q[" n "]" => lowerBoundary j T Z hcover hZ n
local notation:max "l[" n "]" => perfectSupportedUnionKMap i Z n
local notation:max "l'[" n "]" => perfectSupportedUnionKMap b Z' n

local instance supportedMayerVietorisExactKCommGroup {A B : Scheme.{u}} (k : A ⟶ B)
    [IsOpenImmersion k] (n : ℕ) : CommGroup (PerfectSupportedK k n) :=
  Additivity.KCommGroup (perfectSupportedWaldhausen k) n

include hZ hcover in
omit [CompactSpace X] [CompactSpace T.toScheme] in
/-- Excision identifies the common-support image with the kernel on the second open. -/
theorem range_restrict_comp_union (n : ℕ) :
    ((g[n]).comp (l[n])).range = (v[n]).ker := by
  rw [← fiberEquiv_comp_union j T Z hcover, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (fiberEquiv j T Z hcover n).surjective, Subgroup.map_top]
  exact (perfectSupported_positiveLongExactSequence_of_union_compact b Z' hV n).2.2

omit [CompactSpace X] [CompactSpace T.toScheme] in
/-- The transported common-support boundary has exactly the original image. -/
theorem range_lowerBoundary (n : ℕ) :
    (q[n]).range = ((g[n]).comp (l[n])).ker := by
  rw [← fiberEquiv_comp_union j T Z hcover]
  refine Subgroup.ext fun x => ?_
  have he := (perfectSupported_positiveLongExactSequence_of_union_compact b
    Z' hV n).2.1
  constructor
  · rintro ⟨a, rfl⟩
    have ha : d[n] a ∈ (d[n]).range := ⟨a, rfl⟩
    rw [he] at ha
    change l'[n] ((fiberEquiv j T Z hcover n)
      ((fiberEquiv j T Z hcover n).symm (d[n] a))) = 1
    rwa [MulEquiv.apply_symm_apply]
  · intro hx
    have hx' : (fiberEquiv j T Z hcover n) x ∈ (l'[n]).ker := hx
    rw [← he] at hx'
    obtain ⟨a, ha⟩ := hx'
    exact ⟨a, (congrArg (fiberEquiv j T Z hcover n).symm ha).trans
      (MulEquiv.symm_apply_apply _ _)⟩

omit [CompactSpace X] [CompactSpace T.toScheme] in
/-- The transported boundary keeps the original positive-degree restriction kernel. -/
theorem range_lower_restrict (n : ℕ) :
    (v[n + 1]).range = (q[n]).ker := by
  rw [(perfectSupported_positiveLongExactSequence_of_union_compact b
    Z' hV n).1]
  refine Subgroup.ext fun x => ?_
  change d[n] x = 1 ↔ (fiberEquiv j T Z hcover n).symm (d[n] x) = 1
  exact ((fiberEquiv j T Z hcover n).symm.map_eq_one_iff).symm

/-- Compatibility of the actual upper and lower boundaries through the excision inverse. -/
theorem lowerBoundary_comp_overlap (n : ℕ) :
    (q[n]).comp (u[n + 1]) = p[n] := by
  refine MonoidHom.ext fun x => ?_
  apply (fiberEquiv j T Z hcover n).injective
  change (fiberEquiv j T Z hcover n) ((fiberEquiv j T Z hcover n).symm
    (d[n] (u[n + 1] x))) = (fiberEquiv j T Z hcover n) (p[n] x)
  rw [MulEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (fineConnecting_natural j T Z hZ n) x
  exact h.symm.trans (DFunLike.congr_fun (fiberEquiv_toMonoidHom j T Z hcover n).symm
    (p[n] x))

include hZ in
/-- The two supported localization rows yield all three exact positions, including degree zero. -/
@[colib_tag "COL-1293",
  colib_ref "ThomasonTrobaugh1990" "Theorem 8.1 and (8.1.2), p. 367"
    "specialization" "Two-open exact sequence with prescribed support in connective degrees"]
theorem fiveTerm_exact (n : ℕ) :
    Function.MulExact (overlapDifference j T Z (n + 1)) (connectingHom j T Z hcover hZ n) ∧
      Function.MulExact (connectingHom j T Z hcover hZ n) (restrictionPair j T Z n) ∧
      Function.MulExact (restrictionPair j T Z n) (overlapDifference j T Z n) := by
  have h := perfectSupported_positiveLongExactSequence_of_union_compact i Z hX n
  refine ⟨MonoidHom.mulExact_iff.mpr
    (GroupMayerVietoris.range_difference_eq_ker_boundary _ _ _ _ _ h.2.1
      (range_lower_restrict j T Z hcover hZ n)
      (lowerBoundary_comp_overlap j T Z hcover hZ n)).symm,
    MonoidHom.mulExact_iff.mpr
      (GroupMayerVietoris.range_boundary_eq_ker_pair _ _ _ _ h.2.2
        (range_lowerBoundary j T Z hcover hZ n)).symm, ?_⟩
  apply MonoidHom.mulExact_iff.mpr
  cases n with
  | zero =>
    exact (GroupMayerVietoris.range_pair_eq_ker_difference_of_image_reflection _ _ _ _ _
      h.2.2 (range_restrict_comp_union j T Z hcover hZ 0)
      (restriction_square j T Z 0)
      (fun x hx => (SupportedOpenDerivedImage.restrict_mem_range_iff_of_cover
        j T Z hZ hcover x).mp hx)).symm
  | succ n =>
    exact (GroupMayerVietoris.range_pair_eq_ker_difference _ _ _ _ _ _ _
      (perfectSupported_positiveLongExactSequence_of_union_compact i Z hX (n + 1)).2.2
      (range_restrict_comp_union j T Z hcover hZ (n + 1))
      (perfectSupported_positiveLongExactSequence_of_union_compact i Z hX n).1
      (range_lower_restrict j T Z hcover hZ n)
      (restriction_square j T Z (n + 1))
      (lowerBoundary_comp_overlap j T Z hcover hZ n)).symm

end AlgebraicGeometry.Scheme.Modules.SupportedMayerVietoris
