/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietoris
public import Colib.AlgebraicGeometry.KTheory.OpenDerivedImageCoverReflection
public import Colib.Util.References

/-! # Exactness at the pair of local K-zero groups

The two actual restriction images reflect membership by derived gluing. This
gives the missing degree-zero exact position without asserting surjectivity
onto the intersection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris

universe u

variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens) [CompactSpace T.toScheme]
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

attribute [local instance] HasDerivedCategory.standard

local notation "I₀" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "W" => Scheme.Opens.toScheme I₀

variable [QuasiSeparatedSpace V]
local instance mvZeroOverlapCompact : CompactSpace W :=
  isCompact_iff_compactSpace.mp (j.isCompact_preimage
    (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T.toScheme))))

local instance mvZeroKCommGroup (S : Scheme.{u}) (n : ℕ) : CommGroup (perfectK S n) :=
  Additivity.KCommGroup (RingedSpace.perfectComplexesWaldhausen S.toRingedSpace) n

include hcover in
/-- The literal restriction pair is exact at the pair of local degree-zero groups. -/
theorem range_restrictionPair_eq_ker_overlapDifference_zero :
    (restrictionPair j T 0).range = (overlapDifference j T 0).ker :=
  GroupMayerVietoris.range_pair_eq_ker_difference_of_image_reflection _ _ _ _ _
    ((perfectQcqs_positiveLongExactSequence T.ι 0).2.2)
    (range_restrict_comp_support j T hcover 0)
    (restriction_square j T 0)
    (fun x hx => (OpenDerivedImage.restrict_mem_range_iff_of_cover j T hcover x).mp hx)

include hcover in
/-- All three exact positions of the five-term two-open row, for every connective degree. -/
@[colib_tag "COL-1293",
  colib_ref "ThomasonTrobaugh1990" "Theorem 8.1 and (8.1.2), p. 367"
    "specialization" "Ordinary two-open exact sequence in the displayed connective degrees"]
theorem fiveTerm_exact (n : ℕ) :
    Function.MulExact (overlapDifference j T (n + 1)) (connectingHom j T hcover n) ∧
      Function.MulExact (connectingHom j T hcover n) (restrictionPair j T n) ∧
      Function.MulExact (restrictionPair j T n) (overlapDifference j T n) := by
  refine ⟨MonoidHom.mulExact_iff.mpr
    (range_overlapDifference_eq_ker_connectingHom j T hcover n).symm,
    MonoidHom.mulExact_iff.mpr (range_connectingHom_eq_ker_restrictionPair j T hcover n).symm,
    ?_⟩
  cases n with
  | zero =>
    exact MonoidHom.mulExact_iff.mpr
      (range_restrictionPair_eq_ker_overlapDifference_zero j T hcover).symm
  | succ n =>
    exact MonoidHom.mulExact_iff.mpr
      (range_restrictionPair_eq_ker_overlapDifference j T hcover n).symm

end AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris
