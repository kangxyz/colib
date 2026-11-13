/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Stalk.Dimension.SmoothFiniteRank
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.DegreeZero
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.MarkedLerayWindow
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.TransferInvariance
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.RankZeroColimit
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Puncture.CartierReduction

/-! # Local rank and degree induction for ordinary affine-line projections

Vanishing on whole cylinders over generic base opens starts the induction on
local rank. Cartier puncture monicity gives the positive-rank step. The finite
Leray window then closes the outer induction simultaneously for every homotopy
invariant sheaf with transfers.

Adapted from Motivic revision `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/StrictInvariance/DegreeInduction.lean`
(blob `4682a11fc6e866da5214677f7c98a9646226d008`) and
`Motivic/Cohomology/A1/LocalVanishing/RankZero/Vanishing.lean`
(blob `d9db1338ed4091236f54b83f11a3835bbb329820`).
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Each cylinder class restricts to zero on the whole cylinder over a base
open containing the generic point of the original integral affine scheme. -/
def WholeCylinderGenericOpenZero (F : SheafWithTransfers.{u + 1} k) (n : ℕ) : Prop :=
  ∀ (Y : SmoothSite (Spec (.of k))) [IsAffine Y.left] [IsIntegral Y.left],
    let P := cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) n
    ∀ s : P.obj (op (SmoothSite.Contraction.affineLineCylinder.obj Y)),
      ∃ O : Y.left.Opens, genericPoint Y.left ∈ O ∧
        P.map (SmoothSite.Contraction.affineLineCylinder.map
          (SmoothSite.openInclusion Y O)).op s = 0

variable [PerfectField k]

/-- The residue cylinder germ vanishes by strong induction on the dimension of
the actual smooth stalk. The lower-rank hypothesis runs over all smooth objects. -/
theorem residueCylinderColimit_isZero_of_cartier_puncture_mono
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (hGeneric : WholeCylinderGenericOpenZero F (n + 1))
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 → (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hMono : SmoothCartierPunctureRestrictionMono F (n + 1))
    (X : SmoothSite (Spec (.of k))) (x : X.left) :
    IsZero (colimit (pointedCylinderValues (.of k) (X := X) (residuePoint X.left x)
      (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (n + 1))
      (pointedBase (.of k) (X := X) (residuePoint X.left x)))) := by
  suffices h : ∀ d : ℕ, ∀ (Y : SmoothSite (Spec (.of k))) (y : Y.left),
      ringKrullDim (Y.left.presheaf.stalk y) = d →
      IsZero (colimit (pointedCylinderValues (.of k) (X := Y) (residuePoint Y.left y)
        (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (n + 1))
        (pointedBase (.of k) (X := Y) (residuePoint Y.left y)))) by
    obtain ⟨d, hd⟩ := Scheme.exists_nat_ringKrullDim_stalk_of_smooth X.hom x
    exact h d X x hd
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro Y y hd
    let K := Y.left.residueField y
    let b := Y.left.fromSpecResidueField y
    let p := IsLocalRing.closedPoint K
    have hp : b p = y := Y.left.fromSpecResidueField_apply y p
    have hd' : ringKrullDim (Y.left.presheaf.stalk (b p)) = d :=
      (congrArg (fun z : Y.left => ringKrullDim (Y.left.presheaf.stalk z)) hp).trans hd
    by_cases hzero : d = 0
    · have hrank : ringKrullDim (Y.left.presheaf.stalk (b p)) = 0 := by simpa [hzero] using hd'
      exact pointedCylinderColimit_isZero_of_rank_zero_generic_open_zero Y K b p
        (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (n + 1)) hrank hGeneric
    have hIH : LowerRankCylinderGermsZero F (n + 1) d := by
      intro V z hz
      obtain ⟨e, he⟩ := Scheme.exists_nat_ringKrullDim_stalk_of_smooth V.hom z
      change ringKrullDim (V.left.presheaf.stalk z) = e at he
      have hed : e < d := by
        rw [he] at hz
        exact_mod_cast hz
      exact ih e hed V z he
    exact pointedCylinderColimit_isZero_of_positive_rank_and_puncture_mono F hF n d hLow hIH
      hMono Y K b p hd' (Nat.pos_of_ne_zero hzero)

local instance (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- Whole-cylinder generic-open vanishing and the lower-degree construction of
Cartier puncture monicity imply strict A¹-invariance for every HI coefficient. -/
theorem isStrictA1Invariant_of_cartier_puncture_mono
    (hGeneric : ∀ (F : SheafWithTransfers.{u + 1} k), F.obj.IsA1Invariant →
      ∀ n : ℕ, WholeCylinderGenericOpenZero F (n + 1))
    (hMono : ∀ n : ℕ,
      (∀ (G : SheafWithTransfers.{u + 1} k), G.obj.IsA1Invariant →
        ∀ q : ℕ, 0 < q → q < n + 1 → (SheafCohomology.withTransfers k G q).IsA1Invariant) →
      ∀ (F : SheafWithTransfers.{u + 1} k), F.obj.IsA1Invariant →
        SmoothCartierPunctureRestrictionMono F (n + 1))
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    F.IsStrictA1Invariant := by
  suffices h : ∀ N : ℕ, ∀ (G : SheafWithTransfers.{u + 1} k), G.obj.IsA1Invariant →
      A1.IsInvariant (.of k)
        (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj G) N) by
    exact fun N => h N F hF
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro G hG
    cases N with
    | zero => exact degreeZero_isInvariant G hG
    | succ n =>
      intro X
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      apply a1_projection_bijective_of_marked_cylinder_window X G hG (n + 1)
      intro q hq hqN V z
      cases q with
      | zero => exact (Nat.lt_irrefl 0 hq).elim
      | succ m =>
        have hLow (H : SheafWithTransfers.{u + 1} k) (hH : H.obj.IsA1Invariant)
            (r : ℕ) (_hr : 0 < r) (hrm : r < m + 1) :
            (SheafCohomology.withTransfers k H r).IsA1Invariant :=
          (SheafCohomology.withTransfers_isA1Invariant_iff k H r).mpr
            (ih r (Nat.lt_of_lt_of_le hrm hqN) H hH)
        exact residueCylinderColimit_isZero_of_cartier_puncture_mono G hG m
          (hGeneric G hG m) (hLow G hG) (hMono m hLow G hG) ((toSmoothSite X).obj V) z

end AlgebraicGeometry.SheafWithTransfers
