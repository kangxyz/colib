/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.AtPrime
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.OpenComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Puncture.CartierTransport
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Puncture.LowerRankVanishing
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Injectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Cartier reduction of a positive-rank cylinder germ

The argument uses the chosen smooth Cartier neighborhood of the actual marked
point and its open complement. The comparison of marked cylinder diagrams
transports the resulting vanishing back to the original smooth object.

Adapted from Motivic revision `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/Cartier/PositiveRankReduction.lean`
(blob `6f60e34fd41ac2d8d84dea625a5bfe5bf5fa5268`) and
`Motivic/Cohomology/A1/StrictInvariance/DegreeInduction.lean`
(blob `4682a11fc6e866da5214677f7c98a9646226d008`).
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local instance (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- Given Cartier puncture monicity, lower-rank vanishing kills the marked
cylinder germ at a point of positive local rank. -/
theorem pointedCylinderColimit_isZero_of_positive_rank_and_puncture_mono [PerfectField k]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n d : ℕ)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hIH : LowerRankCylinderGermsZero F (n + 1) d)
    (hMono : SmoothCartierPunctureRestrictionMono F (n + 1))
    (X : SmoothSite (Spec (.of k))) (K : Type u) [Field K]
    (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = d) (hpos : 0 < d) :
    IsZero (colimit (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _))
      (cohomologyPresheaf.{u + 1, u + 1} ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
      (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _))))) := by
  have hpos' : 0 < ringKrullDim (X.left.presheaf.stalk (b p)) := by
    rw [hd]
    exact_mod_cast hpos
  obtain ⟨O, _hAffine, hO, Z, i, hi, hI, hs, hz⟩ :=
    Scheme.exists_smooth_cartier_neighborhood X.hom (b p) hpos'
  let : IsClosedImmersion i := hi
  let Y := (toSmoothSite X).obj (openObject O)
  let W : O.toScheme.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let j := SmoothSite.openInclusion Y W
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  let bO := openFieldPointLift K b p O hO
  have hbO : O.ι (bO p) = b p :=
    congrArg (fun f : Spec (.of K) ⟶ X.left => f p) (openFieldPointLift_ι K b p O hO)
  have hcenter : bO p ∈ Set.range i := by
    obtain ⟨z, hz⟩ := hz
    exact ⟨z, Subtype.ext (hz.trans hbO.symm)⟩
  have hW : Set.range i = (W : Set O.toScheme)ᶜ := (compl_compl (Set.range i)).symm
  have hmiss : bO p ∉ Set.range j.left := by
    change bO p ∉ Set.range W.ι
    rw [Scheme.Opens.range_ι]
    exact fun h => h hcenter
  let := hMono Y K bO p Z i hi hI hs hcenter W hW
  let : IsNoetherian X.left := SmoothSite.isNoetherian_left X
  let : IsNoetherianRing (X.left.presheaf.stalk (O.ι (bO p))) := inferInstance
  have hdO : ringKrullDim (Y.left.presheaf.stalk (bO p)) = d := by
    exact (_root_.AlgebraicGeometry.ringKrullDim_stalk_eq_of_etale O.ι (bO p)).trans
      ((congrArg (fun x : X.left => ringKrullDim (X.left.presheaf.stalk x)) hbO).trans hd)
  have hzero := projectionPointFiber_isZero_of_lowerRank j K bO p F hF n d
    hdO hmiss hLow hIH
  have hlocal := hzero.of_iso (pointedCylinderColimitFiberIso (.of k) Y
    (relativeFieldPoint bO K (𝟙 _)) ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
  exact hlocal.of_iso (openFieldPointCylinderColimitIso X K b p O hO _).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
