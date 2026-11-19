/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.Coefficients
public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.OpenNaturality
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Open restriction under ordinary Nisnevich purity -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE
open SmoothSite

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

local notation "Nis" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))

/-- Use the canonical sheafification on the correspondence site. -/
local instance openSupportCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The ordinary purity comparison uses the canonical additive sheafification. -/
local instance openSupportHasSheafify : HasSheafify Nis AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1} Nis

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option maxHeartbeats 650000 in
-- Infer the purity square before specializing the relative-cohomology comparison.
/-- Restriction to an open subscheme commutes with purity and restriction on the centre. -/
theorem supportCohomologyPurityEquiv_precomp_of_isOpenImmersion
    {Z X Z' X' : SmoothSite (Spec (.of k))} (i : Z ⟶ X) [IsClosedImmersion i.left] {a b : ℕ}
    (hX : RelativeDimension X.hom a) (hZ : RelativeDimension Z.hom b)
    (j : Z' ⟶ X') [IsClosedImmersion j.left]
    (hX' : RelativeDimension X'.hom a) (hZ' : RelativeDimension Z'.hom b)
    {f : X ⟶ X'} [IsOpenImmersion f.left] {g : Z ⟶ Z'}
    (h : IsPullback i.left g.left f.left j.left)
    (F : LargeSheaves k) (hF : F.obj.IsA1Invariant) (n : ℕ) (hn : a - b ≤ n)
    (x : relativeH.{u + 1, u + 1} Nis (closedPairOpenInclusion j.left) ((toSheaf k).obj F) n) :
    supportCohomologyPurityEquiv k i hX hZ F hF n hn
        (((relativeCohomologyFunctor.{u + 1, u + 1} Nis n).obj ((toSheaf k).obj F)).map
          (closedSupportArrowMap h).op x) =
      (cohomologyPresheaf.{u + 1, u + 1}
          ((toSheaf k).obj (iteratedHIContraction k (a - b) F hF).1) (n - (a - b))).map g.op
        (supportCohomologyPurityEquiv k j hX' hZ' F hF n hn x) := by
  have hPurity := effectivePurity_naturality_of_isOpenImmersion k
    (i := i) (j := j) (f := f) (g := g) h hX hZ hX' hZ'
  have hRestriction := supportCohomologyPurityEquiv_precomp k i hX hZ j hX' hZ'
    (f := f) (g := g) h hPurity F hF n hn x
  exact hRestriction

end AlgebraicGeometry.MotivicHomotopy
