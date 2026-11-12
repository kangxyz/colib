/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Basic
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1Coefficient
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.EdgeWindow

/-! # The original HI projection: finite Leray consumers without a coefficient-iso premise -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/FiniteField/LerayHI.lean`, blob
`5619a231e4812342755560ca8b337d35ef1d5fef`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction (affineLineCylinder projection)
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)

local notation "π" => CategoryTheory.NatTrans.app
  (projection (SmoothSite.additiveGroupObject (Spec (CommRingCat.of k)))) X

/-- Original transfer HI proves the actual degree-zero direct-image coefficient isomorphism. -/
theorem a1_coefficient_isIso (hF : F.obj.IsA1Invariant) :
    IsIso (Scheme.EtaleSeparatedFiniteType.restrictionToDirectImage ((toSheaf k).obj F)
      π) :=
  Scheme.EtaleSeparatedFiniteType.a1RestrictionCoefficient_isIso (.of k) X ((toSheaf k).obj F) hF

variable [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf
    (Scheme.EtaleSeparatedFiniteType.nisnevichTopology (affineLineCylinder.obj X).left)
      AddCommGrpCat.{u + 1})]

/-- Original HI gives projection bijectivity under the actual finite higher-image window. -/
theorem a1_projection_bijective_of_rightDerived_window (hF : F.obj.IsA1Invariant) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N →
      IsZero (((Scheme.EtaleSeparatedFiniteType.directImage (π).left).rightDerived q).obj
        ((Scheme.EtaleSeparatedFiniteType.restrict (affineLineCylinder.obj X)
            AddCommGrpCat.{u + 1}).obj
          ((toSheaf k).obj F)))) :
    Function.Bijective (A1.projectionPullback (.of k)
      (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) N) X) := by
  let := a1_coefficient_isIso X F hF
  exact Scheme.EtaleSeparatedFiniteType.originalRestriction_bijective_of_rightDerived_window
    π ((toSheaf k).obj F) N hR

/-- The endpoint-free higher-image window gives injectivity of the same original projection. -/
theorem a1_projection_injective_of_rightDerived_window (hF : F.obj.IsA1Invariant) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q < N →
      IsZero (((Scheme.EtaleSeparatedFiniteType.directImage (π).left).rightDerived q).obj
        ((Scheme.EtaleSeparatedFiniteType.restrict (affineLineCylinder.obj X)
            AddCommGrpCat.{u + 1}).obj
          ((toSheaf k).obj F)))) :
    Function.Injective (A1.projectionPullback (.of k)
      (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) N) X) := by
  let := a1_coefficient_isIso X F hF
  exact Scheme.EtaleSeparatedFiniteType.originalRestriction_injective_of_rightDerived_window
    π ((toSheaf k).obj F) N hR

end AlgebraicGeometry.SheafWithTransfers
