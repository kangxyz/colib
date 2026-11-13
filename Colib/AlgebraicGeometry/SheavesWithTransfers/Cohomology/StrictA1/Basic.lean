/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

/-!
# Strict A¹-invariance for ordinary Nisnevich cohomology

Strict A¹-invariance tests the actual native affine-line projection in every
nonnegative degree of Stacks' existing ordinary Ext cohomology presheaf.
The polynomial-spectrum comparison retains the original projection map.
This defines the target predicate, not Voevodsky's strict A¹-invariance theorem.

Adapted from `Motivic/Cohomology/A1/Basic.lean:156-167` at
motivic@a6805c4a87cdfd7717dd7a94039246a167f15380, blob
`b2bd41fcf3b449c6e0a2b11a66429287eeab9e40`.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.Cohomology.FreeYonedaUnivLE
universe w u

namespace AlgebraicGeometry.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1})]

/-- Strict HI tests every ordinary Nisnevich cohomology degree on actual projections. -/
def IsStrictA1Invariant (F : SheafWithTransfers.{u + 1} k) : Prop :=
  ∀ n : ℕ, A1.IsInvariant (.of k)
    (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) n)

/-- Expanding strict A¹-invariance retains the actual ordinary projection map. -/
theorem isStrictA1Invariant_iff (F : SheafWithTransfers.{u + 1} k) :
    IsStrictA1Invariant F ↔ ∀ (n : ℕ) (X : SmoothSite (Spec (.of k))),
      IsIso ((cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) n).map
        ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op) := Iff.rfl

/-- Strict A¹-invariance can be tested on the original polynomial projection. -/
theorem isStrictA1Invariant_iff_polynomial_projection (F : SheafWithTransfers.{u + 1} k) :
    IsStrictA1Invariant F ↔ ∀ (n : ℕ) (X : SmoothSite (Spec (.of k))),
      IsIso ((cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) n).map
        (SmoothSite.productFst X (polynomialAffineLine (.of k))).op) :=
  forall_congr' (fun n ↦ A1.isInvariant_iff_polynomial_projection (.of k)
    (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) n))

end AlgebraicGeometry.SheafWithTransfers
