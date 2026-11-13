/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.Induction
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.PunctureMono
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.Cylinder.HigherGenericBaseZero

/-!
# Strict A¹-invariance from degree-one generic vanishing and boundary epimorphy

The rank-zero input in higher degrees comes from the original smooth
cylinder. The degree-one input and the canonical boundary epimorphism
supply the remaining hypotheses of the native rank and degree induction.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The two geometric suppliers close strict A¹-invariance over a
perfect field. Both hypotheses concern the original ordinary cohomology. -/
theorem isStrictA1Invariant_of_degreeOne_generic_and_boundary_epi
    (hEpi : Boundary.OriginalPresheaf.CanonicalBoundaryEpi k)
    (h₁ : ∀ (G : SheafWithTransfers.{u + 1} k), G.obj.IsA1Invariant →
      WholeCylinderGenericOpenZero G 1)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    F.IsStrictA1Invariant := by
  refine isStrictA1Invariant_of_cartier_puncture_mono ?_
    (smoothCartierPunctureRestrictionMono_of_boundary_epi hEpi) F hF
  intro G hG n
  cases n with
  | zero => exact h₁ G hG
  | succ n =>
    dsimp only [WholeCylinderGenericOpenZero]
    intro Y _ _ s
    obtain ⟨V, _, hη, hz⟩ := SheafCohomology.exists_generic_base_cylinder_h_add_two_zero
      ((toSheaf k).obj G) n Y s
    exact ⟨V, hη, hz⟩

end AlgebraicGeometry.SheafWithTransfers
