/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionAllComponents
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionZerothHomotopy

/-!
# Components of the original projective telescope and Quillen K₀

The actual completion functor induces a bijection of all path components.
Composing that original map with the completion grading identifies the genuine
path components of the original projective telescope with the existing
Grothendieck group and the unchanged homotopical Quillen K₀. The original vertex
at stage `n` with numerator `P` has exactly class `[P] - [rankOnePower n]`.
No numerical rank, invariant-basis-number, commutativity, stable-freeness, or
product-decomposition premise is used.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveTelescopeKZero.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory MonoidalCategory

namespace ModuleCat.FiniteProjective.StableFreeRight

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal

variable (R : Type u) [Ring R]

/-- The original telescope component maps bijectively to its actual virtual projective class. -/
def telescopeZerothHomotopyGrothendieckEquiv :
    ZerothHomotopy (ClassifyingSpace (ProjectiveTelescope R)) ≃
      (exactStructure Rᵐᵒᵖ).GrothendieckGroup :=
  (completionMapComponentsEquiv R).trans (completionPiZeroGrothendieckEquiv Rᵐᵒᵖ)

/-- The actual original telescope path components identify with unchanged homotopical Quillen K₀. -/
def telescopeZerothHomotopyKZeroEquiv :
    ZerothHomotopy (ClassifyingSpace (ProjectiveTelescope R)) ≃ (exactStructure Rᵐᵒᵖ).K 0 :=
  (completionMapComponentsEquiv R).trans (completionZerothHomotopyKZeroEquiv Rᵐᵒᵖ)

/-- The forward grading passes through exactly the original continuous completion map. -/
theorem telescopeZerothHomotopyGrothendieckEquiv_mk
    (x : ClassifyingSpace (ProjectiveTelescope R)) :
    telescopeZerothHomotopyGrothendieckEquiv R (ZerothHomotopy.mk x) =
      completionPiZeroGrothendieckEquiv Rᵐᵒᵖ
        (ZerothHomotopy.mk (classifyingSpaceMapUniversal (completionFunctor R) x)) := rfl

/-- The homotopical K₀ equivalence likewise retains the original continuous map at every point. -/
theorem telescopeZerothHomotopyKZeroEquiv_mk (x : ClassifyingSpace (ProjectiveTelescope R)) :
    telescopeZerothHomotopyKZeroEquiv R (ZerothHomotopy.mk x) =
      completionZerothHomotopyKZeroEquiv Rᵐᵒᵖ
        (ZerothHomotopy.mk (classifyingSpaceMapUniversal (completionFunctor R) x)) := rfl

/-- Every original telescope stage has numerator minus its actual rank-one-power denominator. -/
@[simp] theorem telescopeZerothHomotopyGrothendieckEquiv_stage
    (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    telescopeZerothHomotopyGrothendieckEquiv R
      (ZerothHomotopy.mk
        (classifyingSpacePoint (⟨n, AsSmall.up.obj P⟩ : ProjectiveTelescope R))) =
      (exactStructure Rᵐᵒᵖ).grothendieckClass P.of -
        (exactStructure Rᵐᵒᵖ).grothendieckClass (rankOnePower Rᵐᵒᵖ n).of := by
  rw [telescopeZerothHomotopyGrothendieckEquiv_mk, classifyingSpaceMapUniversal_point,
    completionFunctor_obj]
  exact completionPiZeroGrothendieckEquiv_pair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) P

/-- The K₀ endpoint is the original classical-to-homotopical comparison of the same class. -/
theorem telescopeZerothHomotopyKZeroEquiv_eq
    (a : ZerothHomotopy (ClassifyingSpace (ProjectiveTelescope R))) :
    telescopeZerothHomotopyKZeroEquiv R a =
      (exactStructure Rᵐᵒᵖ).grothendieckToKZero
        (Multiplicative.ofAdd (telescopeZerothHomotopyGrothendieckEquiv R a)) := rfl

/-- The original stage formula holds in the unchanged homotopical Quillen K₀ as well. -/
theorem telescopeZerothHomotopyKZeroEquiv_stage (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    telescopeZerothHomotopyKZeroEquiv R
      (ZerothHomotopy.mk
        (classifyingSpacePoint (⟨n, AsSmall.up.obj P⟩ : ProjectiveTelescope R))) =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of := by
  rw [telescopeZerothHomotopyKZeroEquiv_mk, classifyingSpaceMapUniversal_point,
    completionFunctor_obj]
  exact completionZerothHomotopyKZeroEquiv_pair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) P

/-- Every existing Grothendieck class has an original finite-stage telescope representative. -/
theorem exists_telescope_stage_grothendieckClass (a : (exactStructure Rᵐᵒᵖ).GrothendieckGroup) :
    ∃ (n : ℕ) (P : IsoCategory Rᵐᵒᵖ),
      (exactStructure Rᵐᵒᵖ).grothendieckClass P.of -
        (exactStructure Rᵐᵒᵖ).grothendieckClass (rankOnePower Rᵐᵒᵖ n).of = a := by
  obtain ⟨b, hb⟩ := (telescopeZerothHomotopyGrothendieckEquiv R).surjective a
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective b
  obtain ⟨⟨n, ⟨P⟩⟩, hp⟩ := classifyingSpace_joined_vertex x
  have he := ZerothHomotopy.sound hp.somePath
  rw [← he] at hb
  exact ⟨n, P, (telescopeZerothHomotopyGrothendieckEquiv_stage R n P).symm.trans hb⟩

/-- Equality of virtual stage classes is exactly an actual path in the original telescope. -/
theorem telescope_stage_joined_iff_grade_eq (n m : ℕ) (P Q : IsoCategory Rᵐᵒᵖ) :
    Joined (classifyingSpacePoint (⟨n, AsSmall.up.obj P⟩ : ProjectiveTelescope R))
      (classifyingSpacePoint (⟨m, AsSmall.up.obj Q⟩ : ProjectiveTelescope R)) ↔
    (exactStructure Rᵐᵒᵖ).grothendieckClass P.of -
        (exactStructure Rᵐᵒᵖ).grothendieckClass (rankOnePower Rᵐᵒᵖ n).of =
      (exactStructure Rᵐᵒᵖ).grothendieckClass Q.of -
        (exactStructure Rᵐᵒᵖ).grothendieckClass (rankOnePower Rᵐᵒᵖ m).of := by
  rw [← telescopeZerothHomotopyGrothendieckEquiv_stage R n P,
    ← telescopeZerothHomotopyGrothendieckEquiv_stage R m Q,
    (telescopeZerothHomotopyGrothendieckEquiv R).injective.eq_iff]
  exact ⟨fun h ↦ Quotient.sound h, fun h ↦ Quotient.exact h⟩

end ModuleCat.FiniteProjective.StableFreeRight
