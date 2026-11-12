/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.DifferenceSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation

/-!
# The specified trivialization of a divisor difference away from its support

An empty inverse-image divisor has the unit ideal `⊤`, not the zero ideal. Pulling back
`𝒪(D) ⊗ 𝒪(-E)` and identifying both inverse images with this empty divisor gives a specified
trivialization by the native evaluation pairing. No reduction of the source scheme occurs.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- Avoiding every point of the support makes the full inverse-image ideal the unit ideal. -/
theorem comap_eq_top_of_avoids_support {X Y : Scheme.{u}} (i : X ⟶ Y)
    (D : Y.IdealSheafData) (h : ∀ x : X, i x ∉ D.support) : D.comap i = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
  ext x
  exact iff_of_false (h x) (by simp)

/-- The difference sheaf of two empty divisors is canonically trivial by evaluation. -/
def differenceSheafTopIso (X : Scheme.{u}) :
    differenceSheaf (⊤ : X.IdealSheafData) ⊤ ≅ SheafOfModules.unit X.ringCatSheaf := by
  letI := isEffectiveCartierDivisor_top (X := X)
  letI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (negativeTwist' (⊤ : X.IdealSheafData)) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (isEffectiveCartierDivisor_top (X := X))
  exact Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' (⊤ : X.IdealSheafData))

/-- The boundary trivialization uses the native pullback comparison and the evaluation
pairing for the empty divisor, with both inverse-image ideals identified on the full scheme. -/
def differenceSheafBoundaryIsoOfComapEqTop {X Y : Scheme.{u}} (i : X ⟶ Y)
    (D E : Y.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    (hD : D.comap i = ⊤) (hE : E.comap i = ⊤) :
    (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : IsPullbackDefined i D := by
    change IsEffectiveCartierDivisor (D.comap i)
    rw [hD]
    exact isEffectiveCartierDivisor_top
  letI : IsPullbackDefined i E := by
    change IsEffectiveCartierDivisor (E.comap i)
    rw [hE]
    exact isEffectiveCartierDivisor_top
  exact differenceSheafPullbackIso i D E ≪≫
    eqToIso (congrArg₂ differenceSheaf hD hE) ≪≫ differenceSheafTopIso X

/-- A morphism avoiding both divisor supports has a specified boundary trivialization.
The morphism is arbitrary and its source need not be reduced, flat or finite. -/
def differenceSheafBoundaryIso {X Y : Scheme.{u}} (i : X ⟶ Y)
    (D E : Y.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
    (hD : ∀ x : X, i x ∉ D.support) (hE : ∀ x : X, i x ∉ E.support) :
    (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  differenceSheafBoundaryIsoOfComapEqTop i D E
    (comap_eq_top_of_avoids_support i D hD) (comap_eq_top_of_avoids_support i E hE)

/-- Disjointness from the image of a closed immersion removes its kernel divisor on the
entire source scheme, not just on the reduced source. -/
theorem comap_ker_eq_top_of_disjoint_range {X Y Z : Scheme.{u}}
    (i : X ⟶ Y) (s : Z ⟶ Y) [IsClosedImmersion s]
    (h : Disjoint (Set.range i) (Set.range s)) : s.ker.comap i = ⊤ := by
  apply comap_eq_top_of_avoids_support i s.ker
  intro x hx
  change i x ∈ (s.ker.support : Set Y) at hx
  rw [Scheme.Hom.support_ker] at hx
  rw [s.isClosedEmbedding.isClosed_range.closure_eq] at hx
  exact Set.disjoint_left.1 h ⟨x, rfl⟩ hx

/-- In particular, a boundary disjoint from two closed section images has a specified
trivialization of their literal kernel-divisor difference. Cartierness belongs to the two
kernel ideals; no flatness or reducedness is imposed on the boundary. -/
def differenceSheafBoundaryIsoOfDisjointRange {X Y Z W : Scheme.{u}}
    (i : X ⟶ Y) (s : Z ⟶ Y) (t : W ⟶ Y)
    [IsClosedImmersion s] [IsClosedImmersion t]
    [IsEffectiveCartierDivisor s.ker] [IsEffectiveCartierDivisor t.ker]
    (hs : Disjoint (Set.range i) (Set.range s))
    (ht : Disjoint (Set.range i) (Set.range t)) :
    (Scheme.Modules.pullback i).obj (differenceSheaf s.ker t.ker) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  differenceSheafBoundaryIsoOfComapEqTop i s.ker t.ker
    (comap_ker_eq_top_of_disjoint_range i s hs) (comap_ker_eq_top_of_disjoint_range i t ht)

end Stacks.Divisors
