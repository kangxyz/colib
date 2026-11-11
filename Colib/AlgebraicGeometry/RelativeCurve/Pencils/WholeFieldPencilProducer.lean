/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.GeneratedWholeFieldDivisors
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.GeneratedWholeFieldIdeals
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.ConstantFamily

/-!
# Existence of the actual whole finite-flat correcting pencil over a field

Proper compactification, its ample coefficient, the whole polynomial marking,
and the genuine retained open produce all four sections and the entire finite
flat family. This lower geometric producer assumes no frame, section, family,
correspondence, homotopy, restriction-difference lifting, or boundary epimorphism.
The construction of the compactification/presentation itself is a separate input
producer and is not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable (k K : Type u) [Field k] [CommRing K] (z : k[X] →+* K)
  {C Y A B D : Scheme.{u}}
  (π : C ⟶ Spec (.of k)) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ Spec (.of k[X])) (hq : j ≫ π = p ≫ coordinateLineProjection k)
  (a : A ⟶ Spec (.of k[X])) (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
  (s : Spec (.of K) ⟶ Y) (hs : s ≫ p = coordinateMark k K z)
  (H : IsPullback s (𝟙 (Spec (.of K))) p (coordinateMark k K z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range (coordinateMark k K z)))

local notation "F" => divisorSheaf (compactificationGraph π j).ker
local notation "σ" => divisorSheafGlobalSection (compactificationGraph π j).ker
local notation "gA" => commonToLambda π j α
local notation "gN" => commonToPsi (coordinateLineProjection k) π j p hq a α β h
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "iN" => psiBoundaryInclusion (coordinateLineProjection k) π j p hq a
  (coordinateMark k K z) s hs d
local notation "i" => commonBoundaryInclusion π j α s d
local notation "qB" => commonProjection π j α

variable [IsProper π] [IsAffine Y] [IsAffine A] [IsAffine B]
  [IsOpenImmersion a] [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
  [IsFinite (d ≫ π)] [IsFinite (s ≫ j ≫ π)]
  (L : C.Modules) [IsInvertibleModule C L] (hL : IsAmple C L)
  {V : Scheme.{u}} [IsAffine V] (v : V ⟶ C) [IsOpenImmersion v]
  [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))

local notation "r" => retainedProductInclusion qB π v

/-- Produce the actual whole polynomial family and pole from original geometric
inputs. The four factor finite-flat divisors and exact start/end ideal products
are the accompanying theorems of the generated data. -/
theorem exists_wholeField_finiteFlatPencil :
    ∃ c : WholeFieldSectionData k K z π j p hq a s hs H d hd ha,
      letI := c.T_invertible
      letI := c.N_invertible
      let family := PolynomialSectionPencil.familySource qB (pullback.fst qB (v ≫ π))
        ((Modules.pullback r).obj (c.commonLine α β h))
        (pullbackGlobalSections r _ (c.commonStart α β h))
        (pullbackGlobalSections r _ (c.commonEnd α β h))
      let pole := (zeroScheme _ ((Modules.pullback r).obj (c.commonPoleLine α β h))
        (pullbackGlobalSections r _ (c.commonPole α β h))).subschemeι ≫
          pullback.fst qB (v ≫ π)
      (IsFinite family ∧ Flat family) ∧ (IsFinite pole ∧ Flat pole) := by
  obtain ⟨c⟩ := nonempty_wholeFieldSectionData k K z π j p hq a s hs H d hd ha L hL
  letI := c.T_invertible
  letI := c.N_invertible
  have hp := c.retainedPole_finite_relativeCartier α β h v hc
  exact ⟨c, c.retainedFamily_finite_flat α β h v hc, hp.1, hp.2.2⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
