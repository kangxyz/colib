/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Bounded-above effective motives with transfers

Use the native bounded-above derived category of Nisnevich sheaves with
transfers. Its effective motives are the objects whose actual cohomology
sheaves with transfers are A¹-invariant.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- The effective-motive condition on the actual bounded-above derived object. -/
def effectiveCohomologyCondition :
    ObjectProperty (DerivedCategory.Minus (SheafWithTransfers.{u + 1} k)) :=
  fun K => ∀ i : ℤ,
    ((DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) i).obj
      (DerivedCategory.Minus.ι.obj K)).obj.IsA1Invariant

/-- Effective motives with bounded-above Nisnevich transfer cohomology. -/
@[colib_tag "COL-1042", colib_ref "Voevodsky2000TriangulatedMotives"
  "Section 3.1, after Proposition 3.1.13" "adaptation"
  "The full subcategory of bounded-above complexes with homotopy invariant cohomology"]
abbrev EffectiveMotivesMinus := (effectiveCohomologyCondition k).FullSubcategory

/-- The inclusion into the original derived category of Nisnevich sheaves with transfers. -/
abbrev effectiveMotivesMinusToDerived :
    EffectiveMotivesMinus k ⥤ DerivedCategory (SheafWithTransfers.{u + 1} k) :=
  (effectiveCohomologyCondition k).ι ⋙ DerivedCategory.Minus.ι

/-- Cohomology in a fixed degree uses the original derived homology functor. -/
abbrev effectiveMotivesMinusCohomology (i : ℤ) :
    EffectiveMotivesMinus k ⥤ SheafWithTransfers.{u + 1} k :=
  effectiveMotivesMinusToDerived k ⋙
    DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) i

/-- The effective object condition gives A¹-invariance of each actual cohomology sheaf. -/
theorem effectiveMotivesMinusCohomology_isA1Invariant (K : EffectiveMotivesMinus k) (i : ℤ) :
    ((effectiveMotivesMinusCohomology k i).obj K).obj.IsA1Invariant :=
  K.property i

end AlgebraicGeometry.MotivicHomotopy
