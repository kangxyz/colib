/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Basic
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Sheafification
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.HomotopyInvariance
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Singular representatives of effective motives

The original singular transfer complex in cochain degrees at most zero has
A¹-invariant cohomology after actual Nisnevich sheafification.
Applying this construction to the additive representable gives the motive
of a smooth correspondence object in the bounded-above effective category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- The actual sheafified singular representative has A¹-invariant derived cohomology. -/
theorem singularDerivedCohomology_isA1Invariant (P : PresheafWithTransfers.{u + 1} k)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) i).obj
      (DerivedCategory.Q.obj (singularSheafCochainComplex k P 0))).obj.IsA1Invariant := by
  let K := singularSheafCochainComplex k P 0
  let e := (DerivedCategory.homologyFunctorFactors (SheafWithTransfers.{u + 1} k) i).app K
  let U := SheafWithTransfers.forget k
  apply IsA1Invariant.of_iso _ (U.mapIso e).symm
  by_cases hi : 0 < i
  · have hz : IsZero (K.homology i) := ShortComplex.isZero_homology_of_isZero_X₂ (K.sc i)
      (isZero_singularSheafCochainComplex_X k P 0 i hi)
    exact isA1Invariant_of_isZero (U.map_isZero hz)
  · let r := (-i).toNat
    have hr : (0 : ℤ) - r = i := by omega
    let L := singularCochainComplex P 0
    let a := nisnevichSheafify k
    let e₁ : K.homology i ≅ a.obj (L.homology i) := (L.sc i).mapHomologyIso a
    let e₂ : L.homology i ≅ (singularComplex P).homology r :=
      (singularComplex P).extendHomologyIso (ComplexShape.embeddingUpIntLE 0) hr
    exact (nisnevichSheafify_isA1Invariant _ (singularComplex_homology_isA1Invariant P r)).of_iso
      (U.mapIso (e₁ ≪≫ a.mapIso e₂)).symm

/-- Place the original singular sheaf complex in the bounded-above derived category. -/
def singularDerivedMinusFunctor :
    PresheafWithTransfers.{u + 1} k ⥤ DerivedCategory.Minus (SheafWithTransfers.{u + 1} k) :=
  (DerivedCategory.TStructure.t (C := SheafWithTransfers.{u + 1} k)).minus.lift
    (singularSheafCochainFunctor k 0 ⋙ DerivedCategory.Q) (fun P => by
      let K := singularSheafCochainComplex k P 0
      let : K.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff K 0).2
        (fun i hi => isZero_singularSheafCochainComplex_X k P 0 i hi)
      exact ⟨0, inferInstanceAs ((DerivedCategory.Q.obj K).IsLE 0)⟩)

/-- The original singular sheaf complex, with its effective cohomology proof. -/
def singularEffectiveMotiveFunctor : PresheafWithTransfers.{u + 1} k ⥤ EffectiveMotivesMinus k :=
  (effectiveCohomologyCondition k).lift (singularDerivedMinusFunctor k)
    (singularDerivedCohomology_isA1Invariant k)

/-- The effective motive functor on actual smooth correspondences. -/
@[colib_tag "COL-1042", colib_ref "Voevodsky2000TriangulatedMotives"
  "Section 3.2, Lemma 3.2.1 and Theorem 3.2.6" "adaptation"
  "The actual sheafified singular representative of a smooth scheme"]
def effectiveMotive : Cor k ⥤ EffectiveMotivesMinus k :=
  representableLarge k ⋙ singularEffectiveMotiveFunctor k

end AlgebraicGeometry.MotivicHomotopy
