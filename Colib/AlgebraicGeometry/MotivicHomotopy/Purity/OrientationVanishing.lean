/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.WeightZeroSections
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.Support
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.InvariantUnit
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Cancellation
public import Colib.CategoryTheory.Triangulated.Stabilization.ShiftStages
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Exactness
import Colib.CategoryTheory.Triangulated.SignedShift
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Negative weight-zero degree for orientation descent

Cancellation removes the same Lefschetz power from a local supported class
and its target. In weight zero, a positive shift on the source has zero Hom
to the base motive, by the ordinary cochain bounds.
-/

public noncomputable section

open AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" k ")" => SmoothSite (Spec (CommRingCat.of k))
local notation "J" => effectiveMotivesMinusToDerived k
local notation "M" => effectiveSmoothMotive k
local notation "B" => SmoothSite.base (Spec (CommRingCat.of k))
local notation "L" => effectiveLefschetzTwistFunctor k

/-- The native abelian structure on transfer sheaves in the shifted Hom calculation. -/
local instance orientationVanishingAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

/-- In the chosen derived category the base motive is the actual invariant
transfer coefficient in degree zero, via its singular augmentation. -/
def effectiveBaseMotiveToSingleIso :
    (J).obj ((M).obj B) ≅
      (DerivedCategory.singleFunctor (LargeSheaves k) 0).obj
        ((transferRepresentable k).obj (Cor.mk B)) := by
  let P := (representableLarge k).obj (Cor.mk B)
  let f := singularDerivedUnitApp k P
  let : IsIso f := isIso_singularDerivedUnitApp k P (baseRepresentable_isA1Invariant k)
  exact (asIso f).symm

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}] in
/-- A smooth motive with any positive cochain shift has zero Hom to the base. -/
theorem subsingleton_effectiveSmoothMotive_shift_hom_base_of_pos (X : Sm(k))
    (a : ℤ) (ha : 0 < a) :
    Subsingleton (((M).obj X)⟦a⟧ ⟶ (M).obj B) := by
  let C := DerivedCategory (LargeSheaves k)
  let t := DerivedCategory.TStructure.t (C := LargeSheaves k)
  let A : C := (J).obj ((M).obj X)
  let D : C := (J).obj ((M).obj B)
  have hA : A.IsLE 0 := by
    let P := (representableLarge k).obj (Cor.mk X)
    let K := singularSheafCochainComplex k P 0
    let : K.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff K 0).2
      (fun i hi => isZero_singularSheafCochainComplex_X k P 0 i hi)
    exact inferInstanceAs ((DerivedCategory.Q.obj K).IsLE 0)
  have hD : D.IsGE 0 := t.isGE_of_iso (effectiveBaseMotiveToSingleIso k).symm 0
  let : A.IsLE 0 := hA
  let hA' : (A⟦a⟧).IsLE (-a) := t.isLE_shift A 0 a (-a) (add_neg_cancel a)
  let e := ((J).commShiftIso a).app ((M).obj X)
  refine ⟨fun f g => (J).map_injective ?_⟩
  apply (cancel_epi e.inv).1
  have hf := t.zero_of_isLE_of_isGE (e.inv ≫ (J).map f) (-a) 0 (neg_lt_zero.2 ha) hA' hD
  have hg := t.zero_of_isLE_of_isGE (e.inv ≫ (J).map g) (-a) 0 (neg_lt_zero.2 ha) hA' hD
  exact hf.trans hg.symm

/-- Cancellation gives the vanishing that makes the local rank-`c` Thom
class glue uniquely across a smooth overlap. -/
theorem subsingleton_shift_iterateLefschetz_hom_base_of_pos (c : ℕ) (X : Sm(k))
    (a : ℤ) (ha : 0 < a) :
    Subsingleton
      ((((Stabilization.iterate L c).obj ((M).obj X))⟦a⟧) ⟶
        (Stabilization.iterate L c).obj ((M).obj B)) := by
  let e := (effectiveReducedTorusTensorFullyFaithful k).comp
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor (EffectiveMotivesMinus k) (1 : ℤ)))
  let : (L).Full := e.full
  let : (L).Faithful := e.faithful
  let F := Stabilization.iterate L c
  let e' := Functor.FullyFaithful.ofFullyFaithful F
  let : F.CommShift ℤ := inferInstanceAs ((Stabilization.iterate (L) c).CommShift ℤ)
  let V := (M).obj X
  let W := (M).obj B
  let x := (F.commShiftIso a).app V
  let h := subsingleton_effectiveSmoothMotive_shift_hom_base_of_pos k X a ha
  refine ⟨fun f g => (cancel_epi x.hom).mp ?_⟩
  exact (e'.homEquiv (X := V⟦a⟧) (Y := W)).symm.injective (h.elim _ _)

/-- In particular the negative degree needed for binary Thom descent vanishes. -/
theorem subsingleton_shift_iterateLefschetz_hom_base (c : ℕ) (X : Sm(k)) :
    Subsingleton
      ((((Stabilization.iterate L c).obj ((M).obj X))⟦(1 : ℤ)⟧) ⟶
        (Stabilization.iterate L c).obj ((M).obj B)) :=
  subsingleton_shift_iterateLefschetz_hom_base_of_pos k c X 1 (by decide)

end AlgebraicGeometry.MotivicHomotopy
