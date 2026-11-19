/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.ReflectionNaturality
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Triangulated
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # The effective coefficient of a homotopy invariant transfer sheaf -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

local notation "NST" => LargeSheaves k
local notation "J" => effectiveMotivesMinusToDerived k
local notation "D" => DerivedCategory.singleFunctor NST 0

/-- The coefficient is the original transfer sheaf concentrated in degree zero. -/
def effectiveHICoefficient (F : NST) (hF : F.obj.IsA1Invariant) :
    EffectiveMotivesMinus k := by
  refine ⟨(singleTransferSheafMinus k).obj F, ?_⟩
  intro i
  change ((DerivedCategory.homologyFunctor NST i).obj ((D).obj F)).obj.IsA1Invariant
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact isA1Invariant_of_isZero ((SheafWithTransfers.forget k).map_isZero
      (DerivedCategory.isZero_of_isGE ((D).obj F) 0 i hi))
  · exact hF.of_iso ((SheafWithTransfers.forget k).mapIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso NST 0).app F).symm)
  · exact isA1Invariant_of_isZero ((SheafWithTransfers.forget k).map_isZero
      (DerivedCategory.isZero_of_isLE ((D).obj F) 0 i hi))

/-- Forgetting the effective structure leaves the original single sheaf. -/
theorem effectiveHICoefficient_toDerived (F : NST) (hF : F.obj.IsA1Invariant) :
    (J).obj (effectiveHICoefficient k F hF) = (D).obj F := rfl

/-- A coefficient morphism acts by the original degree-zero morphism. -/
def effectiveHICoefficientMap {F G : NST} (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant)
    (f : F ⟶ G) : effectiveHICoefficient k F hF ⟶ effectiveHICoefficient k G hG :=
  ObjectProperty.homMk ((singleTransferSheafMinus k).map f)

/-- Forgetting the effective structure leaves the original map of single sheaves. -/
theorem effectiveHICoefficientMap_toDerived {F G : NST}
    (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant) (f : F ⟶ G) :
    (J).map (effectiveHICoefficientMap k hF hG f) = (D).map f := rfl

variable [PerfectField k]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Negative-degree derived maps between the specified single sheaves vanish. -/
theorem derivedHom_to_effectiveHICoefficient_shift_eq_zero_of_neg
    (A F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ) (hn : n < 0)
    (x : (D).obj A ⟶ (J).obj ((effectiveHICoefficient k F hF)⟦n⟧)) : x = 0 := by
  let K := effectiveHICoefficient k F hF
  let t := DerivedCategory.TStructure.t (C := NST)
  let : t.IsGE ((J).obj K) 0 := inferInstanceAs (((D).obj F).IsGE 0)
  let : t.IsGE (((J) ⋙ shiftFunctor (DerivedCategory NST) n).obj K) (-n) :=
    t.isGE_shift ((J).obj K) 0 n (-n) (by omega)
  have hTarget : t.IsGE ((J).obj (K⟦n⟧)) (-n) :=
    t.isGE_of_iso (((J).commShiftIso n).app K).symm (-n)
  exact t.zero_of_isLE_of_isGE x 0 (-n) (by omega)
    (inferInstanceAs (((D).obj A).IsLE 0)) hTarget

end AlgebraicGeometry.MotivicHomotopy
