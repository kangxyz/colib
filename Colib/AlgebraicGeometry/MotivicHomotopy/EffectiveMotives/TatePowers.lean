/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Complex
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Exactness
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusPowerRetract

/-!
# Iterating the Tate twist on the motive of the base

The reduced effective tensor adds the first torus coordinate via the
original representable comparison on the split quotient. Successive
shifts by minus one give the genuine signed shift by minus the weight.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Bₖ" => SmoothSite.base Sₖ
local notation "L" => effectiveReducedTorusTensorFunctor k
local notation "E" => effectiveMotivesMinusToDerived k
local notation "C" => singularEffectiveMotiveFunctor k
local notation "D" => EffectiveMotivesMinus k

/-- The actual signed Tate twist, applied repeatedly to the motive of the base. -/
@[no_expose]
def effectiveTatePower : ℕ → D
  | 0 => (effectiveMotive k).obj (Cor.mk Bₖ)
  | q + 1 => ((L).obj (effectiveTatePower q))⟦(-1 : ℤ)⟧

/-- Each iterated twist is the signed shift of the singular motive of the
original reduced transfer torus. -/
@[no_expose]
def effectiveTatePowerTorusIso : (q : ℕ) → effectiveTatePower k q ≅
    ((C).obj (reducedTorus k q))⟦-(q : ℤ)⟧
  | 0 => (C).mapIso (reducedTorusZeroIso k).symm ≪≫
      ((shiftFunctorZero D ℤ).app ((C).obj (reducedTorus k 0))).symm
  | q + 1 => by
    let P := (C).obj (reducedTorus k q)
    let Q := (C).obj (reducedTorus k (q + 1))
    let s := -(q : ℤ)
    let f := effectiveReducedTorusTensorTorusRetractIso k q
    let g := (L).mapIso (effectiveTatePowerTorusIso q) ≪≫
      ((L).commShiftIso s).app P ≪≫ (shiftFunctor D s).mapIso f
    exact (shiftFunctor D (-1 : ℤ)).mapIso g ≪≫
      ((shiftFunctorAdd' D s (-1 : ℤ) (-((q + 1 : ℕ) : ℤ)) (by
        dsimp [s]
        omega)).app Q).symm

/-- The image of the iterated Tate twist is the actual integral motivic
complex, including its signed cochain placement. -/
def effectiveTatePowerMotivicComplexIso (q : ℕ) :
    (E).obj (effectiveTatePower k q) ≅ DerivedCategory.Q.obj (motivicComplex k q) := by
  let A := SheafWithTransfers.{u + 1} k
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let M := (C).obj (reducedTorus k q)
  let K := singularSheafCochainComplex k (reducedTorus k q) 0
  let s := -(q : ℤ)
  exact (E).mapIso (effectiveTatePowerTorusIso k q) ≪≫
    ((E).commShiftIso s).app M ≪≫ (Q.commShiftIso s).symm.app K

end AlgebraicGeometry.MotivicHomotopy
