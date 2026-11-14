/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # The genuine shift on perfect cochain complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSpace

universe u

variable (X : RingedSpace.{u, u})

local notation "P" => IsPerfectComplex (X := X)
local notation "A" => StrictlyPerfect.OXMod X
local notation "W" => perfectComplexesWaldhausen X

/-- The actual cochain shift preserves native perfectness. -/
theorem isPerfectComplex_shift (K : CochainComplex A ℤ) (hK : P K) (n : ℤ) :
    P ((shiftFunctor _ n).obj K) := by
  let : HasDerivedCategory.{u + 1} A := HasDerivedCategory.standard _
  exact isPerfectComplex_of_isPerfect_representation
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hK.isPerfect n)
    ⟨(DerivedCategory.Q.commShiftIso n).app K⟩

/-- Shift of the underlying cochain complex in the native perfect category. -/
def perfectShift (n : ℤ) : ObjectProperty.FullSubcategory P ⥤
    ObjectProperty.FullSubcategory P :=
  ObjectProperty.lift P (ObjectProperty.ι P ⋙ shiftFunctor _ n)
    (fun K => isPerfectComplex_shift X K.obj K.property n)

/-- The shift is exact for actual monomorphisms and quasi-isomorphisms. -/
theorem perfectShift_exact (n : ℤ) :
    Waldhausen.IsExact (W).cof (W).weq (W).cof (W).weq (perfectShift X n) := by
  let F := shiftFunctor (CochainComplex A ℤ) n
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro K hK
    apply IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι P)
    exact F.map_isZero
      ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
        (Waldhausen.complexes A) P (perfectComplexes_cofibrationClosed X)).zero hK)
  · intro K L f hf
    change Mono (F.map f.hom)
    have : Mono (C := CochainComplex A ℤ) f.hom := hf
    infer_instance
  · intro K L f hf
    change QuasiIso (F.map f.hom)
    exact (CochainComplex.quasiIso_shift_iff f.hom n).2 hf
  · intro B C D E i f g j hi h
    have : PreservesColimits F := inferInstanceAs (PreservesColimits (shiftFunctor _ n))
    apply IsPushout.of_map_of_faithful (ObjectProperty.ι P)
    have hp := Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes A) P (perfectComplexes_cofibrationClosed X) hi h
    let hspan : PreservesColimitsOfShape WalkingSpan F :=
      PreservesColimitsOfSize.preservesColimitsOfShape
    let : PreservesColimit (span i.hom f.hom) F :=
      hspan.preservesColimit
    exact hp.map F

end AlgebraicGeometry.RingedSpace
