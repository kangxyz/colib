/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationUnitNative
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNervePointwiseFamily

/-!
# Original evaluation-unit pasting on its actual reference nerve

The complete four-node parameter evaluates to the unchanged original relative homotopy.
Its compact two-parameter family is the same entire native continuous map after the explicit
product association, without asserting joint continuity on an unrestricted nerve product.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationUnit
open GlobalSectionChangeIndex CommonReferenceNerve

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- Every point of the actual reference-nerve parameter is the original native pasting. -/
theorem parameter_native (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    pointwisePrespectrumFamily (sourceMap f) n (parameter f r (s, t)) x =
      (evaluationUnitPasting f r).level n (s, (t, x)) := by
  change pointwisePrespectrumFamily (sourceMap f) n
    (CommonReferenceNerve.parameter (sourceMap f) (nodes f r) (scalarParameter (s, t))) x = _
  rw [pointwisePrespectrumFamily_parameter]
  exact native f r n s t x

/-- The existing compact nerve family retains the original full two-time comparison. -/
theorem compact_native (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    compactPrespectrumFamily (sourceMap f) (parameter f r) n ((s, t), x) =
      (evaluationUnitPasting f r).level n (s, (t, x)) :=
  (pointwisePrespectrumFamily_eq_compact (sourceMap f) (parameter f r) n (s, t) x).symm.trans
    (parameter_native f r n s t x)

/-- The complete compact family has the same native continuous map after product association. -/
theorem compact_family_eq (n : ℕ) :
    (compactPrespectrumFamily (sourceMap f) (parameter f r) n).comp
        (⟨fun z => ((z.1, z.2.1), z.2.2), by fun_prop⟩ :
          C(unitInterval × (unitInterval ×
            (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n),
            (unitInterval × unitInterval) ×
              (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n)) =
      ((evaluationUnitPasting f r).level n).toContinuousMap := by
  apply ContinuousMap.ext
  rintro ⟨s, t, x⟩
  exact compact_native f r n s t x

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationUnit
