/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterPrism

/-!
# Whole native evaluation of the selected split-normalization prism face

Restriction and original normalization evaluation are equalities of entire continuous maps.
Only after composing the independent parameter maps do we evaluate the native input.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.RingedSpace Topology
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterPrism
open GlobalSectionChangeIndex SmallWaldhausenCategory
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The exact selected face retains evaluation time, split-path time, and the native input. -/
def inputCut (n : ℕ) :
    C((unitInterval × unitInterval) × (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj
      (op Y))).space n,
      (unitInterval × (unitInterval × unitInterval)) ×
        (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :=
  ⟨fun z ↦ ((z.1.1, (1, z.1.2)), z.2), by fun_prop⟩

/-- The raw track acts on the actual independent moving evaluation input. -/
def rawInput (n : ℕ) :
    C((unitInterval × unitInterval) × (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj
      (op Y))).space n,
      unitInterval × (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :=
  ⟨fun z ↦ (z.1.2, (evaluationComparison g).level n (z.1.1, z.2)), by fun_prop⟩

private theorem terminal_comp {A B T : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace T]
    {H K : C(A, B)} {S : Set A} (J : H.HomotopyRel K S) (P : C(T, A)) :
    J.toContinuousMap.comp (⟨fun z ↦ (1, P z), by fun_prop⟩ : C(T, _)) = K.comp P := by
  apply ContinuousMap.ext
  intro z
  exact J.apply_one (P z)

/-- Restrict the entire original comparison to its unchanged terminal track. -/
theorem comparison_one_whole {A B C : Scheme.{u}} (f : A ⟶ B) (v : B ⟶ C)
    (n : ℕ) {T : Type*} [TopologicalSpace T]
    (P : C(T, unitInterval × (originalPrespectrum
      (boundedAboveFlatPerfectWaldhausen C.toRingedSpace)).space n)) :
    ((boundedAboveFlatPerfectNormalizedCompTrackComparison f v).level n).toContinuousMap.comp
      (⟨fun z ↦ (1, P z), by fun_prop⟩ : C(T, _)) =
        ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f v).level n).comp P :=
  terminal_comp ((boundedAboveFlatPerfectNormalizedCompTrackComparison f v).level n) P

/-- Restrict the entire compact family before selecting any native input. -/
theorem restricted_whole (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g k hk) n =
      (CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
        (InputChartReference.prismParameter g k hk) n).comp (inputCut (Y := Y) n) := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  let F := InputMixedDesc.sourceMap g
  let p := InputChartReference.prismParameter g k hk
  obtain ⟨j, N, w, hw⟩ := CommonReferenceNerve.exists_parameter F (p (r, (1, s)))
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex F
    (parameter g k hk) N (r, s) w hw.symm n x).trans
    (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex F p N
      (r, (1, s)) w hw.symm n x).symm

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterPrism
