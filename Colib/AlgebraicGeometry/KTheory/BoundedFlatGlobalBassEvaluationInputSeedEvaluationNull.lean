/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationNullRails
public import Colib.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation

/-!
# The complete original objectwise evaluation null comparison on both sheets

Every original chart, cone-boundary collapse, terminal cancellation, and associator is lifted
with its literal operation clock. Evaluation is pointwise; no continuity of the whole nerve
evaluator is assumed. The two distinct tips are retained throughout the complete comparison.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNull
open CommonReferenceNerve InputSeedEvaluationCarrier InputSeedEvaluationNullChart
open InputSeedEvaluationNullRails

private theorem comparison_refl {T : Type v} [TopologicalSpace T] {a b : T}
    {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (n : ℕ) (x : E.space n) (ev : T → F.space n) (p : Path a b) (H : Homotopy f g)
    (hp : ∀ s, ev (p s) = H.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.refl p (r, s)) =
      (Homotopy.RelHomotopy.refl H).level n (r, (s, x)) := hp s

private theorem comparison_symm {T : Type v} [TopologicalSpace T] {a b : T}
    {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} {p q : Path a b} {H K : Homotopy f g}
    (n : ℕ) (x : E.space n) (ev : T → F.space n)
    (J : p.Homotopy q) (J' : H.RelHomotopy K)
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x))) (r s : I) :
    ev (J.symm (r, s)) = J'.symm.level n (r, (s, x)) := hJ _ s

private theorem comparison_trans {T : Type v} [TopologicalSpace T] {a b : T}
    {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {p q z : Path a b} {H K L : Homotopy f g}
    (n : ℕ) (x : E.space n) (ev : T → F.space n)
    (J : p.Homotopy q) (K' : q.Homotopy z)
    (J' : H.RelHomotopy K) (L' : K.RelHomotopy L)
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x)))
    (hK : ∀ r s, ev (K' (r, s)) = L'.level n (r, (s, x))) (r s : I) :
    ev (J.trans K' (r, s)) = (J'.trans L').level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.trans_apply_path]
  exact Path.Evaluation.comparison_trans ev J K' (J'.path n x) (L'.path n x) hJ hK r s

private theorem comparison_hcomp {T : Type v} [TopologicalSpace T] {a b c : T}
    {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}
    {p q : Path a b} {z w : Path b c} {H H' : Homotopy f g} {K K' : Homotopy g h}
    (n : ℕ) (x : E.space n) (ev : T → F.space n)
    (J : p.Homotopy q) (L : z.Homotopy w)
    (J' : H.RelHomotopy H') (L' : K.RelHomotopy K')
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x)))
    (hL : ∀ r s, ev (L (r, s)) = L'.level n (r, (s, x))) (r s : I) :
    ev (J.hcomp L (r, s)) = (J'.hcomp L').level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.hcomp_apply_path]
  exact Path.Evaluation.comparison_hcomp ev J L (J'.path n x) (L'.path n x) hJ hL r s

private theorem transAssoc {T : Type v} [TopologicalSpace T] {a b c d : T}
    {E F : LoopPrespectrum.{u}} {f g h k : E ⟶ F}
    (n : ℕ) (x : E.space n) (ev : T → F.space n)
    (p : Path a b) (q : Path b c) (w : Path c d)
    (H : Homotopy f g) (K : Homotopy g h) (L : Homotopy h k)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x))
    (hw : ∀ s, ev (w s) = L.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.transAssoc p q w (r, s)) =
      (Homotopy.RelHomotopy.transAssoc H K L).level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.transAssoc_apply_path]
  exact Path.Evaluation.transAssoc ev p q w (H.path n x) (K.path n x) (L.path n x)
    hp hq hw r s

variable (X : Scheme.{u}) (e : Bool)

/-- The original old null retains its positive movement followed by its actual cylinder. -/
abbrev oldNull := (positiveMovement X e).trans (oldCone X e)

/-- The original raw null retains both binary pieces followed by its actual cylinder. -/
abbrev newNull := (newPositive X e).trans (newCone X e)

/-- The literal original recipe, with every relative cut and both original associators. -/
def pastedNull : (oldNull X e).Homotopy ((laurentMovement X e).trans (newNull X e)) :=
  ((Path.Homotopy.refl (positiveMovement X e)).hcomp (coneComparison X e)).trans
    ((Path.Homotopy.transAssoc _ _ _).symm.trans
      (((positivePasting X e).hcomp (Path.Homotopy.refl (newCone X e))).trans
        (Path.Homotopy.transAssoc _ _ _)))

/-- Every coordinate of the frozen original pasted-null surface is recovered on either sheet. -/
theorem pastedNull_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (pastedNull X e (r, s)) x =
      (InputPositiveNull.pastedNullComparison X).level n (r, (s, x)) := by
  let ev := fun z : Carrier X => CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X) n z x
  unfold pastedNull InputPositiveNull.pastedNullComparison
  exact comparison_trans n x ev _ _ _ _
    (comparison_hcomp n x ev _ _ _ _
      (comparison_refl n x ev _ _ (fun t => positiveMovement_native X e n t x))
      (fun a b => coneComparison_native X e n a b x))
    (comparison_trans n x ev _ _ _ _
      (comparison_symm n x ev _ _
        (transAssoc n x ev _ _ _ _ _ _
          (fun t => positiveMovement_native X e n t x)
          (fun t => polynomialMovement_native X e n t x)
          (fun t => newCone_native X e n t x)))
      (comparison_trans n x ev _ _ _ _
        (comparison_hcomp n x ev _ _ _ _
          (fun a b => positivePasting_native X e n a b x)
          (comparison_refl n x ev _ _ (fun t => newCone_native X e n t x)))
        (transAssoc n x ev _ _ _ _ _ _
          (fun t => laurentMovement_native X e n t x)
          (fun t => newPositive_native X e n t x)
          (fun t => newCone_native X e n t x)))) r s

/-- The original endpoint transports leave the complete chosen null comparison unchanged. -/
theorem originalNull_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (pastedNull X e (r, s)) x =
      (InputPositiveNull.originalNullComparison X).level n (r, (s, x)) :=
  pastedNull_native X e n r s x

/-- The actual whole-cone inclusion recovers the original fixed global null comparison. -/
theorem originalNull_whole (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) n (pastedNull X e (r, s)) x) =
      (GlobalBassEvaluationNull.originalNullComparison X).level n (r, (s, x)) :=
  (congrArg ((GlobalRawBass.InputIdentityPositive.inclusion X).map n)
    (originalNull_native X e n r s x)).trans
      (InputPositiveNull.originalNullComparison_mapped X n x r s)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNull
