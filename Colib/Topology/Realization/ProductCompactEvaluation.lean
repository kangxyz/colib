/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Topology.Realization.ProductComparison

/-!
# Compact right evaluation on genuine realization products

One finite subcomplex carries the whole compact parameter; the source realization itself need
not be compact. The result is independent of the chosen carrier and evaluates the original
simplicial map at the prescribed pair of realization coordinates.
-/
@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial Topology

universe u v

namespace SSet.ProductRealization

variable {X Y Z : SSet.{u}} {T U : Type v} [TopologicalSpace T] [TopologicalSpace U]
  [CompactSpace T] [CompactSpace U]

/-- The actual finite-right product inverse followed by the original carrier inclusion. -/
def finiteCarrierLift (X Y : SSet.{u}) (B : Y.Subcomplex) [SSet.Finite B] :
    C(|X| × |(B : SSet.{u})|, |X ⊗ Y|) :=
  (SSet.toTop.map (X ◁ B.ι)).hom.comp
    ((finiteRightHomeomorph X (B : SSet.{u})).symm : C(_, _))

/-- Both original product coordinates are unchanged. -/
theorem comparison_finiteCarrierLift (B : Y.Subcomplex) [SSet.Finite B]
    (x : |X|) (b : |(B : SSet.{u})|) :
    comparison X Y (finiteCarrierLift X Y B (x, b)) = (x, SSet.toTop.map B.ι b) := by
  change comparison X Y
    (SSet.toTop.map (X ◁ B.ι) ((finiteRightHomeomorph X (B : SSet.{u})).symm (x, b))) = _
  rw [comparison_inclusion]
  have h : comparison X (B : SSet.{u})
      ((finiteRightHomeomorph X (B : SSet.{u})).symm (x, b)) = (x, b) :=
    (finiteRightHomeomorph X (B : SSet.{u})).apply_symm_apply (x, b)
  rw [h]

/-- A continuous lift of all points over the same compact right parameter. -/
theorem exists_compactRightLift (p : C(T, |Y|)) :
    ∃ lift : C(T × |X|, |X ⊗ Y|), ∀ t x, comparison X Y (lift (t, x)) = (x, p t) := by
  obtain ⟨B, hB, g, hg⟩ := realization_continuousMap_factors_finiteSubcomplex p
  letI : SSet.Finite B := hB
  refine ⟨(finiteCarrierLift X Y B).comp ((ContinuousMap.snd : C(T × |X|, |X|)).prodMk
    (g.comp ContinuousMap.fst)), ?_⟩
  intro t x
  change comparison X Y (finiteCarrierLift X Y B (x, g t)) = _
  rw [comparison_finiteCarrierLift]
  exact _root_.Prod.ext rfl (DFunLike.congr_fun hg t)

/-- Choose one continuous compact-right lift; its value is uniquely determined by comparison. -/
def compactRightLift (p : C(T, |Y|)) : C(T × |X|, |X ⊗ Y|) :=
  (exists_compactRightLift (X := X) p).choose

/-- The product comparison returns the same input and compact-parameter point. -/
theorem comparison_compactRightLift (p : C(T, |Y|)) (t : T) (x : |X|) :
    comparison X Y (compactRightLift p (t, x)) = (x, p t) :=
  (exists_compactRightLift (X := X) p).choose_spec t x

/-- Realize the specified simplicial map at the very same compact-parameter and input points. -/
def compactRightEvaluation (η : X ⊗ Y ⟶ Z) (p : C(T, |Y|)) : C(T × |X|, |Z|) :=
  (SSet.toTop.map η).hom.comp (compactRightLift p)

/-- A given old carrier point is preserved literally, including its independent input coordinate. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/CommonReferenceNerveCompactStage.lean:136-151"
  "adaptation" "Exact compact evaluation on the original finite carrier coordinates."]
theorem compactRightEvaluation_eq_of_comparison (η : X ⊗ Y ⟶ Z) (p : C(T, |Y|))
    (t : T) (x : |X|) (q : |X ⊗ Y|) (hq : comparison X Y q = (x, p t)) :
    compactRightEvaluation η p (t, x) = SSet.toTop.map η q := by
  apply congrArg (SSet.toTop.map η)
  apply comparison_injective X Y
  exact (comparison_compactRightLift p t x).trans hq.symm

/-- Compact evaluation depends on the actual parameter point, not the chosen finite carrier. -/
theorem compactRightEvaluation_eq_of_parameter (η : X ⊗ Y ⟶ Z)
    (p : C(T, |Y|)) (q : C(U, |Y|)) (t : T) (s : U) (h : p t = q s) (x : |X|) :
    compactRightEvaluation η p (t, x) = compactRightEvaluation η q (s, x) := by
  apply compactRightEvaluation_eq_of_comparison
  exact (comparison_compactRightLift q s x).trans (congrArg (fun y ↦ (x, y)) h.symm)

/-- Precomposition changes only the compact parameter of the original evaluated map. -/
theorem compactRightEvaluation_precomp (η : X ⊗ Y ⟶ Z)
    (p : C(T, |Y|)) (q : C(U, T)) (s : U) (x : |X|) :
    compactRightEvaluation η (p.comp q) (s, x) = compactRightEvaluation η p (q s, x) :=
  compactRightEvaluation_eq_of_parameter η (p.comp q) p s (q s) rfl x

end SSet.ProductRealization
