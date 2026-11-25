/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveStageFamily
public import Colib.Topology.Realization.ProductComparison

/-!
# Stage evaluation on an actual finite carrier of compact nerve parameters

A compact parameter map factors through a finite subcomplex of the original reference
nerve. On that subcomplex the canonical product comparison is a homeomorphism. The lifts
from any two choices with the same actual nerve point agree after inclusion, by injectivity
of the original comparison. No global inverse is asserted.

Adapted from `CommonReferenceNerveCompactStage.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open SmallWaldhausenCategory SSet Topology

/-- The actual finite-right product inverse followed by the specified carrier inclusion. -/
def carrierLift (X Y : SSet.{u}) (B : Y.Subcomplex) [SSet.Finite B] :
    C(|X| × |(B : SSet.{u})|, |X ⊗ Y|) :=
  (SSet.toTop.map (X ◁ B.ι)).hom.comp
    ((ProductRealization.finiteRightHomeomorph X (B : SSet.{u})).symm : C(_, _))

/-- The original comparison of this lift retains both actual coordinates. -/
theorem comparison_carrierLift (X Y : SSet.{u}) (B : Y.Subcomplex) [SSet.Finite B]
    (x : |X|) (b : |(B : SSet.{u})|) :
    ProductRealization.comparison X Y (carrierLift X Y B (x, b)) =
      (x, SSet.toTop.map B.ι b) := by
  change ProductRealization.comparison X Y
    (SSet.toTop.map (X ◁ B.ι)
      ((ProductRealization.finiteRightHomeomorph X (B : SSet.{u})).symm (x, b))) = _
  rw [ProductRealization.comparison_inclusion]
  have h : ProductRealization.comparison X (B : SSet.{u})
      ((ProductRealization.finiteRightHomeomorph X (B : SSet.{u})).symm (x, b)) = (x, b) :=
    (ProductRealization.finiteRightHomeomorph X (B : SSet.{u})).apply_symm_apply (x, b)
  rw [h]

/-- Independent finite carriers yield the same actual point of the realized product. -/
theorem carrierLift_eq (X Y : SSet.{u}) (B C : Y.Subcomplex)
    [SSet.Finite B] [SSet.Finite C] (x : |X|)
    (b : |(B : SSet.{u})|) (c : |(C : SSet.{u})|)
    (h : SSet.toTop.map B.ι b = SSet.toTop.map C.ι c) :
    carrierLift X Y B (x, b) = carrierLift X Y C (x, c) := by
  apply ProductRealization.comparison_injective X Y
  rw [comparison_carrierLift, comparison_carrierLift, h]

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- The original stage transformation evaluated through one actual finite nerve carrier. -/
def stageCarrierFamily (r : ℕ) (B : (nerve (Codiscrete (Node F))).Subcomplex)
    [SSet.Finite B] : C(|(B : SSet)| × stageSpace r V, stageSpace r W) :=
  ⟨fun z ↦ SSet.toTop.map (stageTransformation F r)
    (carrierLift ((stages r).obj V) _ B (z.2, z.1)), by fun_prop⟩

/-- Actual stage evaluation is independent of two carriers of the same full nerve point. -/
theorem stageCarrierFamily_eq (r : ℕ)
    (B C : (nerve (Codiscrete (Node F))).Subcomplex) [SSet.Finite B] [SSet.Finite C]
    (b : |(B : SSet)|) (c : |(C : SSet)|)
    (h : SSet.toTop.map B.ι b = SSet.toTop.map C.ι c) (x : stageSpace r V) :
    stageCarrierFamily F r B (b, x) = stageCarrierFamily F r C (c, x) :=
  congrArg (SSet.toTop.map (stageTransformation F r))
    (carrierLift_eq ((stages r).obj V) _ B C x b c h)

variable {T : Type v} [TopologicalSpace T] [CompactSpace T]

/-- One finite subcomplex through which the entire compact parameter factors. -/
def compactCarrier (p : C(T, |nerve (Codiscrete (Node F))|)) :
    (nerve (Codiscrete (Node F))).Subcomplex :=
  (realization_continuousMap_factors_finiteSubcomplex p).choose

/-- The chosen carrier is genuinely finite. -/
theorem compactCarrier_finite (p : C(T, |nerve (Codiscrete (Node F))|)) :
    SSet.Finite (compactCarrier F p) :=
  (realization_continuousMap_factors_finiteSubcomplex p).choose_spec.1

/-- The continuous factor retains every point of the original compact parameter. -/
def compactFactor (p : C(T, |nerve (Codiscrete (Node F))|)) :
    C(T, |(compactCarrier F p : SSet)|) :=
  (realization_continuousMap_factors_finiteSubcomplex p).choose_spec.2.choose

/-- The factor follows the actual original carrier inclusion, exactly. -/
theorem compactFactor_eq (p : C(T, |nerve (Codiscrete (Node F))|)) :
    (SSet.toTop.map (compactCarrier F p).ι).hom.comp (compactFactor F p) = p :=
  (realization_continuousMap_factors_finiteSubcomplex p).choose_spec.2.choose_spec

/-- Continuous evaluation uses one finite carrier for the whole compact parameter. -/
def compactStageFamily (r : ℕ) (p : C(T, |nerve (Codiscrete (Node F))|)) :
    C(T × stageSpace r V, stageSpace r W) := by
  letI := compactCarrier_finite F p
  exact ⟨fun z ↦ stageCarrierFamily F r (compactCarrier F p)
    (compactFactor F p z.1, z.2), by fun_prop⟩

/-- Every other exact finite factorization gives the same entire native stage family. -/
theorem compactStageFamily_eq_carrier (r : ℕ)
    (p : C(T, |nerve (Codiscrete (Node F))|))
    (B : (nerve (Codiscrete (Node F))).Subcomplex) [SSet.Finite B]
    (g : C(T, |(B : SSet)|)) (hg : (SSet.toTop.map B.ι).hom.comp g = p)
    (t : T) (x : stageSpace r V) :
    compactStageFamily F r p (t, x) = stageCarrierFamily F r B (g t, x) := by
  let := compactCarrier_finite F p
  apply stageCarrierFamily_eq
  exact (DFunLike.congr_fun (compactFactor_eq F p) t).trans
    (DFunLike.congr_fun hg t).symm

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
