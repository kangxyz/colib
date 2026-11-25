/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCompactStage
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveParameter
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveStageRealization

/-!
# Equality of compact-parameter and characteristic-simplex stage evaluations

If the actual compact parameter equals a point of a specified characteristic simplex,
both lifts into the realized simplicial product have precisely the same comparison
coordinates. The injectivity of that comparison gives the unchanged stage value.

Adapted from `CommonReferenceNerveCompactStage.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology
universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open SmallWaldhausenCategory SSet

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
variable {T : Type v} [TopologicalSpace T] [CompactSpace T]

/-- The unchanged old simplex lift has the same actual comparison coordinates. -/
theorem comparison_simplexLift (X : SSet.{u}) {k : ℕ} (N : Fin (k + 1) → Node F)
    (x : |X|) (z : StdSimplex ℝ (Fin (k + 1))) :
    ProductRealization.comparison X (nerve (Codiscrete (Node F)))
      (SSet.toTop.map (X ◁ simplexMap F N)
        ((realizationProductSimplexIso X k).inv
          (x, (SimplexCategory.toTopHomeo ⦋k⦌).symm z))) = (x, parameter F N z) := by
  have h := ConcreteCategory.congr_hom
    (prodComparison_natural_whiskerLeft (A := X) SSet.toTop (simplexMap F N))
      ((realizationProductSimplexIso X k).inv
        (x, (SimplexCategory.toTopHomeo ⦋k⦌).symm z))
  change ProductRealization.comparison X _ _ =
    ((realizationProductSimplexIso X k).hom
      ((realizationProductSimplexIso X k).inv
        (x, (SimplexCategory.toTopHomeo ⦋k⦌).symm z))).map id
      (SSet.toTop.map (simplexMap F N)) at h
  rw [Iso.inv_hom_id_apply] at h
  exact h

/-- At every matching nerve point, compact evaluation is the unchanged full old simplex. -/
theorem compactStageFamily_eq_simplex (r : ℕ)
    (p : C(T, |nerve (Codiscrete (Node F))|)) {k : ℕ} (N : Fin (k + 1) → Node F)
    (t : T) (z : StdSimplex ℝ (Fin (k + 1))) (hp : p t = parameter F N z)
    (x : stageSpace r V) :
    compactStageFamily F r p (t, x) = stageBarycentric F r N (z, x) := by
  let := compactCarrier_finite F p
  change SSet.toTop.map (stageTransformation F r)
    (carrierLift ((stages r).obj V) _ (compactCarrier F p) (x, compactFactor F p t)) =
      SSet.toTop.map (stageTransformation F r)
        (SSet.toTop.map ((stages r).obj V ◁ simplexMap F N)
          ((realizationProductSimplexIso ((stages r).obj V) k).inv
            (x, (SimplexCategory.toTopHomeo ⦋k⦌).symm z)))
  apply congrArg (SSet.toTop.map (stageTransformation F r))
  apply ProductRealization.comparison_injective ((stages r).obj V)
    (nerve (Codiscrete (Node F)))
  calc
    _ = (x, SSet.toTop.map (compactCarrier F p).ι (compactFactor F p t)) :=
      comparison_carrierLift ((stages r).obj V) _ (compactCarrier F p) x (compactFactor F p t)
    _ = (x, parameter F N z) :=
      _root_.Prod.ext rfl ((DFunLike.congr_fun (compactFactor_eq F p) t).trans hp)
    _ = _ := (comparison_simplexLift F ((stages r).obj V) N x z).symm

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
