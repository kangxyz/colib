/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelRowZigzagBackwardStable
public import Colib.KTheory.Bass.ModelDiagramRowTargetTopology
public import Colib.Topology.Prespectrum.ZigzagSequentializationLinearGrowth

/-! # The original stable telescope comparison for the proper row target -/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.ModelRowZigzagSequentialization
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C)
  (a : ∀ n, vertex Q M X n ⟶ target Q M X n)

/-- A whole forward factorization gives the original stable telescope comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelRowZigzagSequentialization.lean:79"
  "adaptation" "Original finite-growth stable comparison for the independent row presentation."]
theorem telescopeMap_stable
    (f : ∀ n, vertex Q M X n ⟶ vertex Q M X (n + 1))
    (H : ∀ n, Homotopy (a n) (f n ≫ backward Q M X n)) :
    IsStableEquivalence (ZigzagSequentialization.telescopeMap
      (vertex Q M X) (target Q M X) a (backward Q M X) f H) := by
  let : ∀ n k, T1Space ((vertex Q M X n).space k) :=
    fun n k => modelDiagramIterateSpaceT1Space Q n M X k
  let : ∀ n k, T1Space ((target Q M X n).space k) :=
    fun n k => ModelDiagramRowStabilizedTarget.spaceT1Space Q n M X k
  apply ZigzagSequentialization.telescopeMap_isStableEquivalence_of_linearGrowth
    (vertex Q M X) (target Q M X) a (backward Q M X) (fun n => 2 * n)
    (by intro i j hij; change 2 * i ≤ 2 * j; omega)
    (fun n k => modelDiagramIterate_point_homotopyExtensionProperty Q n M X k)
    (fun n k => ModelDiagramRowStabilizedTarget.point_homotopyExtensionProperty Q n M X k)
    (fun i n x k hk => modelDiagramIterate_homotopyGroup_subsingleton_of_le
      Q i M X (n + 2 * i + 2) (by omega) k (by omega) x)
    (fun i n x k hk => ModelDiagramRowStabilizedTarget.homotopyGroup_subsingleton_at_offset
      Q i M X (2 * (i + 1)) (by omega) n k hk x)
    (backward_stable Q M X) f H

end KTheory.Bass.ModelRowZigzagSequentialization
