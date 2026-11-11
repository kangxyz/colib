/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramSuspension
public import Colib.KTheory.Bass.ModelZigzagVertices
public import Colib.Topology.Prespectrum.ZigzagSequentializationLinearGrowth

/-! # The actual finite-Model homotopy-pushout comparison

The original topology and all-point growth discharge the analytic premises at monotone offset
`2 * n`. The supplied whole factorization and the original forward suspension unit remain
specified; this result does not identify or replace the tensor/cup forward arrows.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.ModelZigzagSequentialization
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C)
variable (a : ∀ n, vertex Q M X n ⟶ suspendedVertex Q M X n)
    (f : ∀ n, vertex Q M X n ⟶ vertex Q M X (n + 1))
    (H : ∀ n, Homotopy (a n) (f n ≫ unit Q M X n))

/-- Original Model topology discharges every excision premise of the actual telescope map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelZigzagSequentialization.lean:52"
  "adaptation" "Original whole-factorization comparison and actual monotone linear growth."]
theorem telescopeMap_isStableEquivalence :
    IsStableEquivalence (ZigzagSequentialization.telescopeMap
      (vertex Q M X) (suspendedVertex Q M X) a (unit Q M X) f H) := by
  let : ∀ n k, T1Space ((vertex Q M X n).space k) :=
    fun n k ↦ modelDiagramIterateSpaceT1Space Q n M X k
  let : ∀ n k, T1Space ((suspendedVertex Q M X n).space k) :=
    fun n k ↦ ModelDiagramSuspension.spaceT1Space Q (n + 1) M X k
  apply ZigzagSequentialization.telescopeMap_isStableEquivalence_of_linearGrowth
    (vertex Q M X) (suspendedVertex Q M X) a (unit Q M X) (fun n ↦ 2 * n)
    (by intro i j hij; change 2 * i ≤ 2 * j; omega)
    (fun n k ↦ modelDiagramIterate_point_homotopyExtensionProperty Q n M X k)
    (fun n k ↦ ModelDiagramSuspension.point_homotopyExtensionProperty Q (n + 1) M X k)
    (fun i n x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_of_le
      Q i M X (n + 2 * i + 2) (by omega) k (by omega) x)
    (fun i n x k hk ↦ ModelDiagramSuspension.homotopyGroup_subsingleton_at_offset
      Q (i + 1) M X (2 * (i + 1)) (by omega) n k hk x)
    (fun n ↦ ModelDiagramSuspension.unit_stable Q n M X) f H

/-- The localized comparison is the image of the original whole-track telescope map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelZigzagSequentialization.lean:71"
  "adaptation" "Original whole-factorization comparison and actual monotone linear growth."]
def telescopeIso :
    toStableLocalization.obj (Telescope.prespectrum (vertex Q M X) f) ≅
      toStableLocalization.obj (Telescope.prespectrum
        (ZigzagSequentialization.stage (vertex Q M X) (suspendedVertex Q M X) a (unit Q M X))
        (ZigzagSequentialization.transition (vertex Q M X) (suspendedVertex Q M X) a
          (unit Q M X))) :=
  stableLocalizationIso _ (telescopeMap_isStableEquivalence Q M X a f H)

end KTheory.Bass.ModelZigzagSequentialization
