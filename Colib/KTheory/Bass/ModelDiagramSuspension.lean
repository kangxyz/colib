/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramConnectivity
public import Colib.KTheory.Bass.ModelDiagramSuccessor
public import Colib.KTheory.Bass.FiniteConeTopology
public import Colib.Topology.Prespectrum.SuspensionLoopTopology
public import Colib.Topology.Prespectrum.SuspensionLoopUnitStable

/-! # Topology and stability of the actual Model-stage suspension

The original finite Model bounds supply every topology and growth premise. The actual
successor identity proves stability of the original suspension unit at positive stages.
-/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.ModelDiagramSuspension
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

/-- The counit at the unlooped cone of the actual i-th Bass iterate is stable. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramSuspension.lean:34"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem cone_counit_stable (X : C) :
    IsStableEquivalence (suspensionLoopCounit
      ((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor))).obj X)) := by
  let G := (strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)
  let : ∀ Y n, T1Space ((G.obj Y).space n) :=
    fun Y n ↦ modelDiagramIterateSpaceT1Space Q i F Y n
  have hp := modelDiagramIterate_point_homotopyExtensionProperty Q i F
  change IsStableEquivalence (suspensionLoopCounit ((ConeTrack.diagram Q G).obj X))
  apply suspensionLoopCounit_isStableEquivalence_of_linearGrowth _ i
  · exact FiniteConeTopology.iterate_point_homotopyExtensionProperty Q 1 G hp X
  · intro n x k hk
    exact FiniteConeTopology.iterate_homotopyGroup_subsingleton Q 1 G hp i
      (fun Y m j hj y ↦ modelDiagramIterate_homotopyGroup_subsingleton_at
        Q i F Y m j hj y) X n k hk x

/-- The original forward suspension unit is stable at every positive actual Bass stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramSuspension.lean:59"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem unit_stable (X : C) :
    IsStableEquivalence (suspensionLoopUnit
      (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X)) := by
  rw [successor_obj]
  exact suspensionLoopUnit_parameterLooping_isStableEquivalence _
    (cone_counit_stable Q i F X)

/-- The actual looped suspension of every original stage retains T1 separation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramSuspension.lean:67"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
instance spaceT1Space (X : C) (n : ℕ) :
    T1Space ((parameterLooping (suspensionCone
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).space n) := by
  infer_instance

/-- The actual looped-suspension point has HEP at every level of every original stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramSuspension.lean:73"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem point_homotopyExtensionProperty (X : C) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((parameterLooping (suspensionCone
        (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).point n))) :=
  suspensionLoop_point_homotopyExtensionProperty _ n
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F X n)

/-- The entire original looped-suspension stage has precisely the proved offset i+1. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramSuspension.lean:81"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem homotopyGroup_subsingleton_at (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : (parameterLooping (suspensionCone
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).space
        (n + (i + 1) + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((parameterLooping (suspensionCone
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).space
        (n + (i + 1) + 2)) x) :=
  suspensionLoop_homotopyGroup_subsingleton _ i
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F X)
    (fun m y j hj ↦ modelDiagramIterate_homotopyGroup_subsingleton_at Q i F X m j hj y)
    n x k hk

/-- The same all-point bound at an arbitrary level above the original cutoff. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramSuspension.lean:94"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem homotopyGroup_subsingleton_of_le (X : C) (m : ℕ) (hm : i + 3 ≤ m)
    (k : ℕ) (hk : k + (i + 1) < m)
    (x : (parameterLooping (suspensionCone
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).space m) :
    Subsingleton (HomotopyGroup.Pi k ((parameterLooping (suspensionCone
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).space m) x) := by
  have h := homotopyGroup_subsingleton_at Q i F X (m - (i + 3)) k (by omega)
  rw [show m - (i + 3) + (i + 1) + 2 = m by omega] at h
  exact h x

/-- Increasing the explicit offset preserves the original all-point growth bound. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramSuspension.lean:105"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem homotopyGroup_subsingleton_at_offset (X : C) (c : ℕ) (hc : i + 1 ≤ c)
    (n k : ℕ) (hk : k < n + 2)
    (x : (parameterLooping (suspensionCone
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).space (n + c + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((parameterLooping (suspensionCone
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).space (n + c + 2)) x) :=
  homotopyGroup_subsingleton_of_le Q i F X (n + c + 2) (by omega) k (by omega) x

end KTheory.Bass.ModelDiagramSuspension
