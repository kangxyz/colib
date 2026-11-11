/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.FiniteConeTopology
public import Colib.Topology.Prespectrum.LoopTranspose
public import Colib.Topology.Prespectrum.ConeLoopSeparation
public import Colib.Topology.Prespectrum.ParameterLoopingPointHEP
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.VanishingTransport
public import Colib.KTheory.Waldhausen.Iterated.FiniteConnectivity
public import Colib.KTheory.Waldhausen.Iterated.PointHEP

/-! # Topology and all-point growth of finite cone-loop stages

These original proofs retain the literal finite cone iterates and parameter loops. Each loop
loses one degree at every component; genuine Model input supplies the initial hypotheses.
-/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.FiniteConeTopology
variable {C : Type u} [Category.{v} C]

/-- All actual loop iterates retain T1 separation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:111"
  "adaptation" "Original actual cone-loop topology and all-point degree loss."]
instance loopsSpaceT1Space (j : ℕ) (E : LoopPrespectrum.{w})
    [∀ m, T1Space (E.space m)] (m : ℕ) : T1Space ((loops j E).space m) := by
  induction j with
  | zero => exact inferInstanceAs (T1Space (E.space m))
  | succ j ih =>
    let : T1Space ((loops j E).space m) := ih
    exact parameterLoopingSpaceT1Space (loops j E) m

/-- Closed genuine point HEP persists through all actual parameter loops. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:120"
  "adaptation" "Original actual cone-loop topology and all-point degree loss."]
theorem loops_point_homotopyExtensionProperty (j : ℕ) (E : LoopPrespectrum.{w})
    [∀ m, T1Space (E.space m)]
    (h : ∀ m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} (E.point m)))) (m : ℕ) :
    TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((loops j E).point m))) := by
  induction j with
  | zero => exact h m
  | succ j ih =>
    exact parameterLooping_point_homotopyExtensionProperty (loops j E) m
      isClosed_singleton ih

/-- Each actual parameter loop loses one degree at every displayed loop component. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:132"
  "adaptation" "Original actual cone-loop topology and all-point degree loss."]
theorem loops_homotopyGroup_subsingleton (j : ℕ) (E : LoopPrespectrum.{w}) (c : ℕ)
    (hπ : ∀ n k, k < n + 2 → ∀ x : E.space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
    (n k : ℕ) (hk : k < n + 2) (x : (loops j E).space (n + (c + j) + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((loops j E).space (n + (c + j) + 2)) x) := by
  induction j generalizing n k with
  | zero => exact hπ n k hk x
  | succ j ih =>
    have he : n + (c + (j + 1)) + 2 = (n + 1) + (c + j) + 2 := by omega
    revert x
    rw [he]
    intro x
    exact Topology.subsingleton_pi_loop_of_succ
      ((loops j E).point ((n + 1) + (c + j) + 2)) k
      (ih (n + 1) (k + 1) (by omega) ((loops j E).point _)) x

/-- Genuine Model input supplies T1 separation to all finite normalized cone-loop stages. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:151"
  "adaptation" "Original actual cone-loop topology and all-point degree loss."]
instance modelLoopsIterateSpaceT1Space (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ)
    (F : C ⥤ WideSubcategory preservesZero.{w}) (X : C) (m : ℕ) :
    T1Space ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space m) := by
  let : ∀ Y n, T1Space (((F ⋙ prespectrumFunctor).obj Y).space n) :=
    fun Y n => prespectrumSpaceT1Space (F.obj Y) n
  infer_instance

/-- No new well-basedness hypothesis is required at a normalized finite Model stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:159"
  "adaptation" "Original actual cone-loop topology and all-point degree loss."]
theorem modelLoopsIterate_point_homotopyExtensionProperty
    (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})
    (X : C) (m : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).point m))) := by
  let : ∀ Y n, T1Space (((F ⋙ prespectrumFunctor).obj Y).space n) :=
    fun Y n => prespectrumSpaceT1Space (F.obj Y) n
  exact loops_point_homotopyExtensionProperty j _
    (iterate_point_homotopyExtensionProperty Q i (F ⋙ prespectrumFunctor)
      (fun Y n => prespectrum_point_homotopyExtensionProperty (F.obj Y) n) X) m

/-- The genuine normalized Model stage has offset equal to the number of loops alone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeTopology.lean:170"
  "adaptation" "Original actual cone-loop topology and all-point degree loss."]
theorem modelLoopsIterate_homotopyGroup_subsingleton
    (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})
    (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : (loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space (n + j + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space (n + j + 2)) x) := by
  have hπ := iterate_homotopyGroup_subsingleton Q i (F ⋙ prespectrumFunctor)
    (fun Y n => prespectrum_point_homotopyExtensionProperty (F.obj Y) n) 0
    (fun Y n k hk x => prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (F.obj Y) (n + 1) k (by omega) x) X
  have hl := loops_homotopyGroup_subsingleton j _ 0 hπ n k hk
  have he : n + (0 + j) + 2 = n + j + 2 := by omega
  exact (he ▸ hl) x

end KTheory.Bass.FiniteConeTopology
