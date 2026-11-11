/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.StrictDiagramVanishing
public import Colib.KTheory.Waldhausen.Iterated.FiniteConnectivity
public import Colib.KTheory.Waldhausen.Iterated.PointHEP

/-! # Finite topology of the original Model Bass stages

The original iterated-S T1 topology, chosen-point HEP and all-point vanishing pass through
every actual strict Bass iterate, with the original cutoff and degree loss.
-/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

/-- Every original model-diagram Bass stage is T1 at each actual level. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramConnectivity.lean:28"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
instance modelDiagramIterateSpaceT1Space (X : C) (m : ℕ) :
    T1Space ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space m) :=
  @strictDiagramIterateSpaceT1Space _ _ Q i (F ⋙ prespectrumFunctor)
    (fun Y n ↦ prespectrumSpaceT1Space (F.obj Y) n) X m

/-- The literal chosen points remain well-based at every level and every actual iterate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramConnectivity.lean:34"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem modelDiagramIterate_point_homotopyExtensionProperty (X : C) (m : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).point m))) := by
  let : ∀ Y n, T1Space (((F ⋙ prespectrumFunctor).obj Y).space n) :=
    fun Y n ↦ prespectrumSpaceT1Space (F.obj Y) n
  exact strictDiagramIterate_point_homotopyExtensionProperty Q i (F ⋙ prespectrumFunctor)
    (fun Y n ↦ prespectrum_point_homotopyExtensionProperty (F.obj Y) n) X m

/-- All original points satisfy the actual one-degree-per-iterate vanishing range. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramConnectivity.lean:43"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem modelDiagramIterate_homotopyGroup_subsingleton_at (X : C)
    (n k : ℕ) (hk : k < n + 2)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (n + i + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (n + i + 2)) x) := by
  let : ∀ Y m, T1Space (((F ⋙ prespectrumFunctor).obj Y).space m) :=
    fun Y m ↦ prespectrumSpaceT1Space (F.obj Y) m
  have h := strictDiagramIterate_homotopyGroup_subsingleton Q i (F ⋙ prespectrumFunctor)
    (fun Y m ↦ prespectrum_point_homotopyExtensionProperty (F.obj Y) m) 0
    (fun Y m t ht y ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (F.obj Y) (m + 1) t (by omega) y) X n k hk
  rw [Nat.zero_add] at h
  exact h x

/-- The same genuine vanishing bound expressed at an arbitrary level above the exact cutoff. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramConnectivity.lean:58"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem modelDiagramIterate_homotopyGroup_subsingleton_of_le (X : C) (m : ℕ)
    (hm : i + 2 ≤ m) (k : ℕ) (hk : k + i < m)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space m) :
    Subsingleton (HomotopyGroup.Pi k
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space m) x) := by
  have h := modelDiagramIterate_homotopyGroup_subsingleton_at Q i F X
    (m - (i + 2)) k (by omega)
  rw [show m - (i + 2) + i + 2 = m by omega] at h
  exact h x

end KTheory.Bass
