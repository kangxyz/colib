/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramRowReplacementStable

/-!
# Topology and finite growth of the actual proper-row target

The zero level retains its three path coordinates; positive levels retain their two path
coordinates. The original finite-cone argument proves separation, point HEP and the all-point
linear growth bound on this same target, without introducing a second prespectrum model.

Adapted from `Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:103-144` and the
finite-cone proofs in `ModelDiagramStabilizedTarget.lean:42-105` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.ModelDiagramRowStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

private instance coneSpaceT1Space (X : C) (n : ℕ) :
    T1Space ((cone Q i F X).space n) := by
  let : ∀ Y m, T1Space
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj Y).space m) :=
    fun Y m ↦ modelDiagramIterateSpaceT1Space Q i F Y m
  exact FiniteConeTopology.diagramSpaceT1Space Q _ X n

/-- The actual zero-level triple loop and positive double loops retain T1 separation. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:104"
  "adaptation" "Original actual row target, with its extra zero-level loop retained."]
instance spaceT1Space (X : C) (n : ℕ) : T1Space ((target Q i F X).space n) := by
  cases n with
  | zero =>
    change T1Space (Path (Path.refl (Path.refl ((cone Q i F X).point 2)))
      (Path.refl (Path.refl ((cone Q i F X).point 2))))
    infer_instance
  | succ k =>
    change T1Space (Path (Path.refl ((cone Q i F X).point (k + 2)))
      (Path.refl ((cone Q i F X).point (k + 2))))
    infer_instance

private theorem cone_point_homotopyExtensionProperty (X : C) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{w + 1} ((cone Q i F X).point n))) :=
  FiniteConeTopology.iterate_point_homotopyExtensionProperty Q 1
    ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F) X n

/-- Point HEP retains the extra actual zero-level loop rather than deleting it. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:116"
  "adaptation" "Original finite-cone HEP followed by the actual two or three path coordinates."]
theorem point_homotopyExtensionProperty (X : C) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{w + 1} ((target Q i F X).point n))) := by
  cases n with
  | zero =>
    have : T1Space ((ModelDiagramRowRefinement.carrier Q i F X).space 0) := by
      change T1Space (Path (Path.refl ((cone Q i F X).point 2))
        (Path.refl ((cone Q i F X).point 2)))
      infer_instance
    have h₁ := Path.homotopyExtensionProperty_refl
      (isClosed_singleton (x := (cone Q i F X).point 2))
      (cone_point_homotopyExtensionProperty Q i F X 2)
    have h₂ := Path.homotopyExtensionProperty_refl isClosed_singleton h₁
    exact Path.homotopyExtensionProperty_refl isClosed_singleton h₂
  | succ k =>
    have : T1Space ((ModelDiagramRowRefinement.carrier Q i F X).space (k + 1)) := by
      change T1Space (Path ((cone Q i F X).point (k + 2))
        ((cone Q i F X).point (k + 2)))
      infer_instance
    have h₁ := Path.homotopyExtensionProperty_refl
      (isClosed_singleton (x := (cone Q i F X).point (k + 2)))
      (cone_point_homotopyExtensionProperty Q i F X (k + 2))
    exact Path.homotopyExtensionProperty_refl isClosed_singleton h₁

/-- At the positive growth cutoff the proper target has the original double-loop spaces. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:134"
  "adaptation" "Original finite-cone all-point bound through the two actual loop coordinates."]
theorem homotopyGroup_subsingleton_at (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : (target Q i F X).space (n + (i + 1) + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((target Q i F X).space (n + (i + 1) + 2)) x) := by
  have hπ := FiniteConeTopology.iterate_homotopyGroup_subsingleton Q 1
    ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F) i
    (fun Y m j hj y ↦ modelDiagramIterate_homotopyGroup_subsingleton_at
      Q i F Y m j hj y) X (n + 2) (k + 2) (by omega)
  have he : (n + 2) + i + 2 = (n + (i + 1) + 2) + 1 := by omega
  rw [he] at hπ
  apply subsingleton_pi_loop_of_succ
    (Path.refl ((cone Q i F X).point ((n + (i + 1) + 2) + 1))) k
  exact subsingleton_pi_loop_of_succ
    ((cone Q i F X).point ((n + (i + 1) + 2) + 1)) (k + 1)
    (hπ ((cone Q i F X).point _)) _

/-- Larger offsets retain the actual positive-level growth bound. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramRowStabilizedTarget.lean:140"
  "adaptation" "Original monotonicity of the all-point finite-growth cutoff."]
theorem homotopyGroup_subsingleton_at_offset (X : C) (c : ℕ) (hc : i + 1 ≤ c)
    (n k : ℕ) (hk : k < n + 2) (x : (target Q i F X).space (n + c + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((target Q i F X).space (n + c + 2)) x) := by
  have h := homotopyGroup_subsingleton_at Q i F X (n + c - (i + 1)) k (by omega)
  rw [show n + c - (i + 1) + (i + 1) + 2 = n + c + 2 by omega] at h
  exact h x

end KTheory.Bass.ModelDiagramRowStabilizedTarget
