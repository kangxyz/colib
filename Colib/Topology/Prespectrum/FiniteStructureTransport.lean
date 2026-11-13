/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.Loop
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift

/-!
# Finite transport of the actual structure homomorphism

Bijections for the two displayed component maps transport a finite structure-map
bijection along an actual prespectrum morphism. Looping uses the original loop-shift
equivalence and no assertion about another prespectrum structure.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiniteStructureTransport.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual based maps,
finite degrees and original proof steps are retained under native names. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology
universe u
namespace Topology

/-- A chosen-point bijection one degree higher gives the actual based-loop bijection. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/FiniteStructureTransport.lean:26-39"
  "adaptation" "Loop-shift naturality transports bijectivity from the successor degree"]
theorem _root_.HomotopyGroup.map_basedLoopMap_bijective_of_succ
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) (k : ℕ)
    (hf : Function.Bijective (HomotopyGroup.map (N := Fin (k + 1)) f h)) :
    Function.Bijective (HomotopyGroup.map (N := Fin k) (basedLoopMap f h)
      (basedLoopMap_refl f h)) := by
  have hb := (loopShiftEquiv (x := y) k).bijective.comp hf
  have he : loopShiftEquiv (x := y) k ∘ HomotopyGroup.map (N := Fin (k + 1)) f h =
      HomotopyGroup.map (N := Fin k) (basedLoopMap f h) (basedLoopMap_refl f h) ∘
        loopShiftEquiv (x := x) k := by
    funext z
    exact loopShiftEquiv_natural k f h z
  rw [he] at hb
  exact (Function.Bijective.of_comp_iff _ (loopShiftEquiv (x := x) k).bijective).mp hb

namespace LoopPrespectrum

/-- Component bijections in precisely two degrees transport the original structure map. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/FiniteStructureTransport.lean:44-66"
  "adaptation"
  "The original strictly commuting structure square transports bijectivity to the target"]
theorem structure_bijective_of_map {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (n k : ℕ)
    (hn : Function.Bijective (HomotopyGroup.map (N := Fin k) (f.map n) (f.map_point n)))
    (hs : Function.Bijective (HomotopyGroup.map (N := Fin (k + 1))
      (f.map (n + 1)) (f.map_point (n + 1))))
    (hE : Function.Bijective (HomotopyGroup.map (N := Fin k)
      (E.structureMap n) (E.map_point n))) :
    Function.Bijective (HomotopyGroup.map (N := Fin k) (F.structureMap n) (F.map_point n)) := by
  have hloop := HomotopyGroup.map_basedLoopMap_bijective_of_succ
    (f.map (n + 1)) (f.map_point (n + 1)) k hs
  have he : HomotopyGroup.map (N := Fin k) (basedLoopMap (f.map (n + 1))
        (f.map_point (n + 1))) (basedLoopMap_refl _ _) ∘
      HomotopyGroup.map (N := Fin k) (E.structureMap n) (E.map_point n) =
    HomotopyGroup.map (N := Fin k) (F.structureMap n) (F.map_point n) ∘
      HomotopyGroup.map (N := Fin k) (f.map n) (f.map_point n) := by
    funext z
    simp only [Function.comp_apply]
    rw [← HomotopyGroup.map_comp, ← HomotopyGroup.map_comp]
    congr 1
    exact ContinuousMap.ext (fun x => f.comm n x)
  have hb := hloop.comp hE
  rw [he] at hb
  exact (Function.Bijective.of_comp_iff _ hn).mp hb

/-- The converse transport uses the same actual structure square. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/FiniteStructureTransport.lean:69-91"
  "adaptation" "The same structure square transports bijectivity to the source"]
theorem structure_bijective_of_map_target {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (n k : ℕ)
    (hn : Function.Bijective (HomotopyGroup.map (N := Fin k) (f.map n) (f.map_point n)))
    (hs : Function.Bijective (HomotopyGroup.map (N := Fin (k + 1))
      (f.map (n + 1)) (f.map_point (n + 1))))
    (hF : Function.Bijective (HomotopyGroup.map (N := Fin k)
      (F.structureMap n) (F.map_point n))) :
    Function.Bijective (HomotopyGroup.map (N := Fin k) (E.structureMap n) (E.map_point n)) := by
  have hloop := HomotopyGroup.map_basedLoopMap_bijective_of_succ
    (f.map (n + 1)) (f.map_point (n + 1)) k hs
  have he : HomotopyGroup.map (N := Fin k) (basedLoopMap (f.map (n + 1))
        (f.map_point (n + 1))) (basedLoopMap_refl _ _) ∘
      HomotopyGroup.map (N := Fin k) (E.structureMap n) (E.map_point n) =
    HomotopyGroup.map (N := Fin k) (F.structureMap n) (F.map_point n) ∘
      HomotopyGroup.map (N := Fin k) (f.map n) (f.map_point n) := by
    funext z
    simp only [Function.comp_apply]
    rw [← HomotopyGroup.map_comp, ← HomotopyGroup.map_comp]
    congr 1
    exact ContinuousMap.ext (fun x => f.comm n x)
  have hb := hF.comp hn
  rw [← he] at hb
  exact (Function.Bijective.of_comp_iff' hloop _).mp hb

end LoopPrespectrum
end Topology
