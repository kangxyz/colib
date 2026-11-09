/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Bass.StrictDiagramSeparation
import Colib.KTheory.Bass.StrictDiagramMap
import Colib.KTheory.Waldhausen.Iterated.Separation
import Colib.Topology.Prespectrum.TelescopeStableColimit

/-!
# Actual supplied-seed Bass towers satisfy the stable-colimit hypotheses

Separation of every finite stage is derived from the initial row alone. The actual
transition is the iterated supplied seed, including stage zero. A supplied proved seed
square gives actual comparison naturality, not stable equivalence of its iterated maps.
The concrete constant endpoint maps are noninjective and exercise all collapsed fibers.
-/

open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum KTheory.Bass
open scoped unitInterval

noncomputable section
universe u v w

namespace ColibTest.BassTowerSeparation

section Tower

variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (F : C ⥤ LoopPrespectrum.{w})

abbrev stages (X : C) (i : ℕ) : LoopPrespectrum.{w} :=
  ((strictDiagramIterate Q i).obj F).obj X

abbrev steps (η : F ⟶ (strictDiagramFunctor Q).obj F) (X : C) (i : ℕ) :
    stages Q F X i ⟶ stages Q F X (i + 1) :=
  (strictDiagramTransition Q η i).app X

example (η : F ⟶ (strictDiagramFunctor Q).obj F) (X : C) :
    steps Q F η X 0 = η.app X := rfl

example (X : C) : stages Q F X 0 = F.obj X := rfl

variable [∀ X k, T1Space ((F.obj X).space k)]

example (X : C) (i k : ℕ) : T1Space ((stages Q F X i).space k) := inferInstance

example (X : C) : T1Space ((stages Q F X 0).space 0) := inferInstance

variable (η : F ⟶ (strictDiagramFunctor Q).obj F) (X : C)

example (k : ℕ) : T1Space ((Telescope.prespectrum (stages Q F X) (steps Q F η X)).space k) := by
  change T1Space (Telescope.Space (stages Q F X) (steps Q F η X) k)
  infer_instance

/-- COL-0350 applied to the literal Bass stages and literal supplied-seed transitions. -/
def stableIso (d : ℤ) :
    colimit (Telescope.stageStableDiagram (stages Q F X) (steps Q F η X) d) ≅
      stableHomotopyGroup (Telescope.prespectrum (stages Q F X) (steps Q F η X)) d :=
  Telescope.stableColimitIso (stages Q F X) (steps Q F η X) d

example (d : ℤ) (i : ℕ) :
    colimit.ι (Telescope.stageStableDiagram (stages Q F X) (steps Q F η X) d) i ≫
        (stableIso Q F η X d).hom =
      (stableHomotopyFunctor d).map (Telescope.inclusion (stages Q F X) (steps Q F η X) i) :=
  Telescope.stableColimitIso_ι_hom (stages Q F X) (steps Q F η X) d i

example (d : ℤ) :
    colimit.ι (Telescope.stageStableDiagram (stages Q F X) (steps Q F η X) d) 0 ≫
        (stableIso Q F η X d).hom =
      (stableHomotopyFunctor d).map (Telescope.inclusion (stages Q F X) (steps Q F η X) 0) :=
  Telescope.stableColimitIso_ι_hom (stages Q F X) (steps Q F η X) d 0

end Tower

section Comparison

variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (F G : C ⥤ LoopPrespectrum.{w})
  (seedF : F ⟶ (strictDiagramFunctor Q).obj F) (seedG : G ⟶ (strictDiagramFunctor Q).obj G)
  (a : F ⟶ G) (h : seedF ≫ (strictDiagramFunctor Q).map a = a ≫ seedG) (X : C)

abbrev stageMaps (i : ℕ) : stages Q F X i ⟶ stages Q G X i :=
  ((strictDiagramIterate Q i).map a).app X

include h in
lemma stageSquare (i : ℕ) :
    stageMaps Q F G a X i ≫ steps Q G seedG X i =
      steps Q F seedF X i ≫ stageMaps Q F G a X (i + 1) := by
  exact (congrArg (fun z ↦ z.app X) (strictDiagramTransition_map Q seedF seedG a h i)).symm

variable [∀ X k, T1Space ((F.obj X).space k)] [∀ X k, T1Space ((G.obj X).space k)]

example (d : ℤ) :
    colimMap (Telescope.stageStableDiagramMap
        (stages Q F X) (steps Q F seedF X) (stages Q G X) (steps Q G seedG X)
        (stageMaps Q F G a X) (stageSquare Q F G seedF seedG a h X) d) ≫
        (stableIso Q G seedG X d).hom =
      (stableIso Q F seedF X d).hom ≫
        (stableHomotopyFunctor d).map (Telescope.map
          (stages Q F X) (steps Q F seedF X) (stages Q G X) (steps Q G seedG X)
          (stageMaps Q F G a X) (stageSquare Q F G seedF seedG a h X)) :=
  Telescope.stableColimitIso_naturality
    (stages Q F X) (steps Q F seedF X) (stages Q G X) (steps Q G seedG X)
    (stageMaps Q F G a X) (stageSquare Q F G seedF seedG a h X) d

end Comparison

section WaldhausenRow

open CategoryTheory.Waldhausen.SmallWaldhausenCategory

variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (W : C ⥤ WideSubcategory preservesZero.{w})

abbrev originalRow : C ⥤ LoopPrespectrum.{w} := W ⋙ Waldhausen.IteratedS.prespectrumFunctor

example (X : C) (k i : ℕ) :
    T1Space ((stages Q (originalRow W) X i).space k) := by
  let : ∀ Y n, T1Space (((originalRow W).obj Y).space n) :=
    fun Y n ↦ Waldhausen.IteratedS.prespectrumSpaceT1Space (W.obj Y) n
  infer_instance

/-- The actual original small-Waldhausen row needs no separately assumed T1 premise. -/
def waldhausenStableIso (η : originalRow W ⟶ (strictDiagramFunctor Q).obj (originalRow W))
    (X : C) (d : ℤ) :
    colimit (Telescope.stageStableDiagram (stages Q (originalRow W) X)
      (steps Q (originalRow W) η X) d) ≅
      stableHomotopyGroup (Telescope.prespectrum (stages Q (originalRow W) X)
        (steps Q (originalRow W) η X)) d := by
  let : ∀ Y n, T1Space (((originalRow W).obj Y).space n) :=
    fun Y n ↦ Waldhausen.IteratedS.prespectrumSpaceT1Space (W.obj Y) n
  exact stableIso Q (originalRow W) η X d

end WaldhausenRow

section Fibers

variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C) (k : ℕ)

example (z : unitInterval × A.space k) :
    HomotopyPushout.cylinder f g k z = HomotopyPushout.point f g k ↔
      z.2 = A.point k ∨ z.1 = 0 ∧ f.map k z.2 = B.point k ∨
        z.1 = 1 ∧ g.map k z.2 = C.point k :=
  HomotopyPushout.cylinder_eq_point_iff f g k z

example (z : unitInterval × A.space k) (y : B.space k) (hy : y ≠ B.point k) :
    HomotopyPushout.cylinder f g k z = HomotopyPushout.left f g k y ↔
      z.1 = 0 ∧ f.map k z.2 = y := HomotopyPushout.cylinder_eq_left_iff f g k z y hy

example (z : unitInterval × A.space k) (y : C.space k) (hy : y ≠ C.point k) :
    HomotopyPushout.cylinder f g k z = HomotopyPushout.right f g k y ↔
      z.1 = 1 ∧ g.map k z.2 = y := HomotopyPushout.cylinder_eq_right_iff f g k z y hy

example (z : unitInterval × A.space k) :
    ReducedMappingCone.cylinder (A.point k) (B.point k) (f.map k) z =
        ReducedMappingCone.point (A.point k) (B.point k) (f.map k) ↔
      z.2 = A.point k ∨ z.1 = 1 ∨ z.1 = 0 ∧ f.map k z.2 = B.point k :=
  ReducedMappingCone.cylinder_eq_point_iff _ _ _ (f.map_point k) z

example (z : unitInterval × A.space k) (y : B.space k) (hy : y ≠ B.point k) :
    ReducedMappingCone.cylinder (A.point k) (B.point k) (f.map k) z =
        ReducedMappingCone.inr (A.point k) (B.point k) (f.map k) y ↔
      z.1 = 0 ∧ f.map k z.2 = y :=
  ReducedMappingCone.cylinder_eq_inr_iff _ _ _ (f.map_point k) z y hy

example (s t : unitInterval) (x : A.space k) :
    (mappingCone f).structureMap k
        (ReducedMappingCone.cylinder (A.point k) (B.point k) (f.map k) (s, x)) t =
      ReducedMappingCone.cylinder (A.point (k + 1)) (B.point (k + 1)) (f.map (k + 1))
        (s, A.structureMap k x t) := rfl

example (γ : Path (A.point k) (A.point k)) (r t : unitInterval) :
    Path.toContinuousMap ((parameterLooping A).structureMap k γ t) r =
      A.structureMap k (γ r) t := rfl

end Fibers

abbrev boolPrespectrum : LoopPrespectrum where
  space _ := TopCat.of Bool
  point _ := false
  structureMap _ := ContinuousMap.const _ (Path.refl false)
  map_point _ := rfl

abbrev collapse : boolPrespectrum ⟶ boolPrespectrum := zeroHom _ _

example (k : ℕ) : ¬ Function.Injective (collapse.map k) := by
  intro h
  have : (true : Bool) = false := h rfl
  cases this

example (k : ℕ) : HomotopyPushout.cylinder collapse collapse k (0, true) =
    HomotopyPushout.point collapse collapse k :=
  (HomotopyPushout.cylinder_eq_point_iff collapse collapse k (0, true)).mpr
    (Or.inr (Or.inl ⟨rfl, rfl⟩))

example (k : ℕ) : HomotopyPushout.cylinder collapse collapse k (1, true) =
    HomotopyPushout.point collapse collapse k :=
  (HomotopyPushout.cylinder_eq_point_iff collapse collapse k (1, true)).mpr
    (Or.inr (Or.inr ⟨rfl, rfl⟩))

example (k : ℕ) : ReducedMappingCone.cylinder false false (collapse.map k) (0, true) =
    ReducedMappingCone.point false false (collapse.map k) :=
  (ReducedMappingCone.cylinder_eq_point_iff false false (collapse.map k) rfl (0, true)).mpr
    (Or.inr (Or.inr ⟨rfl, rfl⟩))

example (k : ℕ) : T1Space ((HomotopyPushout.prespectrum collapse collapse).space k) :=
  inferInstance

example (k : ℕ) : T1Space ((parameterLooping (mappingCone collapse)).space k) := inferInstance

end ColibTest.BassTowerSeparation
