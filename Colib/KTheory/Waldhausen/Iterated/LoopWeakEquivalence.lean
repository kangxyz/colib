/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.RelativeCylinder
public import Colib.KTheory.Waldhausen.Iterated.LoopMap
public import Colib.KTheory.Waldhausen.Iterated.OmegaSpectrum
public import Colib.KTheory.Waldhausen.Fibration.AllWeak.TotalFiberSquare
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.WeakTotalFiber
public import Colib.Topology.HomotopyFiber.CylinderComparison
public import Colib.Topology.HomotopyFiber.Homeomorph
public import Colib.Topology.HomotopyFiber.Congruence
public import Colib.Topology.Realization.HomotopySquare

/-!
# The original relative comparison and degree-raising equivalence

Adapted from `Quillen/Waldhausen/SConstruction/Iterated/LoopWeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual lifted
cylinder, full realized square, relative projection, fiber homeomorphism and
original degree-raising homomorphism are retained.

The existing `stageLoopMap_weak` theorem already proves complete weakness of
the first loop map by `stageLoopMap_zero`. It is reused on the native
`SmallWaldhausenCategory` containing the original category itself. No new
first-loop weak-equivalence alias, alternative model or small-model transport
is introduced. The equivalence below has exactly `degreeRaisingMap` as its
forward homomorphism and needs only the original small-category assumptions.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory SSet Topology
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open Fibration Fibration.RelativeRows SmallWaldhausenCategory
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The original relative tail with the actual all-acyclic witness-forgetting map. -/
def relativeProjection : C(|SSet.diagonalSSet (relativeSRows (AllWeak.nested W))|,
    doubleDelooping W) :=
  (AllWeak.ordinaryTotalInclusionMap W).comp (totalTailMap (AllWeak.nested W))

lemma relativeProjection_eq : relativeProjection W = (SSet.toTop.map (relativeTail W)).hom := by
  simp only [relativeProjection, relativeTail, CategoryTheory.Functor.map_comp, TopCat.hom_comp]
  rfl

lemma relativeProjection_point : relativeProjection W (totalBasepoint (AllWeak.nested W)) =
    doubleBasepoint W := by
  change AllWeak.ordinaryTotalInclusionMap W
    (totalTailMap (AllWeak.nested W) (totalBasepoint (AllWeak.nested W))) = _
  rw [totalTailMap_basepoint, AllWeak.ordinaryTotalInclusionMap_basepoint]
  rfl

lemma relativeProjection_fiberInclusion (x : W.Delooping) :
    relativeProjection W (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W)) x) =
      doubleBasepoint W := by
  change AllWeak.ordinaryTotalInclusionMap W
    (totalTailMap (AllWeak.nested W) (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))
      x)) = _
  rw [totalTailMap_totalFiberInclusion, AllWeak.ordinaryTotalInclusionMap_basepoint]
  rfl

/-- The realized literal lift runs from the actual relative zero to the original fiber inclusion. -/
def relativeTopHomotopy :
    (ContinuousMap.const W.Delooping (totalBasepoint (AllWeak.nested W))).Homotopy
      (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom where
  toContinuousMap := (realizationSimplicialHomotopy (relativeHomotopy W)).toContinuousMap
  map_zero_left x := ((realizationSimplicialHomotopy (relativeHomotopy W)).apply_zero x).trans
    (realization_const_apply _ x)
  map_one_left x := (realizationSimplicialHomotopy (relativeHomotopy W)).apply_one x

/-- The exact realized square commutes for every original point and time. -/
lemma relativeTopHomotopy_tail (t : unitInterval) (x : W.Delooping) :
    relativeProjection W (relativeTopHomotopy W (t, x)) =
      realizationSimplicialHomotopy (suspensionHomotopy W) (t, x) := by
  change relativeProjection W (realizationSimplicialHomotopy (relativeHomotopy W) (t, x)) = _
  rw [relativeProjection_eq]
  have h := realizationSimplicialHomotopy_square (relativeHomotopy W) (suspensionHomotopy W)
    (𝟙 _) (relativeTail W) (by
      change relativeCylinder W ≫ relativeTail W = (𝟙 _ ▷ Δ[1]) ≫ suspensionCylinder W
      simpa using relativeCylinder_tail W) t x
  simp only [CategoryTheory.Functor.map_id, TopCat.id_app] at h
  exact h

lemma cylinderLoop_eq_loopStructureMap :
    HomotopyFiber.cylinderLoop (relativeProjection W) (doubleBasepoint W)
      (totalBasepoint (AllWeak.nested W)) (relativeProjection_point W)
      (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
      (relativeProjection_fiberInclusion W) (relativeTopHomotopy W) = loopStructureMap W := by
  ext x t
  exact relativeTopHomotopy_tail W t x

/-- The target-coordinate homeomorphism retains the original full fiber path. -/
def relativeFiberHomeomorph :
    HomotopyFiber (totalTailMap (AllWeak.nested W))
      (ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested W))) ≃ₜ
        HomotopyFiber (relativeProjection W) (doubleBasepoint W) :=
  (HomotopyFiber.homeomorphOfSquare (totalTailMap (AllWeak.nested W)) (relativeProjection W)
    (Homeomorph.refl _) (AllWeak.ordinaryTotalHomeomorph W) rfl _).trans
      (HomotopyFiber.congrHomeomorph rfl (AllWeak.ordinaryTotalInclusionMap_basepoint W))

/-- The source coordinate is not changed by the target-coordinate homeomorphism. -/
@[simp] lemma relativeFiberHomeomorph_source
    (z : HomotopyFiber (totalTailMap (AllWeak.nested W))
      (ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested W)))) :
    (relativeFiberHomeomorph W z).1.1 = z.1.1 := rfl

/-- The entire path is postcomposed with the original witness-forgetting map. -/
@[simp] lemma relativeFiberHomeomorph_path
    (z : HomotopyFiber (totalTailMap (AllWeak.nested W))
      (ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested W)))) :
    (relativeFiberHomeomorph W z).1.2 = (AllWeak.ordinaryTotalInclusionMap W).comp z.1.2 := rfl

lemma relativeFiberHomeomorph_comparison :
    (relativeFiberHomeomorph W : C(_, _)).comp (totalTailFiberComparison (AllWeak.nested W)) =
      HomotopyFiber.cylinderStrictLift (relativeProjection W) (doubleBasepoint W)
        (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
        (relativeProjection_fiberInclusion W) := by
  ext x : 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · ext t
    exact AllWeak.ordinaryTotalInclusionMap_basepoint W

lemma relativeStrictComparison_weak :
    IsWeakHomotopyEquivalence
      (HomotopyFiber.cylinderStrictLift (relativeProjection W) (doubleBasepoint W)
        (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
        (relativeProjection_fiberInclusion W)) := by
  rw [← relativeFiberHomeomorph_comparison]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv
    (relativeFiberHomeomorph W).toHomotopyEquiv).comp
      (totalTailFiberComparison_isWeakHomotopyEquivalence (AllWeak.nested W))

/-- The original based loop map is bijective in every degree, including components. -/
theorem loopStructureMap_bijective (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (loopStructureMap W)
      (loopStructureMap_basepoint W)) := by
  let B : WideSubcategory preservesZero.{u} := ⟨{ Obj := C, waldhausen := W }⟩
  have hw : IsWeakHomotopyEquivalence (loopStructureMap W) := by
    simpa only [stageLoopMap_zero] using stageLoopMap_weak 0 B
  have h : ∀ (y : Path (doubleBasepoint W) (doubleBasepoint W))
      (hy : loopStructureMap W W.kBasepoint = y),
      Function.Bijective (HomotopyGroup.map (N := Fin n) (loopStructureMap W) hy) := by
    intro y hy
    cases hy
    exact hw.homotopy_bijective W.kBasepoint n
  exact h _ (loopStructureMap_basepoint W)

/-- The unchanged degree-raising homomorphism is bijective on the original K-groups. -/
theorem degreeRaisingMap_bijective (n : ℕ) : Function.Bijective (degreeRaisingMap W n) :=
  (loopShiftMulEquiv n).symm.bijective.comp (loopStructureMap_bijective W (n + 1))

/-- The actual K-group comparison retains the original degree-raising forward map. -/
def degreeRaisingEquiv (n : ℕ) :
    W.K n ≃* HomotopyGroup.Pi (n + 2) (doubleDelooping W) (doubleBasepoint W) :=
  MulEquiv.ofBijective (degreeRaisingMap W n) (degreeRaisingMap_bijective W n)

/-- The equivalence has the exact original forward homomorphism. -/
lemma degreeRaisingEquiv_toMonoidHom (n : ℕ) :
    (degreeRaisingEquiv W n).toMonoidHom = degreeRaisingMap W n := rfl

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0282",
  colib_ref "Waldhausen1985" "Section 1.5, Proposition 1.5.3 and following paragraph, p. 342"
    "ingredient" "The original loop equivalence induces this unchanged degree-raising map"]
  CategoryTheory.Waldhausen.IteratedS.degreeRaisingEquiv

attribute [colib_tag "COL-0282"]
  CategoryTheory.Waldhausen.IteratedS.degreeRaisingMap_bijective
