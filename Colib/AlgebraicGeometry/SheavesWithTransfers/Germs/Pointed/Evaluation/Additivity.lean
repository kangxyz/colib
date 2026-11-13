/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.Pointed.Lifts.Independence
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.Pointed.Lifts.Simultaneous

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Sheaf/Germs/Pointed/Evaluation/Additivity.lean`, blob
`00c7f76582e213299ef9553f24815f6ad267abf1`.
 # Additivity of actual original-germ evaluation for correspondence generators -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

include hP

/-- Additivity is proved on simultaneous actual finite witnesses, not imposed
on the chosen original-germ evaluation. -/
theorem generatorGermEvaluation_add
    (A : pullback (C := Scheme) X.hom Y.hom)
    (hA : IsFiniteCorrespondencePoint X.hom Y.hom A) (x : X.left)
    (a b : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    generatorGermEvaluation k P A hA x (a + b) =
      generatorGermEvaluation k P A hA x a + generatorGermEvaluation k P A hA x b := by
  obtain ⟨L, M, N, h⟩ := exists_additive_pointedGermLiftWitnesses k P A hA x a b
  rw [generatorGermEvaluation_eq_of_witness k P hP A hA x (a + b) N,
    generatorGermEvaluation_eq_of_witness k P hP A hA x a L,
    generatorGermEvaluation_eq_of_witness k P hP A hA x b M]
  exact h

/-- Zero follows from the proved addition identity in the original source fiber. -/
theorem generatorGermEvaluation_zero
    (A : pullback (C := Scheme) X.hom Y.hom)
    (hA : IsFiniteCorrespondencePoint X.hom Y.hom A) (x : X.left) :
    generatorGermEvaluation k P A hA x 0 = 0 := by
  have h := generatorGermEvaluation_add k P hP A hA x 0 0
  have h' : generatorGermEvaluation k P A hA x 0 + 0 =
      generatorGermEvaluation k P A hA x 0 + generatorGermEvaluation k P A hA x 0 := by
    simpa only [add_zero] using h
  exact (add_left_cancel h').symm

/-- The actual generator action on original germ tuples is an additive homomorphism.
No correspondence-composition or ordinary-cohomology transfer law is asserted here. -/
def generatorGermHom (A : pullback (C := Scheme) X.hom Y.hom)
    (hA : IsFiniteCorrespondencePoint X.hom Y.hom A) (x : X.left) :
    (∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) →+
      (SmoothSite.nisnevichPointFiberCocone X x F).pt where
  toFun := generatorGermEvaluation k P A hA x
  map_zero' := generatorGermEvaluation_zero k P hP A hA x
  map_add' := generatorGermEvaluation_add k P hP A hA x

end AlgebraicGeometry.PresheafWithTransfers
