/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplit

/-! The original left-associated endpoints of the actual total and geometric split routes. -/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem ofLevels_map
    {X Y : LoopPrespectrum.{u}} {f g f' g' : X ⟶ Y}
    {H K : Homotopy f g} (J : H.RelHomotopy K)
    (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n)
    (n : ℕ) :
    ((J.ofLevels H' K' hH hK).level n).toContinuousMap =
      (J.level n).toContinuousMap := by
  rfl

/-- The unchanged total route with the original left-associated target. -/
def boundedAboveFlatAffineEvaluationCompTotalLeftHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Homotopy (boundedAboveFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap T)
      ((boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        prespectrumMap (boundedAboveFlatAffinePullbackModelMap f)) ≫
          prespectrumMap (boundedAboveFlatAffinePullbackModelMap g)) :=
  (boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).cast rfl
    (Category.assoc _ _ _).symm

/-- The unchanged geometric split route with the original left-associated target. -/
def boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Homotopy (boundedAboveFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap T)
      ((boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        prespectrumMap (boundedAboveFlatAffinePullbackModelMap f)) ≫
          prespectrumMap (boundedAboveFlatAffinePullbackModelMap g)) :=
  (boundedAboveFlatAffineEvaluationCompSplitHomotopy f g).cast rfl
    (Category.assoc _ _ _).symm

/-- Both source tracks retain every level under the common association transport. -/
theorem boundedAboveFlatAffineEvaluationCompTotalLeftHomotopy_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    (boundedAboveFlatAffineEvaluationCompTotalLeftHomotopy f g).level n =
      (boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).level n :=
  Homotopy.cast_level _ _ _ n

/-- The geometric split retains every level under the common association transport. -/
theorem boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy f g).level n =
      (boundedAboveFlatAffineEvaluationCompSplitHomotopy f g).level n :=
  Homotopy.cast_level _ _ _ n

/-- The entire relative comparison with the original literal endpoints. -/
@[no_expose]
def boundedAboveFlatAffineEvaluationCompTotalSplitLeft
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineEvaluationCompTotalLeftHomotopy f g).RelHomotopy
      (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy f g) :=
  (boundedAboveFlatAffineEvaluationCompTotalSplit f g).ofLevels _ _
    (boundedAboveFlatAffineEvaluationCompTotalLeftHomotopy_level f g)
    (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy_level f g)

/-- Association changes neither the comparison coordinate nor the entire two-time map. -/
theorem boundedAboveFlatAffineEvaluationCompTotalSplitLeft_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    ((boundedAboveFlatAffineEvaluationCompTotalSplitLeft f g).level n).toContinuousMap =
      ((boundedAboveFlatAffineEvaluationCompTotalSplit f g).level n).toContinuousMap := by
  exact ofLevels_map (boundedAboveFlatAffineEvaluationCompTotalSplit f g) _ _ _ _ n

end AlgebraicGeometry.Scheme.Modules
