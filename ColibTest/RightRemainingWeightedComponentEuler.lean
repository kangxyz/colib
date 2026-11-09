/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingWeightedComponentEuler

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) (hv :
    IsFiniteCorrespondencePoint h i v)

include hz hw hv

example
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g)]
      [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g))] {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) = Ideal.span (Set.range
        s)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ t : genericPoints (correspondenceIncidence g h i w v),
        (correspondenceIncidenceTorCoefficient K g h i w v t *
          ((correspondenceIncidenceMap g h i w v).residueDegree t.1 : ℤ)) *
            Koszul.seqEuler (fun j => α (s j))
              (correspondenceRightRemainingImageComponentStalk f g h i z w v x.1 t.1)  := by
  exact finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_weightedComponents
    K f g h i z w v hz hw hv x s hs

end Stacks.Chow
