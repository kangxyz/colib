/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFirstCoefficientEuler

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
  [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h] [IsSeparated i]

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g)]
      [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g))]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)) = Ideal.span (Set.range s)) :
    let E := correspondenceRightIntermediateSupportProduct f g h i z w v
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let I₀ := correspondenceIncidence g h i w v
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    let := (finite_genericPoints_correspondenceIncidence_of_smooth g h i w v hv).fintype
    (∑ t : genericPoints I₀,
      (correspondenceIncidenceTorCoefficient K g h i w v t *
        ((correspondenceIncidenceMap g h i w v).residueDegree t.1 : ℤ)) *
          Koszul.seqEuler (fun j => α (s j))
            (correspondenceRightRemainingImageComponentStalk f g h i z w v x t.1)) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        ∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          (correspondenceIncidenceTorCoefficient K g h i w v
            (correspondenceRightExteriorGenericLabel f g h i z w v η.1) *
              (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
            ((q').residueDegree η.1.1 : ℤ) *
              Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal)  := by
  exact sum_firstTorCoefficient_mul_seqEuler_correspondenceRightRemainingImageComponentStalk
    K f g h i z w v x hw hv hx s hs

end Stacks.Chow
