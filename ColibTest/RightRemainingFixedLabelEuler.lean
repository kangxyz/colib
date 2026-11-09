/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFixedLabelEuler

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

open Classical in
example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    [IsSeparated g] [IsSeparated i] [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w
      v).imageι ≫ pullback.fst g i) ≫ g)] [LocallyOfFiniteType ((((integralComponentAt
      z).subschemeι ≫ pullback.snd f g) ≫ g))]
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
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let π := correspondenceRightExteriorProjection f g h i z w v
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    ((q).residueDegree t : ℤ) * Koszul.seqEuler (fun j => α (s j))
      (correspondenceRightRemainingImageComponentStalk f g h i z w v x t) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        (∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          if π η.1.1 = t then
            (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ) *
              ((q').residueDegree η.1.1 : ℤ)
          else 0) * Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal)  := by
  exact residueDegree_mul_seqEuler_correspondenceRightRemainingImageComponentStalk
    K f g h i z w v x t hw hv hx s hs

end Stacks.Chow
