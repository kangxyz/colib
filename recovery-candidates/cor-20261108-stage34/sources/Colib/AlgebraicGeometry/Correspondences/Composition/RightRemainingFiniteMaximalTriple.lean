/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorStalkEuler
public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteOriginalPairEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteGenericFibre
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightPairColumnCoefficient

/-!
# Every actual right maximal-localization Euler is the same original triple Tor

The original image-stalk Y list is transported entry by entry along actual equal middle
points. The real section-germ scalar square and actual original G,H Tor-sheaf comparison
identify each localized coefficient with the existing original right signed column.
That column already equals the original sixfold triple Tor by the native local comparison.
All maximal labels come from the full actual finite algebra; none is supplied by a caller.

Only an original regular Y presentation is input. The Z list used inside the existing
right-column supplier is independently chosen there on the original Z self-product.
No comparison, scalar action, finite length, cutoff or additional dimension is a premise.
This is the local maximal coefficient join, not the image-component weighted replacement.
References: Stacks 0098, 0AZT and arbitrary-ring local 0B1L; motivic
 a6805c4a87cdfd7717dd7a94039246a167f15380, RightFirstStageWeightedRemainingCoefficient.lean.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

private theorem right_regular_stalkCongr {T : Scheme.{u}} {a b : T} (hab : a = b)
    {r : ℕ} (s : Fin r → T.presheaf.stalk a)
    (hs : IsRegular (T.presheaf.stalk a) (List.ofFn s)) :
    IsRegular (T.presheaf.stalk b)
      (List.ofFn (fun j => (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom (s j))) := by
  subst b
  simpa [TopCat.Presheaf.stalkCongr] using hs

private theorem right_ideal_stalkCongr {T : Scheme.{u}} (I : T.IdealSheafData)
    {a b : T} (hab : a = b) {r : ℕ} (s : Fin r → T.presheaf.stalk a)
    (hs : IdealSheafData.stalk I a = Ideal.span (Set.range s)) :
    IdealSheafData.stalk I b = Ideal.span
      (Set.range (fun j => (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom (s j))) := by
  subst b
  simpa [TopCat.Presheaf.stalkCongr] using hs

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)

include hw hv

/-- Actual tensor-localization Euler equals original triple Tor at the same maximal label. -/
theorem finsum_signed_correspondenceRightRemainingFiniteMaximalEuler_eq_tripleTor
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    (p : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x.1)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let A := (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    let y := (correspondenceRightRemainingFiniteMaximalEquivGenericTriple
      f g h i z w v hw hv x.1 x.2 p).1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    ∀ {r : ℕ} (s : Fin r → A) (hsr : IsRegular A (List.ofFn s))
      (hs : IdealSheafData.stalk (pullback.diagonal g).ker
        (correspondenceRightImageMiddlePair f g h i z w v
          (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
            Ideal.span (Set.range s)),
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Koszul.seqEuler
        (fun j => algebraMap B (Localization.AtPrime p.asIdeal)
          (algebraMap R B (α (s j))))
        (Localization.AtPrime p.asIdeal ⊗[B] M n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v y.1)
            (correspondenceTripleIncidenceTor f g h i z w v y.1 n)).toNat : ℤ) := by
  dsimp only
  intro r s hsr hs
  let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x.1
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x.1
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient g h i) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceIntersectionAmbientToField K g h i)
  let q := (correspondenceRightRemainingFiniteClosedEquivMaximal
    f g h i z w v x.1 hw hv).symm p
  let y := (correspondenceRightRemainingFiniteMaximalEquivGenericTriple
    f g h i z w v hw hv x.1 x.2 p).1
  have hy : correspondenceTripleToRightImageIncidence f g h i z w v y.1 = x.1 :=
    (correspondenceRightRemainingFiniteMaximalEquivGenericTriple
      f g h i z w v hw hv x.1 x.2 p).2
  have hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y.1 =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x.1 q.1 :=
    correspondenceRightRemainingFiniteMaximalEquivTriple_projection
      f g h i z w v x.1 hw hv p
  have hprime : ((isAffineOpen_top E).primeIdealOf ⟨q.1, trivial⟩).asIdeal = p.asIdeal := by
    rw [(isAffineOpen_top E).primeIdealOf_eq_map_closedPoint]
    exact (correspondenceRightRemainingFiniteMaximalEquivTriple_germPrime
      f g h i z w v x.1 hw hv p).symm
  let eY := (pullback g g).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x.1 y.1 hy))
  let sY := fun j => eY.hom (s j)
  have hsY := right_regular_stalkCongr
    (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x.1 y.1 hy) s hsr
  have hksY := right_ideal_stalkCongr (pullback.diagonal g).ker
    (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x.1 y.1 hy) s hs
  let a₀ := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y.1
  let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk a₀
  let π := correspondenceRightExteriorProjection f g h i z w v
  let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π a₀)
  let : Algebra P₀ P := (π.stalkMap a₀).hom.toAlgebra
  let sP := fun j => correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v y.1
    ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y.1) (sY j))
  have hlocal (n : ℕ) :
      letI := correspondenceIncidenceTorModule g h i w v (π a₀) n
      Koszul.seqEuler
        (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (algebraMap R B (α (s j))))
        (Localization.AtPrime p.asIdeal ⊗[B] M n) =
          Koszul.seqEuler sP
            (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π a₀) n) := by
    let := correspondenceIncidenceTorModule g h i w v (π a₀) n
    let := stalkModule (correspondenceRightRemainingFiniteTorSheaf f g h i z w v x.1 n) q.1
    have h₁ := seqEuler_correspondenceRightRemainingFiniteTorTensor_eq_stalk
      f g h i z w v hw hv x.1 q.1 n (fun j => algebraMap R B (α (s j)))
    dsimp only at h₁
    rw [hprime] at h₁
    have h₂ := seqEuler_correspondenceRightRemainingFiniteTorStalk_eq_originalPair
      f g h i z w v x.1 q.1 q.2 y.1 hy hρ n sY
    dsimp only at h₂
    have h₂' :
        Koszul.seqEuler (fun j => E.presheaf.germ ⊤ q.1 trivial
          (algebraMap R B (α (s j))))
          ((correspondenceRightRemainingFiniteTorSheaf f g h i z w v x.1 n).presheaf.stalk q.1) =
            Koszul.seqEuler sP
              (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π a₀) n) := by
      simpa only [sY, Iso.hom_inv_id_apply] using h₂
    exact h₁.trans h₂'
  calc
    _ = ∑ᶠ n : ℕ, letI := correspondenceIncidenceTorModule g h i w v (π a₀) n
        (-1 : ℤ) ^ n * Koszul.seqEuler sP
          (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π a₀) n) := by
      apply finsum_congr
      intro n
      let := correspondenceIncidenceTorModule g h i w v (π a₀) n
      dsimp only
      rw [hlocal]
    _ = _ := by
      have hk : IdealSheafData.stalk (pullback.diagonal g).ker
          (correspondenceSixfoldFirstMiddlePair f g h i
            (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y.1)) =
          Ideal.ofList (List.ofFn sY) := by
        simpa only [Ideal.ofList_ofFn] using hksY
      simpa only [List.map_ofFn, List.length_ofFn, List.get_ofFn, Fin.cast_eq_self] using
        (finsum_actualLastPair_originalRemainingEuler_eq_tripleTor
          K f g h i z w v y (List.ofFn sY) hsY hk)

end Stacks.Chow
