/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightColumnCombinedEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageCommonMiddleList
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# Original G,H Tor with the original remaining Y list computes common triple Tor

The coefficient in every degree is the actual full tensor pullback of original G,H Tor to
its genuine right-stage stalk. The accepted right-stage-linear common-Z Koszul comparison
identifies every remaining Y-homology length and Euler characteristic. The preceding right
signed-column theorem therefore computes exactly the original combined-diagonal triple Tor.

The terminal statement takes only the original remaining Y list and its actual regular
original diagonal presentation. Its extension ideal is proved from the native Cartesian
kernel and stalk-comap theorem. Smoothness chooses a common Z list internally; the input Y
list is never replaced. No coefficient model, scalar map, comparison equality, support
condition, reversed correspondence, or reversed admissibility is introduced. Flatness of
the first support over the original field is provided by the native field-target instance.

References: Stacks 01PB (ideal pullback), 0AZT (Tor), 0B1L (local signed associativity).
Independent source context: motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean,
blob 5771cc85d24a32f3610872f2a94d457154d1673b. This is only a local right coefficient theorem;
global finite-image localization and the weighted right-cycle equality remain separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence TopologicalSpace
open scoped BigOperators TensorProduct

universe u

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

omit [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated h] in
/-- The original Y ideal extends along the actual common first-middle stalk map. -/
theorem correspondenceActualFirstMiddleList_ideal
    (x : correspondenceTripleIncidence f g h i z w v) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    let RY := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
    let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    ∀ (t : List RY)
      (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
        (correspondenceSixfoldFirstMiddlePair f g h i p) = Ideal.ofList t),
      IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList (t.map α) := by
  dsimp only
  intro t hkt
  rw [ker_correspondenceFirstDiagonal, IdealSheafData.stalk_comap, hkt, Ideal.map_ofList]

omit [Smooth h] [IsSeparated g] in
/-- Actual original last-pair Tor has precisely the same remaining homology length,
linearly over the actual full right-stage ring in every pair of homological degrees. -/
theorem length_rightCommonKoszul_eq_originalPairTor
    (x : correspondenceTripleIncidence f g h i z w v) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    let q := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
    let RZ := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
    let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
    ∀ (s : List RZ) (hs : IsRegular RZ s)
      (hZ : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map β)) (n : ℕ),
      let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hZ
      letI := correspondenceIncidenceTorModule g h i w v (π q) n
      letI : Algebra P₀ P := ((π).stalkMap q).hom.toAlgebra
      ∀ {r : ℕ} (a : Fin r → P) (b : ℕ),
        Module.length P ((Koszul.seqComplexTensor a
          (correspondenceRightRemainingFirstKoszulModule
            f g h i z w v x (s.map β) hreg.1 hreg.2 n)).homology b) =
        Module.length P ((Koszul.seqComplexTensor a
          (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n)).homology b) := by
  dsimp only
  intro s hs hZ n r a b
  let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
  let q := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
  let π := correspondenceRightExteriorProjection f g h i z w v
  let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
  let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
  let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
  let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hZ
  let := correspondenceTripleIncidenceRightFirstKoszulModule
    f g h i z w v x (s.map β) hreg.1 hreg.2 n
  let := correspondenceIncidenceTorModule g h i w v (π q) n
  let : Algebra P₀ P := ((π).stalkMap q).hom.toAlgebra
  let : Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g) := inferInstance
  let e := correspondenceTripleIncidenceRightCommonKoszulIsoOriginalPairTor
    f g h i z w v x s hs hZ n
  exact (Koszul.homologyTensorCongr a e b).toLinearEquiv.length_eq

omit [Smooth h] [IsSeparated g] in
/-- Every remaining-list Euler term is the Euler of the actual original G,H Tor pullback. -/
theorem seqEuler_rightCommonKoszul_eq_originalPairTor
    (x : correspondenceTripleIncidence f g h i z w v) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    let q := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
    let RZ := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
    let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
    ∀ (s : List RZ) (hs : IsRegular RZ s)
      (hZ : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map β)) (n : ℕ),
      let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hZ
      letI := correspondenceIncidenceTorModule g h i w v (π q) n
      letI : Algebra P₀ P := ((π).stalkMap q).hom.toAlgebra
      ∀ {r : ℕ} (a : Fin r → P),
        Koszul.seqEuler a (correspondenceRightRemainingFirstKoszulModule
          f g h i z w v x (s.map β) hreg.1 hreg.2 n) =
        Koszul.seqEuler a
          (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n) := by
  dsimp only
  intro s hs hZ n r a
  let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
  let q := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
  let π := correspondenceRightExteriorProjection f g h i z w v
  let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
  let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
  let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
  let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hZ
  let := correspondenceTripleIncidenceRightFirstKoszulModule
    f g h i z w v x (s.map β) hreg.1 hreg.2 n
  let := correspondenceIncidenceTorModule g h i w v (π q) n
  let : Algebra P₀ P := ((π).stalkMap q).hom.toAlgebra
  unfold Koszul.seqEuler
  apply Finset.sum_congr rfl
  intro b _
  rw [length_rightCommonKoszul_eq_originalPairTor K f g h i z w v x s hs hZ n a b]

/-- All signed original G,H Tor columns, with unchanged original Y/Z lists, compute the
same literal common triple-Tor coefficient. No coefficient comparison is assumed. -/
theorem finsum_actualLastPair_remainingEuler_eq_combinedTor
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let q := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x.1
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
    let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let RY := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
    let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
    letI : Algebra P₀ P := ((π).stalkMap q).hom.toAlgebra
    let RZ := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
    let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
    ∀ (t : List RY) (s : List RZ) (ht : IsRegular RY t) (hs : IsRegular RZ s)
      (hY : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList (t.map α))
      (hZ : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map β)),
      (∑ᶠ n : ℕ, letI := correspondenceIncidenceTorModule g h i w v (π q) n
        (-1 : ℤ) ^ n * Koszul.seqEuler (fun j => κ ((t.map α).get j))
          (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length A (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat : ℤ) := by
  dsimp only
  intro t s ht hs hY hZ
  let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
  let q := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x.1
  let π := correspondenceRightExteriorProjection f g h i z w v
  let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
  let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
  let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
  let β := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
  let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
  let : Algebra P₀ P := ((π).stalkMap q).hom.toAlgebra
  let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x.1 s hs hZ
  let H := fun n => correspondenceRightRemainingFirstKoszulModule
    f g h i z w v x.1 (s.map β) hreg.1 hreg.2 n
  calc
    _ = ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        Koszul.seqEuler (fun j => κ ((t.map α).get j)) (H n) := by
      apply finsum_congr
      intro n
      let := correspondenceIncidenceTorModule g h i w v (π q) n
      exact congrArg (fun a : ℤ => (-1 : ℤ) ^ n * a)
        (seqEuler_rightCommonKoszul_eq_originalPairTor
          K f g h i z w v x.1 s hs hZ n (fun j => κ ((t.map α).get j))).symm
    _ = _ := finsum_originalMiddleLists_rightEuler_eq_combinedTor
      K f g h i z w v x t s ht hs hY hZ

/-- The original remaining Y list alone computes the actual triple coefficient from actual
G,H Tor. Smoothness supplies a Z list internally without changing the input ordered Y list. -/
theorem finsum_actualLastPair_originalRemainingEuler_eq_tripleTor
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let q := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x.1
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
    let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let RY := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
    let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
    letI : Algebra P₀ P := ((π).stalkMap q).hom.toAlgebra
    ∀ (t : List RY) (ht : IsRegular RY t)
      (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
        (correspondenceSixfoldFirstMiddlePair f g h i p) = Ideal.ofList t),
      (∑ᶠ n : ℕ, letI := correspondenceIncidenceTorModule g h i w v (π q) n
        (-1 : ℤ) ^ n * Koszul.seqEuler (fun j => κ ((t.map α).get j))
          (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length A (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat : ℤ) := by
  dsimp only
  intro t ht hkt
  obtain ⟨t₀, s, ht₀, hs, hY₀, hZ⟩ := exists_correspondenceOriginalMiddleLists f g h i
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1)
  have hY := correspondenceActualFirstMiddleList_ideal K f g h i z w v x.1 t hkt
  exact finsum_actualLastPair_remainingEuler_eq_combinedTor
    K f g h i z w v x t s ht hs hY hZ

end Stacks.Chow
