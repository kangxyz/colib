/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightPairColumnCoefficient

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence TopologicalSpace
open scoped BigOperators TensorProduct

universe u

open Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceTripleIncidence f g h i z w v) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    let RY := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
    let α := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    ∀ (t : List RY)
      (_hkt : IdealSheafData.stalk (pullback.diagonal g).ker
        (correspondenceSixfoldFirstMiddlePair f g h i p) = Ideal.ofList t),
      IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList (t.map α) :=
  correspondenceActualFirstMiddleList_ideal (K := K) f g h i z w v x

example
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
          (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n)).homology b) :=
  length_rightCommonKoszul_eq_originalPairTor (K := K) f g h i z w v x

example
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
          (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n) :=
  seqEuler_rightCommonKoszul_eq_originalPairTor (K := K) f g h i z w v x

example
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
    ∀ (t : List RY) (s : List RZ) (_ht : IsRegular RY t) (_hs : IsRegular RZ s)
      (_hY : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList (t.map α))
      (_hZ : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map β)),
      (∑ᶠ n : ℕ, letI := correspondenceIncidenceTorModule g h i w v (π q) n
        (-1 : ℤ) ^ n * Koszul.seqEuler (fun j => κ ((t.map α).get j))
          (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length A (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat : ℤ) :=
  finsum_actualLastPair_remainingEuler_eq_combinedTor (K := K) f g h i z w v x

example
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
    ∀ (t : List RY) (_ht : IsRegular RY t)
      (_hkt : IdealSheafData.stalk (pullback.diagonal g).ker
        (correspondenceSixfoldFirstMiddlePair f g h i p) = Ideal.ofList t),
      (∑ᶠ n : ℕ, letI := correspondenceIncidenceTorModule g h i w v (π q) n
        (-1 : ℤ) ^ n * Koszul.seqEuler (fun j => κ ((t.map α).get j))
          (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length A (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat : ℤ) :=
  finsum_actualLastPair_originalRemainingEuler_eq_tripleTor (K := K) f g h i z w v x
