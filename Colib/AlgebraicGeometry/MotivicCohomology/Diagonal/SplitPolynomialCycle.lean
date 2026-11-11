/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CubicBoundary
import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialProducts
import Mathlib.Tactic.FinCases

/-!
# The full split two-coordinate polynomial cycles

Native one-coordinate polynomial cycles add under multiplication. The unique
lift to the open where the complement is a unit keeps the same coefficients.
After the genuine two-coordinate map, a linear factor is the literal rational
pair graph, so repeated factors occur with their full multiplicities.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalSplitPolynomialCycle

open _root_.AlgebraicGeometry.Scheme SmoothSite
open DiagonalTopDegree DiagonalCycleSymbols DiagonalCubicBoundary PolynomialCurveCycles

variable {k : Type u} [Field k]

private theorem mul_constant_isUnit (p q : k[X])
    (hp : IsUnit (p.coeff 0)) (hq : IsUnit (q.coeff 0)) :
    IsUnit ((p * q).coeff 0) := by
  simpa only [coeff_zero_eq_eval_zero, eval_mul] using hp.mul hq

private theorem mul_eval_one_isUnit (p q : k[X])
    (hp : IsUnit (p.eval 1)) (hq : IsUnit (q.eval 1)) :
    IsUnit ((p * q).eval 1) := by
  simpa only [eval_mul] using hp.mul hq

/-- The whole two-coordinate point cycle of a product adds the original factors. -/
theorem pointCycle_mul (p q : k[X]) (hp : p.Monic) (hq : q.Monic)
    (hp0 : IsUnit (p.coeff 0)) (hq0 : IsUnit (q.coeff 0))
    (hp1 : IsUnit (p.eval 1)) (hq1 : IsUnit (q.eval 1))
    (h0 : IsUnit ((p * q).coeff 0)) (h1 : IsUnit ((p * q).eval 1)) :
    pointCycle k (p * q) (hp.mul hq) h0 h1 =
      pointCycle k p hp hp0 hp1 + pointCycle k q hq hq0 hq1 := by
  let f := 𝟙 (Spec (.of k))
  let a := openPolynomialCycle f p hp hp0 hp1
  let b := openPolynomialCycle f q hq hq0 hq1
  let c := openPolynomialCycle f (p * q) (hp.mul hq) h0 h1
  let j := (Cor.graphFunctor k).map (openInclusion k)
  have h : c = a + b := by
    apply openGraph_injective k (X := base (Spec (.of k))) (openInclusion k)
    change c ≫ j = (a + b) ≫ j
    rw [Preadditive.add_comp]
    exact (openPolynomialCycle_inclusion f (p * q) (hp.mul hq) h0 h1).trans
      ((NativeTorusPolynomial.polynomialCycle_mul f p q hp hq hp0 hq0).trans
        (congrArg₂ (· + ·) (openPolynomialCycle_inclusion f p hp hp0 hp1).symm
          (openPolynomialCycle_inclusion f q hq hq0 hq1).symm))
  let t := (Cor.graphFunctor k).map (pairMap k)
  change c ≫ t = a ≫ t + b ≫ t
  exact (congrArg (fun z => z ≫ t) h).trans (Preadditive.add_comp _ _ _ a b t)

private theorem linear_eval_one_isUnit (a b : kˣ) (h : (b : k) = 1 - (a : k)) :
    IsUnit ((Polynomial.X - C (a : k)).eval 1) := by
  rw [eval_sub, eval_X, eval_C, ← h]
  exact b.isUnit

private theorem complementEquation_rational (a b : kˣ) (h : (b : k) = 1 - (a : k)) :
    (NativeTorusPolynomial.smoothUnitPoint (𝟙 (Spec (.of k))) a).left.appTop
      (complementEquation k) = (specGlobalUnit b).val := by
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  apply e.injective
  have hc := congrArg Units.val (nativeAffineTorusPoint_coordinate (𝟙 (Spec (.of k))) a)
  change e ((NativeTorusPolynomial.smoothUnitPoint (𝟙 (Spec (.of k))) a).left.appTop
    (multiplicativeGroupBaseChangeCoordinate (Spec (.of k))).val) = (a : k) at hc
  have hb : e (specGlobalUnit b).val = (b : k) :=
    congrArg Units.val (specGlobalUnit_recover b)
  rw [complementEquation, map_sub, map_one, map_sub, map_one, hc, hb, h]

private theorem liftPoint_pair (a b : kˣ) (h : (b : k) = 1 - (a : k)) :
    liftPoint k (NativeTorusPolynomial.smoothUnitPoint (𝟙 (Spec (.of k))) a)
        (by rw [complementEquation_rational a b h]; exact (specGlobalUnit b).isUnit) ≫
      pairMap k = rationalTuple k 2 ![a, b] := by
  let f := NativeTorusPolynomial.smoothUnitPoint (𝟙 (Spec (.of k))) a
  have hu : IsUnit (f.left.appTop (complementEquation k)) := by
    change IsUnit ((NativeTorusPolynomial.smoothUnitPoint (𝟙 (Spec (.of k))) a).left.appTop _)
    rw [complementEquation_rational a b h]
    exact (specGlobalUnit b).isUnit
  let x := liftPoint k f hu
  have hfirst : x ≫ openInclusion k = f := liftPoint_inclusion k f hu
  have hover : x.left ≫ (complementObject k).hom = 𝟙 (Spec (.of k)) :=
    MorphismProperty.Over.w x
  have hval : Units.map x.left.appTop.hom.toMonoidHom (complementUnit k) = specGlobalUnit b := by
    apply Units.ext
    have hcomp := congrArg (fun g => g.left.appTop (complementEquation k)) hfirst
    change (x.left ≫ (openInclusion k).left).appTop (complementEquation k) =
      f.left.appTop (complementEquation k) at hcomp
    rw [Scheme.Hom.comp_appTop] at hcomp
    change x.left.appTop ((complementUnit k).val) = _
    rw [complementUnit_val]
    exact hcomp.trans (complementEquation_rational a b h)
  have hsecond : x ≫ complementCoordinate k =
      NativeTorusPolynomial.smoothUnitPoint (𝟙 (Spec (.of k))) b := by
    apply MorphismProperty.Over.Hom.ext
    have hs := nativeTorusPoint_comp_left (complementObject k).hom x.left (complementUnit k)
    let t : (Spec (.of k) ⟶ Spec (.of k)) → (Spec (.of k) ⟶ torusScheme k) :=
      fun g => (nativeTorusPoint g (specGlobalUnit b)).left
    have ht : (x.left ≫ (complementObject k).hom : Spec (.of k) ⟶ Spec (.of k)) =
        𝟙 (Spec (.of k)) := hover
    have he := congrArg t ht
    calc
      _ = (nativeTorusPoint (x.left ≫ (complementObject k).hom)
          (Units.map x.left.appTop.hom.toMonoidHom (complementUnit k))).left := hs.symm
      _ = (nativeTorusPoint (x.left ≫ (complementObject k).hom) (specGlobalUnit b)).left :=
        congrArg (fun v => (nativeTorusPoint (x.left ≫ (complementObject k).hom) v).left) hval
      _ = (nativeTorusPoint (𝟙 (Spec (.of k))) (specGlobalUnit b)).left := he
      _ = _ := rfl
  change x ≫ pairMap k = _
  apply torusPower_hom_ext
  intro i
  rw [Category.assoc, pairMap, torusPowerLift_coordinate, rationalTuple_coordinate]
  fin_cases i
  · exact hfirst
  · exact hsecond

/-- A linear polynomial with its complementary unit gives the literal pair graph. -/
theorem pointCycle_linear_graph (a b : kˣ) (hab : (b : k) = 1 - (a : k))
    (h0 : IsUnit ((Polynomial.X - C (a : k)).coeff 0))
    (h1 : IsUnit ((Polynomial.X - C (a : k)).eval 1)) :
    pointCycle k (Polynomial.X - C (a : k)) (monic_X_sub_C _) h0 h1 =
      (Cor.graphFunctor k).map (rationalTuple k 2 ![a, b]) := by
  let f := 𝟙 (Spec (.of k))
  let g := NativeTorusPolynomial.smoothUnitPoint f a
  have h : IsUnit (g.left.appTop (complementEquation k)) := by
    change IsUnit ((NativeTorusPolynomial.smoothUnitPoint (𝟙 (Spec (.of k))) a).left.appTop _)
    rw [complementEquation_rational a b hab]
    exact (specGlobalUnit b).isUnit
  let x := liftPoint k g h
  have hLift : openPolynomialCycle f (Polynomial.X - C (a : k)) (monic_X_sub_C _) h0 h1 =
      (Cor.graphFunctor k).map x := by
    apply openGraph_injective k (X := base (Spec (.of k))) (openInclusion k)
    change openPolynomialCycle f (Polynomial.X - C (a : k)) (monic_X_sub_C _) h0 h1 ≫
      (Cor.graphFunctor k).map (openInclusion k) =
        (Cor.graphFunctor k).map x ≫ (Cor.graphFunctor k).map (openInclusion k)
    calc
      _ = NativeTorusPolynomial.polynomialCycle f (Polynomial.X - C (a : k))
          (monic_X_sub_C _) h0 := openPolynomialCycle_inclusion f _ _ h0 h1
      _ = (Cor.graphFunctor k).map g :=
        (NativeTorusPolynomial.polynomialCycle_linear_graph f a
          (Cor.finite_genericPoints k (point k))).trans
            (NativeTorusPolynomial.graph_smoothUnitPoint f a).symm
      _ = (Cor.graphFunctor k).map (x ≫ openInclusion k) :=
        congrArg (fun y => (Cor.graphFunctor k).map y) (liftPoint_inclusion k g h).symm
      _ = _ := Functor.map_comp _ _ _
  change openPolynomialCycle f (Polynomial.X - C (a : k)) (monic_X_sub_C _) h0 h1 ≫
    (Cor.graphFunctor k).map (pairMap k) = _
  rw [hLift, ← Functor.map_comp]
  exact congrArg (fun y => (Cor.graphFunctor k).map y) (liftPoint_pair a b hab)

private theorem threeLinear_pointCycle (a a' b b' c c' : kˣ)
    (ha : (a' : k) = 1 - (a : k)) (hb : (b' : k) = 1 - (b : k))
    (hc : (c' : k) = 1 - (c : k))
    (p : k[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0)) (h1 : IsUnit (p.eval 1))
    (h : p = (Polynomial.X - C (a : k)) * (Polynomial.X - C (b : k)) *
      (Polynomial.X - C (c : k))) :
    pointCycle k p hp h0 h1 =
      (Cor.graphFunctor k).map (rationalTuple k 2 ![a, a']) +
      (Cor.graphFunctor k).map (rationalTuple k 2 ![b, b']) +
      (Cor.graphFunctor k).map (rationalTuple k 2 ![c, c']) := by
  subst p
  let A : k[X] := Polynomial.X - C (a : k)
  let B : k[X] := Polynomial.X - C (b : k)
  let D : k[X] := Polynomial.X - C (c : k)
  have hA : A.Monic := monic_X_sub_C _
  have hB : B.Monic := monic_X_sub_C _
  have hD : D.Monic := monic_X_sub_C _
  have hA0 : IsUnit (A.coeff 0) := NativeTorusPolynomial.linear_constant_isUnit a
  have hB0 : IsUnit (B.coeff 0) := NativeTorusPolynomial.linear_constant_isUnit b
  have hD0 : IsUnit (D.coeff 0) := NativeTorusPolynomial.linear_constant_isUnit c
  have hA1 : IsUnit (A.eval 1) := linear_eval_one_isUnit a a' ha
  have hB1 : IsUnit (B.eval 1) := linear_eval_one_isUnit b b' hb
  have hD1 : IsUnit (D.eval 1) := linear_eval_one_isUnit c c' hc
  have hAB0 := mul_constant_isUnit A B hA0 hB0
  have hAB1 := mul_eval_one_isUnit A B hA1 hB1
  calc
    _ = pointCycle k (A * B) (hA.mul hB) hAB0 hAB1 + pointCycle k D hD hD0 hD1 :=
      pointCycle_mul (A * B) D (hA.mul hB) hD hAB0 hD0 hAB1 hD1 _ _
    _ = pointCycle k A hA hA0 hA1 + pointCycle k B hB hB0 hB1 + pointCycle k D hD hD0 hD1 :=
      congrArg (fun z => z + pointCycle k D hD hD0 hD1)
        (pointCycle_mul A B hA hB hA0 hB0 hA1 hB1 hAB0 hAB1)
    _ = _ := congrArg₂ (· + ·)
      (congrArg₂ (· + ·) (pointCycle_linear_graph a a' ha hA0 hA1)
        (pointCycle_linear_graph b b' hb hB0 hB1))
      (pointCycle_linear_graph c c' hc hD0 hD1)

/-- Three linear factors give the signed sum of the three original graph classes. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightTwo/SplitPolynomialCycle.lean:379-514"
  "adaptation" "Native polynomial product additivity preserves repeated endpoints"]
theorem cycleClass_eq_three_graphSymbol_of_factorization (p : k[X]) (hp : p.Monic)
    (h0 : IsUnit (p.coeff 0)) (h1 : IsUnit (p.eval 1))
    (a a' b b' c c' : kˣ)
    (h : p = (Polynomial.X - C (a : k)) * (Polynomial.X - C (b : k)) *
      (Polynomial.X - C (c : k)))
    (ha : (a' : k) = 1 - (a : k)) (hb : (b' : k) = 1 - (b : k))
    (hc : (c' : k) = 1 - (c : k)) :
    cycleClass k 2 (pointCycle k p hp h0 h1) =
      graphSymbol k 2 ![a, a'] + graphSymbol k 2 ![b, b'] + graphSymbol k 2 ![c, c'] := by
  have he := congrArg (cycleClass k 2) (threeLinear_pointCycle a a' b b' c c' ha hb hc p hp h0 h1 h)
  simpa only [map_add, graphSymbol] using he

end AlgebraicGeometry.MotivicCohomology.DiagonalSplitPolynomialCycle
