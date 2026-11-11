/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialCurveCycles
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CycleSymbols
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FaceSquare

import Mathlib.Tactic.ComputeDegree

/-!
# The full two-unit cubic boundary

The original cubic is a whole polynomial correspondence into the native
two-fold torus. Each coface is the whole specialized polynomial cycle,
including repeated factors and nonreduced fibers. Their graph classes agree
in the actual reduced singular quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite Polynomial
open Stacks.Chow.PolynomialEndpointFiber

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCubicBoundary

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open DiagonalTopDegree DiagonalCycleSymbols PolynomialCurveCycles
open DiagonalFiniteCyclePushforward (source sourceFace sourceFace_chart sourceChart0 sourceChart1
  sourceSimplexProjection simplexChart0 simplexChart1 zeroCoordinateEquiv oneCoordinateEquiv)

variable {k : Type u} [Field k]

/-- The unit value at one is preserved by the literal coefficient map. -/
theorem map_eval_one_isUnit {R A : Type u} [CommRing R] [CommRing A]
    (a : R →+* A) (p : R[X]) (h1 : IsUnit (p.eval 1)) :
    IsUnit ((p.map a).eval 1) := by
  rw [← a.map_one, eval_map_apply]
  exact h1.map a

/-- Actual graph precomposition specializes the whole two-coordinate polynomial cycle. -/
theorem polynomialCurveCycle_graphRestriction
    {R A : Type u} [CommRing R] [CommRing A] [IsDomain R] [IsDomain A]
    [IsIntegrallyClosed R] [IsIntegrallyClosed A] [IsNoetherianRing R] [IsNoetherianRing A]
    (f : Spec (.of R) ⟶ Spec (.of k)) (g : Spec (.of A) ⟶ Spec (.of k))
    [Smooth f] [IsSeparated f] [QuasiCompact f] [Smooth g] [IsSeparated g] [QuasiCompact g]
    (a : R →+* A) (ha : Spec.map (CommRingCat.ofHom a) ≫ f = g)
    (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0)) (h1 : IsUnit (p.eval 1)) :
    (Cor.graphFunctor k).map (homMk (Spec.map (CommRingCat.ofHom a)) ha) ≫
        polynomialCurveCycle f p hp h0 h1 =
      polynomialCurveCycle g (p.map a) (hp.map a)
        (NativeTorusPolynomial.map_constant_isUnit a p h0) (map_eval_one_isUnit a p h1) := by
  subst g
  let γ := (Cor.graphFunctor k).map (NativeTorusPolynomial.coefficientGraph f a)
  let c := openPolynomialCycle f p hp h0 h1
  let d := openPolynomialCycle (Spec.map (CommRingCat.ofHom a) ≫ f) (p.map a) (hp.map a)
    (NativeTorusPolynomial.map_constant_isUnit a p h0) (map_eval_one_isUnit a p h1)
  let j := (Cor.graphFunctor k).map (openInclusion k)
  have h : γ ≫ c = d := by
    apply openGraph_injective k (openInclusion k)
    change (γ ≫ c) ≫ j = d ≫ j
    calc
      _ = γ ≫ (c ≫ j) := Category.assoc _ _ _
      _ = γ ≫ NativeTorusPolynomial.polynomialCycle f p hp h0 :=
        congrArg (fun z => γ ≫ z) (openPolynomialCycle_inclusion f p hp h0 h1)
      _ = NativeTorusPolynomial.polynomialCycle (Spec.map (CommRingCat.ofHom a) ≫ f)
          (p.map a) (hp.map a) (NativeTorusPolynomial.map_constant_isUnit a p h0) :=
        NativeTorusPolynomial.polynomialCycle_graphRestriction f a p hp h0
      _ = _ := (openPolynomialCycle_inclusion _ _ _ _ _).symm
  let t := (Cor.graphFunctor k).map (pairMap k)
  change γ ≫ (c ≫ t) = d ≫ t
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ t) h)

variable (k)

/-- The polynomial parameter line over the original field. -/
def lineStructure : Spec (.of k[X]) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))

instance : Smooth (lineStructure k) := by
  rw [lineStructure, HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap k k[X]).Smooth
  exact RingHom.smooth_algebraMap.mpr
    (Algebra.Smooth.of_equiv (oneCoordinateEquiv k))

instance : IsSeparated (lineStructure k) :=
  inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))))

instance : QuasiCompact (lineStructure k) :=
  inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))))

/-- The polynomial line as the smooth site object for the family. -/
abbrev line : SmoothSite (Spec (.of k)) := SmoothSite.mk (lineStructure k)

private theorem endpoint_over (s : k) :
    endpoint s ≫ lineStructure k = 𝟙 (Spec (.of k)) := by
  have h : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom s) = 𝟙 (CommRingCat.of k) := by
    ext r
    simp
  rw [endpoint, lineStructure, ← Spec.map_comp, h, Spec.map_id]

private def linePoint (s : k) : base (Spec (.of k)) ⟶ line k :=
  homMk (endpoint s) (endpoint_over k s)

private theorem simplexChart0_hom :
    (simplexChart0 k).hom = AlgebraicSimplex.structureMap k 0 := by
  change Spec.map (CommRingCat.ofHom (zeroCoordinateEquiv k).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (AlgebraicSimplex.constant k 0))
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (zeroCoordinateEquiv k).symm.commutes

/-- The polynomial simplex chart retains the original field action. -/
theorem simplexChart1_over :
    (simplexChart1 k).hom ≫ lineStructure k = AlgebraicSimplex.structureMap k 1 := by
  change Spec.map (CommRingCat.ofHom (oneCoordinateEquiv k).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom Polynomial.C) =
    Spec.map (CommRingCat.ofHom (AlgebraicSimplex.constant k 1))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (oneCoordinateEquiv k).symm.commutes

private theorem sourceChart0_hom :
    (sourceChart0 k).hom =
      (productFst (base (Spec (.of k))) (AlgebraicSimplex.smoothSiteObj k 0)).left := by
  change sourceSimplexProjection k 0 ≫ (simplexChart0 k).hom = _
  rw [simplexChart0_hom]
  have h := MorphismProperty.Over.w
    (productFst (base (Spec (.of k))) (AlgebraicSimplex.smoothSiteObj k 0))
  change _ ≫ 𝟙 (Spec (.of k)) = (source k 0).hom at h
  rw [Category.comp_id] at h
  exact (MorphismProperty.Over.w
    (productSnd (base (Spec (.of k))) (AlgebraicSimplex.smoothSiteObj k 0))).trans h.symm

/-- The actual degree-one source chart as a map of smooth-site objects. -/
def simplexLineMap : source k 1 ⟶ line k :=
  homMk (sourceChart1 k).hom (by
    change (sourceSimplexProjection k 1 ≫ (simplexChart1 k).hom) ≫ lineStructure k =
      (source k 1).hom
    rw [Category.assoc, simplexChart1_over]
    exact MorphismProperty.Over.w
      (productSnd (base (Spec (.of k))) (AlgebraicSimplex.smoothSiteObj k 1)))

private theorem sourceFace_line (i : Fin 2) :
    sourceFace k i ≫ simplexLineMap k =
      productFst (base (Spec (.of k))) (AlgebraicSimplex.smoothSiteObj k 0) ≫
        linePoint k (i.val : k) := by
  apply MorphismProperty.Over.Hom.ext
  change (sourceFace k i).left ≫ (sourceChart1 k).hom =
    (productFst (base (Spec (.of k))) (AlgebraicSimplex.smoothSiteObj k 0)).left ≫
      endpoint (i.val : k)
  exact (sourceFace_chart k i).trans
    (congrArg (fun e => e ≫ endpoint (i.val : k)) (sourceChart0_hom k))

/-- The whole two-unit polynomial cycle over the original field point. -/
abbrev pointCycle (p : k[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0))
    (h1 : IsUnit (p.eval 1)) : point k ⟶ target k 2 :=
  polynomialCurveCycle (𝟙 (Spec (.of k))) p hp h0 h1

/-- The genuine one-simplex correspondence from the whole monic family. -/
def singularCorrespondence (p : k[X][X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0))
    (h1 : IsUnit (p.eval 1)) : Cor.simplexProduct (point k) 1 ⟶ target k 2 :=
  (Cor.graphFunctor k).map (simplexLineMap k) ≫
    polynomialCurveCycle (lineStructure k) p hp h0 h1

/-- The original coface is the literal whole polynomial specialization. -/
theorem singularCorrespondence_face (p : k[X][X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0))
    (h1 : IsUnit (p.eval 1)) (i : Fin 2) :
    (Cor.simplexProductCosimplicial (point k)).δ i ≫
        singularCorrespondence k p hp h0 h1 =
      WeightOne.zeroSimplexProjection k ≫
        pointCycle k (p.map (evalRingHom (i.val : k))) (hp.map _)
          (NativeTorusPolynomial.map_constant_isUnit _ _ h0) (map_eval_one_isUnit _ _ h1) := by
  change (Cor.graphFunctor k).map (sourceFace k i) ≫
      (Cor.graphFunctor k).map (simplexLineMap k) ≫ _ = _
  rw [← Functor.map_comp_assoc, sourceFace_line, Functor.map_comp, Category.assoc]
  have h := polynomialCurveCycle_graphRestriction (lineStructure k) (𝟙 (Spec (.of k)))
    (evalRingHom (i.val : k)) (endpoint_over k (i.val : k)) p hp h0 h1
  exact congrArg (fun z => WeightOne.zeroSimplexProjection k ≫ z) h

private theorem class_of_face (i : Fin 2) (α : Cor.simplexProduct (point k) 1 ⟶ target k 2)
    (z : point k ⟶ target k 2) (h : (Cor.simplexProductCosimplicial (point k)).δ i ≫ α =
      WeightOne.zeroSimplexProjection k ≫ z) :
    singularClass k 2 (transfer (reducedTorus k 2)
      ((Cor.simplexProductCosimplicial (point k)).δ i)
      ((toReducedTorus k 2).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α))) =
        cycleClass k 2 z := by
  have hq := reducedTorus_transfer_apply k 2 ((Cor.simplexProductCosimplicial (point k)).δ i) α
  have hclass := congrArg (fun β : Cor.simplexProduct (point k) 0 ⟶ target k 2 =>
    singularClass k 2 ((toReducedTorus k 2).hom.app
      (op (Cor.simplexProduct (point k) 0)) (ULift.up β))) h
  exact (congrArg (singularClass k 2) hq).trans (hclass.trans (cycleClass_apply k 2 z).symm)

/-- The actual two specialized polynomial cycles have equal raw graph classes. -/
theorem cycleClass_endpoints (p : k[X][X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0))
    (h1 : IsUnit (p.eval 1)) (p₀ p₁ : k[X])
    (hp₀ : p.map (evalRingHom 0) = p₀) (hp₁ : p.map (evalRingHom 1) = p₁)
    (hm₀ : p₀.Monic) (hm₁ : p₁.Monic) (hc₀ : IsUnit (p₀.coeff 0))
    (hc₁ : IsUnit (p₁.coeff 0)) (hu₀ : IsUnit (p₀.eval 1)) (hu₁ : IsUnit (p₁.eval 1)) :
    cycleClass k 2 (pointCycle k p₀ hm₀ hc₀ hu₀) =
      cycleClass k 2 (pointCycle k p₁ hm₁ hc₁ hu₁) := by
  subst p₀
  subst p₁
  let α := singularCorrespondence k p hp h0 h1
  let x : chains k 2 1 :=
    (toReducedTorus k 2).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α)
  let d (i : Fin 2) : chains k 2 0 :=
    transfer (reducedTorus k 2) ((Cor.simplexProductCosimplicial (point k)).δ i) x
  have h₀ := class_of_face k 0 α _ (singularCorrespondence_face k p hp h0 h1 0)
  have h₁ := class_of_face k 1 α _ (singularCorrespondence_face k p hp h0 h1 1)
  have hcast₀ : ((0 : Fin 2).val : k) = 0 := Nat.cast_zero
  have hcast₁ : ((1 : Fin 2).val : k) = 1 := Nat.cast_one
  simp only [hcast₀] at h₀
  simp only [hcast₁] at h₁
  apply sub_eq_zero.mp
  calc
    _ = singularClass k 2 (d 0) - singularClass k 2 (d 1) :=
      congrArg₂ (· - ·) h₀.symm h₁.symm
    _ = singularClass k 2 (d 0 - d 1) := (map_sub (singularClass k 2) _ _).symm
    _ = singularClass k 2 (boundary k 2 x) :=
      congrArg (singularClass k 2) (boundary_eq_endpoints k 2 x).symm
    _ = 0 := singularClass_boundary k 2 x

variable {k}

/-- The literal cubic pencil, with parameter in the coefficient ring. -/
def cubic (a : k) : k[X][X] :=
  Polynomial.X ^ 3 - C (Polynomial.X * C (a ^ 3 + 1)) * Polynomial.X ^ 2 +
    C (Polynomial.X * C (a ^ 3 + 1)) * Polynomial.X - C (C (a ^ 3))

/-- The whole zero endpoint of the original cubic. -/
def cubicZero (a : k) : k[X] := Polynomial.X ^ 3 - C (a ^ 3)

/-- The whole one endpoint of the original cubic. -/
def cubicOne (a : k) : k[X] :=
  (Polynomial.X - C (a ^ 3)) * (Polynomial.X ^ 2 - Polynomial.X + 1)

theorem cubic_monic (a : k) : (cubic a).Monic := by
  unfold cubic
  monicity <;> norm_num

theorem cubic_specialize_zero (a : k) :
    (cubic a).map (evalRingHom 0) = cubicZero a := by
  simp [cubic, cubicZero]

theorem cubic_specialize_one (a : k) :
    (cubic a).map (evalRingHom 1) = cubicOne a := by
  simp only [cubic, cubicOne, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, coe_evalRingHom, eval_mul,
    eval_X, eval_C, one_mul]
  rw [C_add, C_1]
  ring

theorem cubic_constant_isUnit (a : k) (ha : a ≠ 0) : IsUnit ((cubic a).coeff 0) := by
  rw [coeff_zero_eq_eval_zero]
  have h : (cubic a).eval 0 = C (-(a ^ 3)) := by simp [cubic]
  rw [h]
  exact ((isUnit_iff_ne_zero.mpr (pow_ne_zero 3 ha)).neg).map C

theorem cubic_eval_one_isUnit (a : k) (ha : a ^ 3 ≠ 1) : IsUnit ((cubic a).eval 1) := by
  have h : (cubic a).eval 1 = C (1 - a ^ 3) := by simp [cubic]
  rw [h]
  exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ha.symm)).map C

theorem cubicZero_monic (a : k) : (cubicZero a).Monic := by
  rw [← cubic_specialize_zero]
  exact (cubic_monic a).map _

theorem cubicOne_monic (a : k) : (cubicOne a).Monic := by
  rw [← cubic_specialize_one]
  exact (cubic_monic a).map _

theorem cubicZero_constant_isUnit (a : k) (ha : a ≠ 0) : IsUnit ((cubicZero a).coeff 0) := by
  rw [← cubic_specialize_zero]
  exact NativeTorusPolynomial.map_constant_isUnit _ _ (cubic_constant_isUnit a ha)

theorem cubicOne_constant_isUnit (a : k) (ha : a ≠ 0) : IsUnit ((cubicOne a).coeff 0) := by
  rw [← cubic_specialize_one]
  exact NativeTorusPolynomial.map_constant_isUnit _ _ (cubic_constant_isUnit a ha)

theorem cubicZero_eval_one_isUnit (a : k) (ha : a ^ 3 ≠ 1) : IsUnit ((cubicZero a).eval 1) := by
  rw [← cubic_specialize_zero]
  exact map_eval_one_isUnit _ _ (cubic_eval_one_isUnit a ha)

theorem cubicOne_eval_one_isUnit (a : k) (ha : a ^ 3 ≠ 1) : IsUnit ((cubicOne a).eval 1) := by
  rw [← cubic_specialize_one]
  exact map_eval_one_isUnit _ _ (cubic_eval_one_isUnit a ha)

/-- The whole zero endpoint as an actual signed point cycle. -/
def zeroCycle (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) : point k ⟶ target k 2 :=
  pointCycle k (cubicZero a) (cubicZero_monic a)
    (cubicZero_constant_isUnit a ha) (cubicZero_eval_one_isUnit a ha3)

/-- The whole one endpoint as an actual signed point cycle. -/
def oneCycle (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) : point k ⟶ target k 2 :=
  pointCycle k (cubicOne a) (cubicOne_monic a)
    (cubicOne_constant_isUnit a ha) (cubicOne_eval_one_isUnit a ha3)

/-- The two full literal cubic endpoints have equal classes in actual raw homology. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/CubicBoundary.lean:641-706"
  "adaptation" "The genuine cubic singular correspondence and both whole specialized endpoints"]
theorem cubic_cycleClass_endpoints (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    cycleClass k 2 (zeroCycle a ha ha3) = cycleClass k 2 (oneCycle a ha ha3) :=
  cycleClass_endpoints k (cubic a) (cubic_monic a)
    (cubic_constant_isUnit a ha) (cubic_eval_one_isUnit a ha3)
    (cubicZero a) (cubicOne a) (cubic_specialize_zero a) (cubic_specialize_one a)
    (cubicZero_monic a) (cubicOne_monic a)
    (cubicZero_constant_isUnit a ha) (cubicOne_constant_isUnit a ha)
    (cubicZero_eval_one_isUnit a ha3) (cubicOne_eval_one_isUnit a ha3)

end AlgebraicGeometry.MotivicCohomology.DiagonalCubicBoundary
