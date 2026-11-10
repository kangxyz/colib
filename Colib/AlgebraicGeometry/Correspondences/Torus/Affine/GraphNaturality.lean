/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatFiber
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NormNaturality
public import Colib.AlgebraicGeometry.Sites.Smooth.Torus

/-!
# Ordinary graph naturality of actual affine torus cycles and norms

Restriction is literally precomposition by the existing graph functor, with
its original incidence Tor composition. The graph-fiber comparison and the
constructed whole coefficient fiber give the signed prime calculation.
Native additive extensionality retains every integer multiplicity. The actual
rational inverse then gives divisor and whole polynomial-cycle naturality.

The coefficient map is arbitrary. Both affine objects are smooth over an
arbitrary field; normal integral Noetherian coefficients are retained exactly
where rational recovery is used. No transfer structure on ordinary units is
introduced. This source-only file does not assert sheaf descent or acceptance.

Adapted from motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Torus/Affine/PolynomialBaseChange.lean and DivisorNaturality.lean.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Polynomial Stacks.Chow
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
  (f : Spec (.of R) ⟶ Spec (.of k)) (a : R →+* A)
  [Smooth f] [IsSeparated f] [QuasiCompact f]
  [Smooth (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [IsSeparated (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [QuasiCompact (Spec.map (CommRingCat.ofHom a) ≫ f)]

/-- The actual contravariant spectrum map as an ordinary smooth-site arrow. -/
def coefficientGraph : mk (Spec.map (CommRingCat.ofHom a) ≫ f) ⟶ mk f :=
  homMk (Spec.map (CommRingCat.ofHom a)) rfl

/-- Ordinary restriction is the existing native graph precomposition. -/
def graphRestriction :
    finiteCorrespondences f (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) →+
      finiteCorrespondences (Spec.map (CommRingCat.ofHom a) ≫ f)
        (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) :=
  Preadditive.leftComp (Cor.mk (multiplicativeGroupObject (Spec (.of k))))
    ((Cor.graphFunctor k).map (coefficientGraph f a))

variable [IsDomain R] [IsIntegrallyClosed R]
  [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]

omit [IsIntegrallyClosed A] in
/-- Native left-graph Tor composition is the actual unreduced support fiber cycle. -/
theorem graphRestriction_single_eq_coefficientFiber (Z : PrimePoint f) :
    graphRestriction f a (singleFiniteCorrespondence f
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) Z.val Z.property 1) =
        Z.coefficientFiberCycle a := by
  have : IsIntegral (mk (Spec.map (CommRingCat.ofHom a) ≫ f)).left :=
    inferInstanceAs (IsIntegral (Spec (.of A)))
  have : Flat ((integralComponentAt Z.val).subschemeι ≫
      pullback.fst (mk f).hom (multiplicativeGroupObject (Spec (.of k))).hom) :=
    inferInstanceAs (Flat Z.projection)
  apply Subtype.ext
  exact Cor.graph_comp_single_val_eq_fiber
    (X := mk (Spec.map (CommRingCat.ofHom a) ≫ f)) (Y := mk f)
    (Z := multiplicativeGroupObject (Spec (.of k)))
    k Z.val Z.property (coefficientGraph f a)

omit [IsIntegrallyClosed A] in
/-- A signed original prime retains its integer weight on the whole coefficient fiber. -/
theorem graphRestriction_single (Z : PrimePoint f) (n : ℤ) :
    graphRestriction f a (singleFiniteCorrespondence f
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) Z.val Z.property n) =
        n • Z.coefficientFiberCycle a := by
  rw [singleFiniteCorrespondence_eq_zsmul, map_zsmul,
    graphRestriction_single_eq_coefficientFiber]

/-- The actual ordinary restriction of every signed cycle has the mapped rational function. -/
theorem cycleRationalFunction_graphRestriction
    (z : finiteCorrespondences f
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))) :
    cycleRationalFunction (Spec.map (CommRingCat.ofHom a) ≫ f) (graphRestriction f a z) =
      (admissibleMap a).toAdditive (cycleRationalFunction f z) := by
  have H : (cycleRationalFunction (Spec.map (CommRingCat.ofHom a) ≫ f)).comp
      (graphRestriction f a) = (admissibleMap a).toAdditive.comp (cycleRationalFunction f) := by
    apply finiteCorrespondences.addHom_ext_one f
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))
    intro z hz
    simpa only [AddMonoidHom.comp_apply, cycleRationalFunction_single, one_zsmul,
      MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul] using
      (congrArg (cycleRationalFunction (Spec.map (CommRingCat.ofHom a) ≫ f))
        (graphRestriction_single_eq_coefficientFiber f a (⟨z, hz⟩ : PrimePoint f))).trans
          (PrimePoint.cycleRationalFunction_coefficientFiberCycle (⟨z, hz⟩ : PrimePoint f) a)
  exact DFunLike.congr_fun H z

/-- The independently defined support determinant norm is ordinary-natural on all signed cycles. -/
theorem cycleNorm_graphRestriction
    (z : finiteCorrespondences f
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))) :
    cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f) (graphRestriction f a z) =
      (Units.map a.toMonoidHom).toAdditive (cycleNorm f z) := by
  have H : (cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f)).comp (graphRestriction f a) =
      (Units.map a.toMonoidHom).toAdditive.comp (cycleNorm f) := by
    apply finiteCorrespondences.addHom_ext_one f
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))
    intro z hz
    simpa only [AddMonoidHom.comp_apply, cycleNorm_single, one_zsmul,
      MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul] using
      (congrArg (cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f))
        (graphRestriction_single_eq_coefficientFiber f a (⟨z, hz⟩ : PrimePoint f))).trans
          (PrimePoint.cycleNorm_coefficientFiberCycle (⟨z, hz⟩ : PrimePoint f) a)
  exact DFunLike.congr_fun H z

variable [IsNoetherianRing R]

/-- The actual divisor is natural under every coefficient graph, including nonflat faces. -/
theorem rationalDivisorHom_graphRestriction (q : Additive (admissibleGroup R)) :
    graphRestriction f a (rationalDivisorHom f q) =
      rationalDivisorHom (Spec.map (CommRingCat.ofHom a) ≫ f)
        ((admissibleMap a).toAdditive q) := by
  apply cycleRationalFunction_injective (Spec.map (CommRingCat.ofHom a) ≫ f)
  rw [cycleRationalFunction_graphRestriction, cycleRationalFunction_rationalDivisorHom,
    cycleRationalFunction_rationalDivisorHom]

/-- The genuine boundary divisor is ordinary-natural in the original boundary-one group. -/
theorem boundaryDivisor_graphRestriction (q : Additive (group R)) :
    graphRestriction f a (boundaryDivisor f q) =
      boundaryDivisor (Spec.map (CommRingCat.ofHom a) ≫ f)
        ((Polynomial.BoundaryOneRationalFunctions.map a).toAdditive q) := by
  change graphRestriction f a
    (rationalDivisorHom f (Additive.ofMul (boundaryInclusion q.toMul))) =
      rationalDivisorHom (Spec.map (CommRingCat.ofHom a) ≫ f)
        (Additive.ofMul (boundaryInclusion (Polynomial.BoundaryOneRationalFunctions.map a q.toMul)))
  rw [rationalDivisorHom_graphRestriction]
  exact congrArg (fun t : admissibleGroup A =>
    rationalDivisorHom (Spec.map (CommRingCat.ofHom a) ≫ f) (Additive.ofMul t))
      (boundaryInclusion_natural a q.toMul)

/-- Whole polynomial cycles, with every repeated factor, have actual graph base change. -/
theorem polynomialCycle_graphRestriction (p : R[X]) (hp : p.Monic)
    (h0 : IsUnit (p.coeff 0)) :
    graphRestriction f a (polynomialCycle f p hp h0) =
      polynomialCycle (Spec.map (CommRingCat.ofHom a) ≫ f) (p.map a) (hp.map a)
        (map_constant_isUnit a p h0) := by
  let d : denominators R := ⟨p, hp, h0⟩
  have H := rationalDivisorHom_graphRestriction f a (Additive.ofMul (admissibleFraction d 1))
  change graphRestriction f a (rationalDivisor f (admissibleFraction d 1)) =
    rationalDivisor (Spec.map (CommRingCat.ofHom a) ≫ f)
      (admissibleMap a (admissibleFraction d 1)) at H
  simp only [admissibleMap_fraction, map_one, rationalDivisor_fraction,
    denominatorCycle_one, sub_zero] at H
  simpa [denominatorCycle, denominatorMap, d] using H

end AlgebraicGeometry.NativeTorusPolynomial
