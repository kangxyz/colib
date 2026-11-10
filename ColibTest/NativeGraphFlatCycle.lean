/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.ReducedGraphNaturality

/-! Source-only consumers. No characteristic, coefficient-flatness, or reduced-fiber premise. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open NativeTorusPolynomial Polynomial Polynomial.BoundaryOneRationalFunctions
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

universe u

section FlatSource

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [IsSeparated g] [Smooth h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  [Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h)]
  [IsLocallyNoetherian (integralComponentAt z).subscheme]

example : Flat (correspondenceSupportProductToGraph f g h z w) := inferInstance

example (x : correspondenceIncidence f g h z w) (n : ℕ) :
    IsZero (correspondenceIncidenceAmbientTor f g h z w x (n + 1)) :=
  isZero_correspondenceIncidenceTor_succ_of_flat_source f g h z w x n

example (x : correspondenceIncidence f g h z w) :
    Module.length (correspondenceIncidenceAmbientStalk f g h z w x)
      (correspondenceIncidenceAmbientTor f g h z w x 0) =
    Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x)
      ((correspondenceIncidence f g h z w).presheaf.stalk x) :=
  length_correspondenceIncidenceAmbientTor_zero f g h z w x

example (x : genericPoints (correspondenceIncidence f g h z w)) :
    correspondenceIncidenceTorCoefficient k f g h z w x =
      ((Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x.val)
        ((correspondenceIncidence f g h z w).presheaf.stalk x.val)).toNat : ℤ) :=
  correspondenceIncidenceTorCoefficient_eq_length_of_flat_source f g h z w x

example [IsNoetherian (correspondenceIncidence f g h z w)]
    (hw : IsFiniteCorrespondencePoint g h w) :
    incidenceTorCycle f g h z w hw =
      AlgebraicCycle.fundamentalCycle (correspondenceIncidence f g h z w) :=
  incidenceTorCycle_eq_fundamentalCycle_of_flat_source f g h z w hw

end FlatSource

section FiberGeometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (w : pullback (C := Scheme) g h) (φ : X ⟶ Y) (hφ : φ ≫ g = f)

example : IsClosedImmersion (correspondenceGraphFiberMap f g h w φ hφ) := inferInstance

example (x : correspondenceGraphFiber g h w φ) :
    (correspondenceGraphFiberMap f g h w φ hφ).residueDegree x = 1 :=
  correspondenceGraphFiberMap_residueDegree f g h w φ hφ x

example [IsIntegral X] [IsSeparated g] (s : genericPoints X) :
    (correspondenceLeftGraphFiberIso f g h w φ hφ s).hom ≫
      correspondenceGraphFiberMap f g h w φ hφ =
      correspondenceIncidenceMap f g h (correspondenceGraphMap f g φ hφ s.val) w :=
  correspondenceLeftGraphFiberIso_map f g h w φ hφ s

end FiberGeometry

section Coefficients

variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
  (f : Spec (.of R) ⟶ Spec (.of k)) (a : R →+* A)
  [Smooth f] [IsSeparated f] [QuasiCompact f]
  [Smooth (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [IsSeparated (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [QuasiCompact (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]

example (Z : PrimePoint f) :
    graphRestriction f a (singleFiniteCorrespondence f
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) Z.val Z.property 1) =
      Z.coefficientFiberCycle a := graphRestriction_single_eq_coefficientFiber f a Z

example (Z : PrimePoint f) :
    graphRestriction f a (singleFiniteCorrespondence f
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) Z.val Z.property (-3)) =
      (-3 : ℤ) • Z.coefficientFiberCycle a := graphRestriction_single f a Z (-3)

example (Z : PrimePoint f) :
    cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f)
      (graphRestriction f a (singleFiniteCorrespondence f
        (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) Z.val Z.property (-3))) =
      Additive.ofMul ((Units.map a.toMonoidHom Z.coordinateNorm) ^ (-3 : ℤ)) := by
  rw [graphRestriction_single]
  exact Z.cycleNorm_zsmul_coefficientFiberCycle a (-3)

example (z : finiteCorrespondences f
    (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))) :
    cycleRationalFunction (Spec.map (CommRingCat.ofHom a) ≫ f) (graphRestriction f a z) =
      (admissibleMap a).toAdditive (cycleRationalFunction f z) :=
  cycleRationalFunction_graphRestriction f a z

example (z : finiteCorrespondences f
    (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))) :
    cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f) (graphRestriction f a z) =
      (Units.map a.toMonoidHom).toAdditive (cycleNorm f z) :=
  cycleNorm_graphRestriction f a z

example (q : Additive (admissibleGroup R)) :
    graphRestriction f a (rationalDivisorHom f q) =
      rationalDivisorHom (Spec.map (CommRingCat.ofHom a) ≫ f)
        ((admissibleMap a).toAdditive q) := rationalDivisorHom_graphRestriction f a q

example (q : Additive (group R)) :
    graphRestriction f a (boundaryDivisor f q) =
      boundaryDivisor (Spec.map (CommRingCat.ofHom a) ≫ f)
        ((Polynomial.BoundaryOneRationalFunctions.map a).toAdditive q) :=
  boundaryDivisor_graphRestriction f a q

example (p : R[X]) (hp : p.Monic) (h0 : IsUnit (p.coeff 0)) :
    graphRestriction f a (polynomialCycle f p hp h0) =
      polynomialCycle (Spec.map (CommRingCat.ofHom a) ≫ f) (p.map a) (hp.map a)
        (map_constant_isUnit a p h0) := polynomialCycle_graphRestriction f a p hp h0

example (p : R[X]) (hp : p.Monic) (h0 : IsUnit ((p ^ 2).coeff 0)) :
    graphRestriction f a (polynomialCycle f (p ^ 2) (hp.pow 2) h0) =
      polynomialCycle (Spec.map (CommRingCat.ofHom a) ≫ f) ((p ^ 2).map a)
        ((hp.pow 2).map a) (map_constant_isUnit a (p ^ 2) h0) :=
  polynomialCycle_graphRestriction f a (p ^ 2) (hp.pow 2) h0

example (z : Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    powerOneNorm (Spec.map (CommRingCat.ofHom a) ≫ f)
        ((Cor.graphFunctor k).map (coefficientGraph f a) ≫ z) =
      (Units.map a.toMonoidHom).toAdditive (powerOneNorm f z) :=
  powerOneNorm_graph_comp f a z

example (z : sections (reducedTorus k 1) (Cor.mk (mk f))) :
    reducedNormApp (Spec.map (CommRingCat.ofHom a) ≫ f)
      (transfer (reducedTorus k 1) ((Cor.graphFunctor k).map (coefficientGraph f a)) z) =
      ULift.up ((Units.map a.toMonoidHom).toAdditive (reducedNormApp f z).down) :=
  reducedNormApp_coefficientGraph f a z

end Coefficients
