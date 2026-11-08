/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFreePullback
public import Colib.AlgebraicGeometry.KTheory.Pullback

/-!
# Consumers of actual arbitrary native pullback

Every comparison below retains full source, target and named geometric arguments. The
commutative pair square is arbitrary, not assumed cartesian. Degree zero and arbitrary
scheme morphisms are explicit consumers. No all-perfect or supported-boundary naturality
statement is assumed or claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace ColibTest.BoundedFiniteLocallyFreePullback

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] :
    (S.map (Scheme.Modules.pullback f)).ShortExact :=
  Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree (g := f) (S := S) hS

example {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Vect) :
    ((Scheme.Modules.vectorBundleExactPullback f).toFunctor.obj M).obj =
      (Scheme.Modules.pullback f).obj M.obj := rfl

example {X Y : Scheme.{u}} (f : X ⟶ Y) {K : CochainComplex Y.Modules ℤ}
    (hK : boundedFiniteLocallyFreeComplex Y K) :
    boundedFiniteLocallyFreeComplex X
      (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  boundedFiniteLocallyFreeComplex_pullback (X := X) (Y := Y) (f := f) (K := K) hK

example {X Y : Scheme.{u}} (f : X ⟶ Y) {K : CochainComplex Y.Modules ℤ}
    (hK : boundedFiniteLocallyFreeComplex Y K) (ha : K.Acyclic) :
    (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
  acyclic_pullback_of_boundedFiniteLocallyFree (X := X) (Y := Y)
    (f := f) (K := K) hK ha

example {X Y : Scheme.{u}} (f : X ⟶ Y) {K L : CochainComplex Y.Modules ℤ}
    (hK : boundedFiniteLocallyFreeComplex Y K) (hL : boundedFiniteLocallyFreeComplex Y L)
    (s : K ⟶ L) [QuasiIso s] :
    QuasiIso (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) :=
  quasiIso_pullback_of_boundedFiniteLocallyFree (X := X) (Y := Y)
    (f := f) (K := K) (L := L) hK hL s

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedFiniteLocallyFreeWaldhausen Y).cof
      (boundedFiniteLocallyFreeWaldhausen Y).weq
      (boundedFiniteLocallyFreeWaldhausen X).cof
      (boundedFiniteLocallyFreeWaldhausen X).weq (boundedFiniteLocallyFreePullback f) :=
  boundedFiniteLocallyFreePullback_isExact (X := X) (Y := Y) (f := f)

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    vectorBundleComplexInclusion Y ⋙ boundedFiniteLocallyFreePullback f ≅
      Scheme.Modules.vectorBundlePullback f ⋙ vectorBundleComplexInclusion X :=
  vectorBundleComplexInclusionPullbackIso (X := X) (Y := Y) (f := f)

example (X : Scheme.{u}) (n : ℕ) :
    Scheme.boundedFiniteLocallyFreeKPullback (𝟙 X) n =
      MonoidHom.id (X.boundedFiniteLocallyFreeK n) :=
  Scheme.boundedFiniteLocallyFreeKPullback_id (X := X) (n := n)

example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    Scheme.boundedFiniteLocallyFreeKPullback (f ≫ g) n =
      (Scheme.boundedFiniteLocallyFreeKPullback f n).comp
        (Scheme.boundedFiniteLocallyFreeKPullback g n) :=
  Scheme.boundedFiniteLocallyFreeKPullback_comp (X := X) (Y := Y) (Z := Z)
    (f := f) (g := g) (n := n)

example {U X V Y : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (f : X ⟶ Y) (g : U ⟶ V)
    (h : i ≫ f = g ≫ j) (n : ℕ) :
    (Scheme.boundedFiniteLocallyFreeKRestrict i n).comp
        (Scheme.boundedFiniteLocallyFreeKPullback f n) =
      (Scheme.boundedFiniteLocallyFreeKPullback g n).comp
        (Scheme.boundedFiniteLocallyFreeKRestrict j n) :=
  Scheme.boundedFiniteLocallyFreeKRestrict_pullback (U := U) (X := X) (V := V) (Y := Y)
    (i := i) (j := j) (f := f) (g := g) (h := h) (n := n)

example {U X V Y : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (f : X ⟶ Y) (g : U ⟶ V)
    (h : i ≫ f = g ≫ j) :
    (Scheme.boundedFiniteLocallyFreeKRestrict i 0).comp
        (Scheme.boundedFiniteLocallyFreeKPullback f 0) =
      (Scheme.boundedFiniteLocallyFreeKPullback g 0).comp
        (Scheme.boundedFiniteLocallyFreeKRestrict j 0) :=
  Scheme.boundedFiniteLocallyFreeKRestrict_pullback (U := U) (X := X) (V := V) (Y := Y)
    (i := i) (j := j) (f := f) (g := g) (h := h) (n := 0)

example {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    Scheme.boundedFiniteLocallyFreeKPullback j n = Scheme.boundedFiniteLocallyFreeKRestrict j n :=
  Scheme.boundedFiniteLocallyFreeKPullback_eq_restrict (X := X) (Y := Y) (j := j) (n := n)

example {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (Scheme.boundedFiniteLocallyFreeKPullback f n).comp
        (Scheme.vectorBundleToBoundedFiniteLocallyFreeKMap Y n) =
      (Scheme.vectorBundleToBoundedFiniteLocallyFreeKMap X n).comp
        (Waldhausen.KMap (Scheme.Modules.vectorBundleExactPullback f).waldhausenExact n) :=
  Scheme.vectorBundleToBoundedFiniteLocallyFreeKMap_pullback
    (X := X) (Y := Y) (f := f) (n := n)

example {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Scheme.K Y n →* Scheme.K X n := Scheme.pullbackK (f := f) (n := n)

example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    Scheme.pullbackK (f ≫ g) n = (Scheme.pullbackK f n).comp (Scheme.pullbackK g n) :=
  Scheme.pullbackK_comp (f := f) (g := g) (n := n)

example {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    Scheme.pullbackK j n = Scheme.restrictK j n :=
  Scheme.pullbackK_eq_restrictK (j := j) (n := n)

example {R S : CommRingCat.{u}} (φ : R ⟶ S) (n : ℕ) :
    Scheme.K (Spec R) n →* Scheme.K (Spec S) n :=
  Scheme.pullbackK (f := Spec.map φ) (n := n)

end ColibTest.BoundedFiniteLocallyFreePullback
