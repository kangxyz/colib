/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Simplex.OrdinaryChains
import Colib.AlgebraicGeometry.Simplex.BaseChange
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Data.ZMod.Basic

/-! # Consumers of the actual simplex, coefficient squares and ordinary chains -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicSimplex
open scoped Simplicial

universe u v w

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Preadditive A]
variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)

example (n : ℕ) : Smooth (structureMap R n) := inferInstance

example (n : ℕ) : IsSeparated (structureMap R n) := inferInstance

example (n : ℕ) : QuasiCompact (structureMap R n) := inferInstance

example : cosimplicialSmoothSite R ⋙ SmoothSite.forget (Spec (.of R)) =
    cosimplicialSchemeOver R := cosimplicialSmoothSite_forget R

example (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (SmoothSite.product U (smoothSiteObj R n)).left =
      CategoryTheory.Limits.pullback U.hom (structureMap R n) := rfl

example (n : ℕ) (U : (SmoothSite (Spec (.of R)))ᵒᵖ) :
    (((singularChainsFunctor R).obj P).X n).obj U =
      P.obj (op (SmoothSite.product U.unop (smoothSiteObj R n))) := rfl

example (n : ℕ) {U V : (SmoothSite (Spec (.of R)))ᵒᵖ} (f : U ⟶ V) :
    (((singularChainsFunctor R).obj P).X n).map f =
      P.map (SmoothSite.productMap f.unop (𝟙 (smoothSiteObj R n))).op := rfl

example (n : ℕ) :
    ((singularChainsFunctor R).obj P).d (n + 2) (n + 1) ≫
      ((singularChainsFunctor R).obj P).d (n + 1) n = 0 :=
  ((singularChainsFunctor R).obj P).d_comp_d _ _ _

example (U : (SmoothSite (Spec (.of R)))ᵒᵖ) :
    (((singularChainsFunctor R).obj P).d 1 0).app U =
      P.map (SmoothSite.productMap (𝟙 U.unop)
        ((cosimplicialSmoothSite R).δ (0 : Fin 2))).op -
      P.map (SmoothSite.productMap (𝟙 U.unop)
        ((cosimplicialSmoothSite R).δ (1 : Fin 2))).op :=
  singularChainsFunctor_obj_d_one_zero_app R P U

example {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α β : P ⟶ Q) :
    (singularChainsFunctor R).map (α + β) =
      (singularChainsFunctor R).map α + (singularChainsFunctor R).map β :=
  Functor.map_add _

example {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q)
    (n : ℕ) (U : (SmoothSite (Spec (.of R)))ᵒᵖ) :
    (((singularChainsFunctor R).map α).f n).app U =
      α.app (op (SmoothSite.product U.unop (smoothSiteObj R n))) := rfl

example (n : ℕ) :
    IsPushout (CommRingCat.ofHom (Int.castRingHom (ZMod 6)))
      (CommRingCat.ofHom (constant ℤ n))
      (CommRingCat.ofHom (constant (ZMod 6) n))
      (CommRingCat.ofHom (mapCoefficients (Int.castRingHom (ZMod 6)) n)) :=
  mapCoefficients_isPushout _ n

example (n : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (mapCoefficients (Int.castRingHom (ZMod 6)) n)))
      (structureMap (ZMod 6) n) (structureMap ℤ n)
      (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod 6)))) :=
  mapCoefficients_isPullback _ n

example {S : Type u} [CommRing S] (c : R →+* S) (n : ℕ) :
    (coefficientPullbackIso c n).hom ≫
      pullback.fst (structureMap R n) (Spec.map (CommRingCat.ofHom c)) =
        Spec.map (CommRingCat.ofHom (mapCoefficients c n)) :=
  coefficientPullbackIso_hom_fst c n

example {S : Type u} [CommRing S] (c : R →+* S) (n : ℕ) :
    (coefficientPullbackIso c n).hom ≫
      pullback.snd (structureMap R n) (Spec.map (CommRingCat.ofHom c)) =
        structureMap S n := coefficientPullbackIso_hom_snd c n

/-- The actual ordinary chains accept the native normalized-Moore homotopy equivalence. -/
example {B : Type v} [Category.{w} B] [Abelian B]
    (Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ B) :
    HomotopyEquiv
      ((AlgebraicTopology.normalizedMooreComplex _).obj (simplicialPresheaf R Q))
      ((singularChainsFunctor R).obj Q) :=
  AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
