module

import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFree

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Perfect.BoundedLocallyFreeComplexes
open scoped ZeroObject

universe u

noncomputable section

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X : Scheme.{u}}

example (K : CochainComplex X.Modules ℤ) :
    boundedFiniteLocallyFreeComplex X K ↔
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
        ∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u} (K.X n) :=
  boundedFiniteLocallyFreeComplex_iff_termBounds K

example : boundedFiniteLocallyFreeComplex X 0 :=
  boundedFiniteLocallyFreeComplex_of_isZero (isZero_zero _)

example {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : boundedFiniteLocallyFreeComplex X S.X₁)
    (h₃ : boundedFiniteLocallyFreeComplex X S.X₃) :
    boundedFiniteLocallyFreeComplex X S.X₂ :=
  boundedFiniteLocallyFreeComplex_of_shortExact hS h₁ h₃

example {K : CochainComplex X.Modules ℤ} (hK : boundedFiniteLocallyFreeComplex X K) :
    boundedFiniteLocallyFreeComplex X (K⟦(-1 : ℤ)⟧) :=
  boundedFiniteLocallyFreeComplex_shift hK (-1)

example {K L : CochainComplex X.Modules ℤ} (hK : boundedFiniteLocallyFreeComplex X K)
    (hL : boundedFiniteLocallyFreeComplex X L) (f : K ⟶ L) :
    boundedFiniteLocallyFreeComplex X (CochainComplex.mappingCone f) :=
  boundedFiniteLocallyFreeComplex_mappingCone hK hL f

example {K : CochainComplex X.Modules ℤ} (hK : boundedFiniteLocallyFreeComplex X K) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K :=
  isPerfectComplex_of_boundedFiniteLocallyFree hK

example (M : X.Vect) :
    boundedFiniteLocallyFreeComplex X
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) (-2)).obj M.obj) :=
  boundedFiniteLocallyFreeComplex_single_obj M.obj (-2) M.property

example {K L : (boundedFiniteLocallyFreeComplex X).FullSubcategory} (f : K ⟶ L) :
    ((boundedFiniteLocallyFreePerfectInclusion X).map f).hom = f.hom := rfl

example {K L : (boundedFiniteLocallyFreeComplex X).FullSubcategory} (f : K ⟶ L) :
    (boundedFiniteLocallyFreeWaldhausen X).weq f ↔ QuasiIso f.hom := Iff.rfl

example (n : ℕ) : X.boundedFiniteLocallyFreeToPerfectKMap n =
    Waldhausen.KMap (boundedFiniteLocallyFreePerfectInclusion_isExact X) n := rfl

example (n : ℕ) : X.vectorBundleToBoundedFiniteLocallyFreeKMap n =
    Waldhausen.KMap (vectorBundleComplexInclusion_isExact X) n := rfl
