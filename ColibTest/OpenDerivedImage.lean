/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Exact
import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.DualFactorization

/-! Regression clients retain original maps, strict equations, and actual kernel endpoints. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.OpenDerivedImage

noncomputable section

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

local notation "R" => Functor.mapHomologicalComplex (restrictFunctor j) (ComplexShape.up ℤ)

example {E E' : CochainComplex U.Modules ℤ} (f : E ⟶ E') [QuasiIso f] :
    complexObjects j E ↔ complexObjects j E' := complexObjects_iff_of_quasiIso j f

example {E : CochainComplex U.Modules ℤ} (hE : complexObjects j E) :
    RingedSpace.IsPerfectComplex (X := U.toRingedSpace) E := isPerfectComplex_of_mem j hE

example : corestrict j ⋙ inclusion j = perfectComplexesRestrictOpenImmersion j :=
  corestrict_comp_inclusion j

example (hroof : HasDerivedRoofs j) {S : ShortComplex (CochainComplex U.Modules ℤ)}
    (hS : S.ShortExact) (h₂ : complexObjects j S.X₂) (h₃ : complexObjects j S.X₃) :
    complexObjects j S.X₁ := complexObjects_kernel_of_shortExact j hroof hS h₂ h₃

example (hroof : HasDerivedRoofs j) {A B : Obj j} (f : A ⟶ B) :
    (waldhausen j hroof).cof f ↔ Mono f.hom := Iff.rfl

example (hroof : HasDerivedRoofs j) {A B : Obj j} (f : A ⟶ B) :
    (waldhausen j hroof).weq f ↔ QuasiIso f.hom := Iff.rfl

example (hroof : HasDerivedRoofs j) :
    Waldhausen.IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (waldhausen j hroof).cof (waldhausen j hroof).weq (corestrict j) :=
  corestrict_isExact j hroof

example (hroof : HasDerivedRoofs j)
    (P : CochainComplex X.Modules ℤ)
    (hP : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) P)
    (B B' : CochainComplex U.Modules ℤ)
    (hB' : complexObjects j B') (w : (R).obj P ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : CochainComplex X.Modules ℤ) (D : CochainComplex U.Modules ℤ)
      (c : C ⟶ P) (d : D ⟶ B) (u : (R).obj C ⟶ D) (v : B' ⟶ D),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) C ∧
      complexObjects j D ∧ QuasiIso u ∧ QuasiIso v ∧
      u ≫ d = (R).map c ≫ w ∧ v ≫ d = b ∧
      (∀ i, IsSplitEpi (c.f i)) ∧ (∀ i, IsSplitEpi (d.f i)) ∧
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) (kernel c) ∧
      complexObjects j (kernel d) :=
  exists_dual_factorization j hroof P hP B B' hB' w b
