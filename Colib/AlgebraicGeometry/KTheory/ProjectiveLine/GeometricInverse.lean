/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricCoefficientFunctors
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasqueKEquivalence

/-! # The geometric coefficient map of the projective-line formula

The two coordinates come from actual direct image and actual direct image after the
negative twist. The common flasque model is removed by the K-equivalence of its literal
inclusion into native perfect complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [CompactSpace X]

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "W" Y =>
  perfectComplexesWaldhausen (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y))

/-- The literal inclusion of flasque perfect complexes into all perfect complexes on the line. -/
def projectiveLineFlasqueKEquiv (n : ℕ) : (FlasquePerfect.waldhausen P).K n ≃* (W P).K n := by
  let := isProper_projectiveSpaceOver 1 X
  let : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace π
  exact MulEquiv.ofBijective (KMap (FlasquePerfect.perfectInclusion_exact P) n)
    (FlasquePerfect.perfectInclusion_KMap_bijective P n)

/-- The actual geometric map with its ordered direct-image and negative-twist coordinates. -/
def projectiveLineGeometricKMap (n : ℕ) : (W P).K n →* (W X).K n × (W X).K n :=
  ((KMap (FlasquePerfect.projectiveLineG₀_exact X) n).prod
    (KMap (FlasquePerfect.projectiveLineG₁_exact X) n)).comp
      (projectiveLineFlasqueKEquiv X n).symm.toMonoidHom

/-- The geometric map on the actual classes of termwise flasque representatives. -/
theorem projectiveLineGeometricKMap_of_flasque (n : ℕ) (a : (FlasquePerfect.waldhausen P).K n) :
    projectiveLineGeometricKMap X n (projectiveLineFlasqueKEquiv X n a) =
      (KMap (FlasquePerfect.projectiveLineG₀_exact X) n a,
        KMap (FlasquePerfect.projectiveLineG₁_exact X) n a) := by
  simp only [projectiveLineGeometricKMap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.prod_apply]

end AlgebraicGeometry.Scheme
