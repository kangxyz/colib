/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.NormCoordinates

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers AlgebraicGeometry.NativeTorusPolynomial
open AlgebraicGeometry.MotivicCohomology.WeightOne

universe u
noncomputable section

variable (k : Type u) [Field k]

section Spectrum

variable {R : Type u} [CommRing R]
variable (f : Spec (.of R) ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]
variable [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]

example : (reducedNorm k).app (op (mk f)) = specSectionsReducedNorm f :=
  reducedNorm_spec k f

example : (reducedNorm k).app (op (mk f)) ≫ (specUnitsIso f).hom = reducedNormApp f :=
  reducedNorm_spec_units k f

example (z : (rawReducedTorus k).obj (op (mk f))) :
    (specUnitsIso f).hom ((reducedNorm k).app (op (mk f)) z) = reducedNormApp f z :=
  reducedNorm_spec_apply k f z

end Spectrum

example (z : point k ⟶ pointTarget k) :
    (specUnitsIso (𝟙 (Spec (.of k)))).hom
      ((reducedNorm k).app (op (base (Spec (.of k))))
        ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up z))) =
      ULift.up (pointCycleNorm k z) :=
  reducedNorm_point_toReduced k z

example (a : kˣ) :
    (specUnitsIso (𝟙 (Spec (.of k)))).hom
      ((reducedNorm k).app (op (base (Spec (.of k))))
        ((toReducedTorus k 1).hom.app (op (point k))
          (ULift.up ((Cor.graphFunctor k).map (rationalPoint k a))))) =
      ULift.up (Additive.ofMul a) := by
  rw [reducedNorm_point_toReduced, pointCycleNorm_graph]

example (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    (specUnitsIso (𝟙 (Spec (.of k)))).hom
      ((reducedNorm k).app (op (base (Spec (.of k))))
        ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up (pointGenerator k Z m)))) =
      ULift.up (m • Additive.ofMul Z.coordinateNorm) := by
  rw [reducedNorm_point_toReduced, pointCycleNorm_generator]

example (Z : PrimePoint (𝟙 (Spec (.of k)))) :
    ((specUnitsIso (𝟙 (Spec (.of k)))).hom
      ((reducedNorm k).app (op (base (Spec (.of k))))
        ((toReducedTorus k 1).hom.app (op (point k))
          (ULift.up (pointGenerator k Z (-1)))))).down.toMul =
      Z.coordinateNorm ^ (-1 : ℤ) := by
  rw [reducedNorm_point_toReduced]
  exact pointCycleNorm_generator_toMul k Z (-1)
