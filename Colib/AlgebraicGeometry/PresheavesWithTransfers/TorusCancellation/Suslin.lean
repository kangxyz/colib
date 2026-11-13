/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.NormalizedCriterion
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.BoundaryReflection
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.SingularSurjectivity

/-!
# Cancellation for the native Suslin comparison

The signed power cut reflects normalized boundaries. The relative
interchange gives surjectivity modulo boundaries on normalized cycles.
The normalized criterion applies to the original transfer chain map.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The reduced torus comparison of the original transfer singular complexes
is a quasi-isomorphism. -/
@[colib_tag "COL-1045", colib_ref "Voevodsky2010Cancellation" "Corollary 4.9, p. 684"
  "adaptation" "Integral cancellation on the native smooth finite-correspondence category"]
theorem torusCancellationChainMap_quasiIso (Y : Cor k) :
    QuasiIso (torusCancellationChainMap k Y) :=
  singularComplexMap_quasiIso_of_normalized (torusCancellationMap k Y)
    (fun X n x _ hx => torusCancellationMap_reflects_normalizedBoundary k Y X n x hx)
    (torusCancellationMap_surjective_mod_normalizedBoundaries k Y)

end AlgebraicGeometry.PresheafWithTransfers
