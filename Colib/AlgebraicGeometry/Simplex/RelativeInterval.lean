/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.EndpointHomotopy
public import Colib.AlgebraicTopology.DoldKan.NormalizedCycles

/-!
# Relative interval homotopies on algebraic singular chains

For a simplex over the interval whose face restrictions vanish, the two
endpoint restrictions differ by a normalized boundary. The proof uses the
existing geometric prism and the canonical retraction to the Moore complex.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicTopology.NormalizedMooreComplex
open scoped Simplicial

universe u v

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable (P : (SmoothSite (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{v})

set_option quotPrecheck false in
local notation "S(" V ")" => ((simplicialPresheaf R P).flip.obj (op V))
set_option quotPrecheck false in
local notation "I" => (cosimplicialSmoothSite R).obj ⦋1⦌

/-- The difference of the actual endpoint restrictions of a relative cycle is
a normalized boundary in the original evaluated singular simplicial group. -/
theorem intervalEndpoint_sub_isNormalizedBoundary (U : SmoothSite (Spec (.of R)))
    (n : ℕ) (x : (S(SmoothSite.product U I)).obj (op ⦋n⦌))
    (hx : IsCycle (S(SmoothSite.product U I)) n x) :
    IsBoundary (S(U)) n
      (((simplicialPresheaf R P).flip.map (intervalInclusion R U 0).op).app (op ⦋n⦌) x -
        ((simplicialPresheaf R P).flip.map (intervalInclusion R U 1).op).app (op ⦋n⦌) x) := by
  let e (v : Fin 2) : S(SmoothSite.product U I) ⟶ S(U) :=
    (simplicialPresheaf R P).flip.map (intervalInclusion R U v).op
  have hc := (hx.map (e 0)).sub (S(U)) (hx.map (e 1))
  exact isBoundary_sub_of_homotopy (S(U)) (intervalEndpointHomotopy R P U) n x
    (alternatingCycle_of_isCycle _ n x hx) (hc.isNormalized (S(U)))

end AlgebraicSimplex
