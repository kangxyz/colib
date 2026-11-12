/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoherentSerreVanishing
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Sections
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Basic

/-!
# Eventual lifting of prescribed quotient sections

A coherent epimorphism on projective space has a coherent kernel. Native Serre vanishing
annihilates its first cohomology after sufficiently large twists, and native exactness of
twisting and evaluation then lifts every prescribed section of the quotient. The vanishing
bound is produced, not assumed. This is the projective-space input to whole-boundary lifting
along a finite projective presentation; the finite pushforward and boundary projection-formula
comparisons are not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace AlgebraicGeometry.Scheme.Modules

/-- Every prescribed quotient section lifts after one common Serre bound, for a coherent
epimorphism on projective space over a noetherian ring. -/
@[colib_tag "COL-1042", stacks 01YS
  "eventual lifting of quotient sections by coherent-kernel Serre vanishing"]
theorem exists_surjective_twisted_evaluation_of_coherent_epi
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {F G : SheafOfModules.{u} (projRingSheaf (polyGrading R n))}
    [F.IsCoherent] [G.IsCoherent] (φ : G ⟶ F) [Epi φ] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d → Function.Surjective
      ((SheafOfModules.evaluation (projRingSheaf (polyGrading R n)) (op ⊤)).map
        ((twistFunctor (polyGrading R n) d).map φ)).hom := by
  have hker : SheafOfModules.IsCoherent (kernel φ) :=
    CoherentAbelian.isCoherent_kernel φ
  obtain ⟨B, hB⟩ :=
    Stacks.ProjectiveSpace.SerreVanishing.exists_isZero_Hgroup_twist_of_isCoherent
      R n 1 Nat.one_pos (kernel φ) hker
  refine ⟨B, fun d hd => ?_⟩
  have hse :=
    Stacks.AlgebraicGeometry.TwistFlatness.shortExact_map_twistFunctor_of_adjoin_degree_one
    (polyGrading R n)
    (Stacks.ProjectiveSpace.SerreVanishing.adjoin_range_one_polyGrading R n) d
    (ShortComplex.shortExact_mk_kernel_ι φ)
  exact Stacks.AmpleCohomologicalCriterion.surjective_evaluation_map_g
    (AlgebraicGeometry.Proj (polyGrading R n)) ⊤ hse
    ((Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      (projRingSheaf (polyGrading R n)) ⊤ 1
      (twistSheafOfModules (polyGrading R n) (kernel φ) d)).mpr (hB d hd))

end AlgebraicGeometry.Scheme.Modules
