/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RefinedProducer
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FiniteProjectiveAmple
/-!
# General-ring refined lifting from the actual finite projective map

This is the exact original geometric input boundary: the native projective map
supplies properness and the actual ample coefficient internally. No chosen line,
frame, section, signed endpoint or local-zero provider is an input.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.AmpleProjectiveImmersion
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {k : Type u} [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (n : ℕ) {X C Y A Z D T : Scheme.{u}}
  [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine T]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (f : C ⟶ projectiveSpaceOverRing n (.of R)) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j]
  (p : Y ⟶ X) [Etale p]
  (hq : j ≫ (f ≫ (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R))) = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (z : Z ⟶ X) [IsFinite (z ≫ q)]
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (d : D ⟶ C) [IsClosedImmersion d]
  [IsFinite (d ≫ (f ≫ (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R))))]
  [IsClosedImmersion (s ≫ j)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range z))
  (v : T ⟶ C) [IsOpenImmersion v]
  [SmoothOfRelativeDimension 1 (v ≫ (f ≫ (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R))))]
  (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
  (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)

local notation "π" => f ≫ (projectiveSpaceOverRing n (CommRingCat.of R) ↘ Spec (CommRingCat.of R))

include hs H hd ha hc in
/-- The finite projective presentation gives the original restriction-difference lift. -/
theorem exists_refined_finiteProjective_lifting (x : X)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U), x ∈ U ∧
      ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V), q x ∈ V ∧
        ∃ _h : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U,
          ∃ hW : IsAffineOpen (parameterOpen q U V),
            letI : IsAffine V.toScheme := hV
            letI : IsAffine (parameterOpen q U V).toScheme := hW
            PresheafWithTransfers.HasRestrictionDifferenceLifting P
              (refinedGraph t q U V π j p hq a v φ hφ)
              (refinedBeta t q U V π j p hq a)
              (refinedAlpha t q U V π j p hq a) := by
  exact exists_refined_relativeCurve_lifting t q π j p hq a z s hs H d hd ha v hc φ hφ
    (finiteProjectiveCoefficient R n f) (finiteProjectiveCoefficient_isAmple R n f) x P hP

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
