/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholePolynomialBoundaryFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RefinedSmoothSites
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SignedPencil
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FiniteProjectiveAmple
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.ProperFiniteFrames
public import Colib.AlgebraicGeometry.Morphisms.Smooth.PolynomialProjection

/-!
# A genuine signed pencil with only a coefficient-base shrink

The target parameter is the whole polynomial line. Its global graph frame is
constructed from the actual evaluation kernel. One common principal base open
frames both full finite boundaries. The two relative Serre constructions and
the signed finite-flat pencil are the existing native producers. No parameter
open, coefficient frame, section, endpoint or lifting is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.AmpleProjectiveImmersion
universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {k : Type u} [Field k] (R B : Type u) [CommRing R] [CommRing B]
  [IsNoetherianRing R] (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (n : ℕ) {C Y A D T : Scheme.{u}} [IsAffine Y] [IsAffine A] [IsAffine T]
  (f : C ⟶ projectiveSpaceOverRing n (.of R)) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p]
  (hq : j ≫ (f ≫ (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R))) =
    p ≫ coordinateLineProjection R)
  (a : A ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion a]
  (z : Polynomial R →+* B) [IsFinite (coordinateMark R B z ≫ coordinateLineProjection R)]
  (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = coordinateMark R B z)
  (H : IsPullback s (𝟙 _) p (coordinateMark R B z))
  (d : D ⟶ C) [IsClosedImmersion d]
  [IsClosedImmersion (s ≫ j)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range (coordinateMark R B z)))
  (v : T ⟶ C) [IsOpenImmersion v]
  [SmoothOfRelativeDimension 1
    (v ≫ (f ≫ (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R))))]
  (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
  (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)

local notation "q" => coordinateLineProjection R
set_option quotPrecheck false in
local notation "π" => f ≫ (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R))
local notation "z₀" => coordinateMark R B z

local instance : SmoothOfRelativeDimension 1 q :=
  AffineLineEtaleCompactification.polynomialProjection_smooth_one R

include hs H hd ha hc in
/-- Both sources are restricted only along an actual principal open of the
coefficient base. In particular an original whole punctured line remains whole.
The returned predicate has the original beta-minus-alpha order. -/
theorem exists_wholePolynomial_base_lifting_of_finite_fiber
    [IsProper (d ≫ π)] (w : Spec (.of R)) (hfinite : ((d ≫ π) ⁻¹' {w}).Finite)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V), w ∈ V ∧
      ∃ hW : IsAffineOpen (parameterOpen q ⊤ V),
        letI : IsAffine V.toScheme := hV
        letI : IsAffine (parameterOpen q ⊤ V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (refinedGraph t q ⊤ V π j p hq a v φ hφ)
          (refinedBeta t q ⊤ V π j p hq a)
          (refinedAlpha t q ⊤ V π j p hq a) := by
  let L := finiteProjectiveCoefficient R n f
  have hL : IsAmple C L := finiteProjectiveCoefficient_isAmple R n f
  let : IsFinite (s ≫ j ≫ π) := by
    rw [markedBase_eq q π j p hq z₀ s hs]
    infer_instance
  obtain ⟨U, hwU, hfin, ⟨eD⟩⟩ := exists_base_open_finite_and_frame
    (d ≫ π) w hfinite ((Modules.pullback d).obj L)
  obtain ⟨V₀, hwV₀, ⟨eZ⟩⟩ := exists_finiteTargetFrame_around_finite
    (z₀ ≫ q) ((Modules.pullback (s ≫ j)).obj L) {w} (Set.finite_singleton w)
  obtain ⟨r, hwr, hr⟩ := (Spec (.of R)).exists_basicOpen_subset_of_finite_of_isQuasiAffine
    (Set.finite_singleton w) (U ⊓ V₀)
    (Set.singleton_subset_iff.mpr ⟨hwU, hwV₀ (Set.mem_singleton w)⟩)
  let V := (Spec (.of R)).basicOpen r
  have hV : IsAffineOpen V := (isAffineOpen_top (Spec (.of R))).basicOpen r
  have hW := parameterOpen_affine q ⊤ V (isAffineOpen_top _) hV
  let : IsAffine V.toScheme := hV
  let : IsAffine (parameterOpen q ⊤ V).toScheme := hW
  let : IsFinite ((d ≫ π) ∣_ U) := hfin
  let : IsFinite ((d ≫ π) ∣_ V) :=
    Scheme.RelativeCurve.finite_morphismRestrict_of_le (d ≫ π) (fun _ hx => (hr hx).1)
  let eD' := Stacks.SheafOfModules.restrictIsoUnitOfLE ((Modules.pullback d).obj L)
    (show (d ≫ π) ⁻¹ᵁ V ≤ (d ≫ π) ⁻¹ᵁ U from fun _ hx => (hr hx).1) eD
  let eZ' := Stacks.SheafOfModules.restrictIsoUnitOfLE ((Modules.pullback (s ≫ j)).obj L)
    (show (z₀ ≫ q) ⁻¹ᵁ V ≤ (z₀ ≫ q) ⁻¹ᵁ V₀ from fun _ hx => (hr hx).2) eZ
  let h : ∀ b : Spec (.of B), (z₀ ≫ q) b ∈ V → z₀ b ∈ (⊤ : (Spec (.of (Polynomial R))).Opens) :=
    fun _ _ => trivial
  let q' := parameterProjection q ⊤ V
  let π' := compactificationProjection π V
  let j' := firstInclusion q ⊤ V π j p hq
  let p' := firstMap q ⊤ V p
  let a' := secondMap q ⊤ V a
  let z' := markToParameter q ⊤ V z₀ h
  let s' := closedLift q ⊤ V z₀ h p s hs
  let d' := sourceBaseMap π V d
  let v' := sourceBaseMap π V v
  let φ' := refinedTargetMap q ⊤ V π j p hq a v φ hφ
  let m := markedProductToOriginal q ⊤ V z₀ h
  let e : divisorSheaf (relativeBoundaryGraph q' z').ker ≅
      SheafOfModules.unit (pullback q' (z' ≫ q')).ringCatSheaf :=
    (divisorComapEqIso m (relativeBoundaryGraph q z₀).ker
      (relativeBoundaryGraph q' z').ker
      (markedGraphToOriginal_ideal q ⊤ V z₀ h)).symm ≪≫
        Modules.framePullback m (wholePolynomialBoundaryFrame R B z)
  let : IsAffine (sourceBaseOpen π V v).toScheme := sourceBaseOpen_affine π V v hV
  let : IsFinite (d' ≫ π') := by
    rw [sourceBaseMap_projection]
    infer_instance
  let : IsFinite (s' ≫ j' ≫ π') := by
    rw [← Category.assoc]
    infer_instance
  refine ⟨V, hV, hwr (Set.mem_singleton w), hW, ?_⟩
  exact hasRestrictionDifferenceLifting_of_constructedFrames q' π' j' p'
    (firstInclusion_projection q ⊤ V π j p hq) a' z' s'
    (closedLift_parameter q ⊤ V z₀ h p s hs)
    (closedLift_isPullback q ⊤ V z₀ h p s hs H) e d'
    (refinedInfinity_disjoint q ⊤ V π j p hq d hd)
    (puncture_disjoint q ⊤ V z₀ h a ha) (V.ι ≫ t)
    (pullback.fst p' a') (pullback.snd p' a') pullback.condition v'
    (refinedBoundary_cover q ⊤ V π j p hq z₀ h s hs d v hc) φ'
    (refinedTargetMap_inclusion q ⊤ V π j p hq a v φ hφ)
    (coefficientModule π V L) (coefficientModule_isAmple π V hV L hL)
    (coefficientFrame π V d L eD')
    (refinedMarkCoefficientFrame q ⊤ V π j p hq z₀ h s hs L eZ') P hP

include hs H hd ha hc in
/-- If the whole boundary is finite over the coefficient base, the same
construction applies at every coefficient point. -/
theorem exists_wholePolynomial_base_lifting [IsFinite (d ≫ π)] (w : Spec (.of R))
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V), w ∈ V ∧
      ∃ hW : IsAffineOpen (parameterOpen q ⊤ V),
        letI : IsAffine V.toScheme := hV
        letI : IsAffine (parameterOpen q ⊤ V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (refinedGraph t q ⊤ V π j p hq a v φ hφ)
          (refinedBeta t q ⊤ V π j p hq a)
          (refinedAlpha t q ⊤ V π j p hq a) :=
  exists_wholePolynomial_base_lifting_of_finite_fiber R B t n f j p hq a z s hs H d hd ha
    v hc φ hφ w ((d ≫ π).finite_preimage_singleton w) P hP

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
