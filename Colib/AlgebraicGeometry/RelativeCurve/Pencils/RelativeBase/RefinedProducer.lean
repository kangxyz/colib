/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RefinedSmoothSites
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SignedPencil
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison
/-!
# Constructed relative pencils on an explicit simultaneous refinement

The parameter U, common base V, canonical graph frame, both complete finite
boundary coefficient frames, both Serre section pairs, four finite-flat zero
schemes and actual signed polynomial homotopy are constructed internally. C is
proper over the arbitrary affine Noetherian base S, not over the ground field.
Both independent sources are pulled back to the same new parameter. The target
is the original retained open restricted only by V. The complete nonreduced
mark survives as a Cartesian subscheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open AlgebraicGeometry.Scheme.SmoothSite.Contraction
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {S X C Y A Z D T : Scheme.{u}}
  [IsAffine S] [IsLocallyNoetherian S] [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine T]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j]
  (p : Y ⟶ X) [Etale p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (z : Z ⟶ X) [IsFinite (z ≫ q)]
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (d : D ⟶ C) [IsClosedImmersion d] [IsFinite (d ≫ π)] [IsClosedImmersion (s ≫ j)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range z))
  (v : T ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
  (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)
  (L : C.Modules) [IsInvertibleModule C L] (hL : IsAmple C L)

variable (U : X.Opens) (V : S.Opens)
  [IsAffine V.toScheme] [IsAffine (parameterOpen q U V).toScheme]
  (h : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U)

local notation "q'" => parameterProjection q U V
local notation "π'" => compactificationProjection π V
local notation "j'" => firstInclusion q U V π j p hq
local notation "p'" => firstMap q U V p
local notation "a'" => secondMap q U V a
local notation "z'" => markToParameter q U V z h
local notation "s'" => closedLift q U V z h p s hs
local notation "d'" => sourceBaseMap π V d
local notation "v'" => sourceBaseMap π V v
local notation "φ'" => refinedTargetMap q U V π j p hq a v φ hφ
local notation "α" => pullback.fst p' a'
local notation "β" => pullback.snd p' a'

omit [IsFinite (z ≫ q)] [IsFinite (d ≫ π)] in
include hs H hd ha hc hφ hL in
/-- Application to the actual refined geometry. Its frames are exactly the
intermediate choices constructed by the following existence theorem. -/
private theorem signedPencil_on_constructed_refinement
    (e : divisorSheaf (relativeBoundaryGraph q' z').ker ≅
      SheafOfModules.unit (pullback q' (z' ≫ q')).ringCatSheaf)
    (eD : ((Modules.pullback d).obj L).restrict ((d ≫ π) ⁻¹ᵁ V).ι ≅
      SheafOfModules.unit ((d ≫ π) ⁻¹ᵁ V).toScheme.ringCatSheaf)
    (eZ : ((Modules.pullback (s ≫ j)).obj L).restrict (markOpen q V z).ι ≅
      SheafOfModules.unit (markOpen q V z).toScheme.ringCatSheaf) :
    ∃ lam : Cor.mk (refinedFirstSite t q U V π j p hq) ⟶
        Cor.mk (refinedTargetSite t V π v),
      ∃ psi : Cor.mk (refinedSecondSite t q U V a) ⟶
          Cor.mk (refinedTargetSite t V π v),
        ∃ δ : Cor.mk (affineLineCylinder.obj (refinedOverlapSite t q U V π j p hq a)) ⟶
            Cor.mk (refinedTargetSite t V π v),
          (Cor.graphFunctor k).map (nativeAffineSection (.of k)
            (refinedOverlapSite t q U V π j p hq a) 0) ≫ δ =
              (Cor.graphFunctor k).map (refinedGraph t q U V π j p hq a v φ hφ) ∧
          (Cor.graphFunctor k).map (nativeAffineSection (.of k)
            (refinedOverlapSite t q U V π j p hq a) 1) ≫ δ =
              (Cor.graphFunctor k).map (refinedAlpha t q U V π j p hq a) ≫ lam -
              (Cor.graphFunctor k).map (refinedBeta t q U V π j p hq a) ≫ psi := by
  let : IsAffine (sourceBaseOpen π V v).toScheme :=
    sourceBaseOpen_affine π V v (show IsAffineOpen V from ‹IsAffine V.toScheme›)
  exact exists_signedPencil_of_constructedFrames q' π' j' p'
    (firstInclusion_projection q U V π j p hq) a' z' s'
    (closedLift_parameter q U V z h p s hs)
    (closedLift_isPullback q U V z h p s hs H) e d'
    (refinedInfinity_disjoint q U V π j p hq d hd)
    (puncture_disjoint q U V z h a ha)
    (V.ι ≫ t) α β pullback.condition v'
    (refinedBoundary_cover q U V π j p hq z h s hs d v hc) φ'
    (refinedTargetMap_inclusion q U V π j p hq a v φ hφ)
    (coefficientModule π V L)
    (coefficientModule_isAmple π V (show IsAffineOpen V from ‹IsAffine V.toScheme›) L hL)
    (coefficientFrame π V d L eD)
    (refinedMarkCoefficientFrame q U V π j p hq z h s hs L eZ)

omit [IsAffine V.toScheme] [IsAffine (parameterOpen q U V).toScheme] in
include hs H hd ha hc hL in
/-- Genuine relative geometric pencil existence. Every frame, section and
finite-flat correspondence is constructed. The target remains the original
retained open over V; both source maps are explicitly refined along U and V. -/
theorem exists_refined_signedPencil (x : X) :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U), x ∈ U ∧
      ∃ (V : S.Opens) (hV : IsAffineOpen V), q x ∈ V ∧
        ∃ _h : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U,
          ∃ hW : IsAffineOpen (parameterOpen q U V),
            letI : IsAffine V.toScheme := hV
            letI : IsAffine (parameterOpen q U V).toScheme := hW
            ∃ lam : Cor.mk (refinedFirstSite t q U V π j p hq) ⟶
                Cor.mk (refinedTargetSite t V π v),
              ∃ psi : Cor.mk (refinedSecondSite t q U V a) ⟶
                  Cor.mk (refinedTargetSite t V π v),
                ∃ δ : Cor.mk (affineLineCylinder.obj (refinedOverlapSite t q U V π j p hq a)) ⟶
                    Cor.mk (refinedTargetSite t V π v),
                  (Cor.graphFunctor k).map (nativeAffineSection (.of k)
                    (refinedOverlapSite t q U V π j p hq a) 0) ≫ δ =
                    (Cor.graphFunctor k).map (refinedGraph t q U V π j p hq a v φ hφ) ∧
                  (Cor.graphFunctor k).map (nativeAffineSection (.of k)
                    (refinedOverlapSite t q U V π j p hq a) 1) ≫ δ =
                    (Cor.graphFunctor k).map (refinedAlpha t q U V π j p hq a) ≫ lam -
                    (Cor.graphFunctor k).map (refinedBeta t q U V π j p hq a) ≫ psi := by
  obtain ⟨u, hxu, r, hxr, h, ⟨e⟩, ⟨eD⟩, ⟨eZ⟩⟩ :=
    exists_canonicalGraph_and_coefficient_frames q z π d (s ≫ j) L x
  let U := X.basicOpen u
  let V := S.basicOpen r
  have hU : IsAffineOpen U := (isAffineOpen_top X).basicOpen u
  have hV : IsAffineOpen V := (isAffineOpen_top S).basicOpen r
  have hW := parameterOpen_affine q U V hU hV
  let : IsAffine V.toScheme := hV
  let : IsAffine (parameterOpen q U V).toScheme := hW
  exact ⟨U, hU, hxu, V, hV, hxr, h, hW,
    signedPencil_on_constructed_refinement t q π j p hq a z s hs H d hd ha
      v hc φ hφ L hL U V h e eD eZ⟩

omit [IsAffine V.toScheme] [IsAffine (parameterOpen q U V).toScheme] in
include hs H hd ha hc hL in
/-- The original restriction-difference lifting on a genuinely constructed
same-base refinement. No desired frame, section, local-zero or lifting provider
is an input. This is the native general-relative-base RefinedLifting endpoint. -/
theorem exists_refined_relativeCurve_lifting (x : X)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U), x ∈ U ∧
      ∃ (V : S.Opens) (hV : IsAffineOpen V), q x ∈ V ∧
        ∃ _h : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U,
          ∃ hW : IsAffineOpen (parameterOpen q U V),
            letI : IsAffine V.toScheme := hV
            letI : IsAffine (parameterOpen q U V).toScheme := hW
            PresheafWithTransfers.HasRestrictionDifferenceLifting P
              (refinedGraph t q U V π j p hq a v φ hφ)
              (refinedBeta t q U V π j p hq a)
              (refinedAlpha t q U V π j p hq a) := by
  obtain ⟨U, hU, hxU, V, hV, hxV, h, hW, lam, psi, δ, h₀, h₁⟩ :=
    exists_refined_signedPencil t q π j p hq a z s hs H d hd ha v hc φ hφ L hL x
  let : IsAffine V.toScheme := hV
  let : IsAffine (parameterOpen q U V).toScheme := hW
  exact ⟨U, hU, hxU, V, hV, hxV, h, hW,
    PresheafWithTransfers.hasRestrictionDifferenceLifting_of_homotopy P hP _ _ _
      lam psi δ h₀ h₁⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
