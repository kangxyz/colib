/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryFrameCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FiniteBoundaryFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeBoundaryClosed
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedCoordinateUnit

/-!
# Boundary frames for moving over an affine source neighborhood

Trivialize the graph and coefficient lines on the entire finite boundary
above an affine source neighborhood. The graph frame uses the canonical
infinity frame on the infinity summand.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Moving/OneSidedRefinedFrames.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open Stacks.Ample

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable {S C Y D Z : Scheme.{u}}
  (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (d : D ⟶ C) [IsFinite (d ≫ π)] (s : Z ⟶ Y) [IsFinite (s ≫ j ≫ π)]
  (hd : Disjoint (Set.range j) (Set.range d))

local notation "P" => pullback (j ≫ π) π
local notation "p" => pullback.fst (j ≫ π) π
local notation "F" => divisorSheaf (Scheme.Hom.ker (compactificationGraph π j))
local notation "σ" => divisorSheafGlobalSection (Scheme.Hom.ker (compactificationGraph π j))
local notation "i₀" => fullGraphBoundaryMap π j s d

include hd in
/-- The actual coefficient frame and the graph frame with unit infinity
coordinate exist on the same complete boundary above an affine neighborhood. -/
theorem exists_affineMovingBoundaryFrames (L : (P).Modules) [IsInvertibleModule P L] (x : Y) :
    ∃ U : Y.affineOpens, x ∈ U.1 ∧
      let u := U.1.ι
      let g := commonToLambda π j u
      let D' := commonInfinity π j u d
      let Z' := commonZero π j u s
      let i := commonBoundaryInclusion π j u s d
      ∃ E : (Modules.pullback i).obj ((Modules.pullback g).obj F) ≅
          SheafOfModules.unit (D' ⨿ Z').ringCatSheaf,
        (coprod.inl : D' ⟶ D' ⨿ Z').appTop
          (E.hom.app ⊤ (pullbackGlobalSections i _
            (pullbackGlobalSections g F σ))) = 1 ∧
        Nonempty ((Modules.pullback i).obj ((Modules.pullback g).obj L) ≅
          SheafOfModules.unit (D' ⨿ Z').ringCatSheaf) := by
  let b := i₀ ≫ p
  have : IsFinite b := fullGraphBoundary_isFinite π j d s
  obtain ⟨V, hxV, ⟨eF⟩, ⟨eL⟩⟩ := exists_wholeFiniteBoundary_pair_frames b
    ((Modules.pullback i₀).obj F) ((Modules.pullback i₀).obj L) x
  obtain ⟨-, ⟨U₀, hU, rfl⟩, hxU, hUV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  let U : Y.Opens := U₀
  let u := U.ι
  let g := commonToLambda π j u
  let D' := commonInfinity π j u d
  let Z' := commonZero π j u s
  let iD : D' ⟶ commonAmbient π j u := pullback.fst _ _
  let iZ := commonZeroInclusion π j u s
  let i := commonBoundaryInclusion π j u s d
  let β := commonBoundaryToLambda π j u s d
  have hβ : β ≫ b = (i ≫ pullback.fst (commonProjection π j u) π) ≫ u := by
    calc
      _ = (β ≫ i₀) ≫ p := (Category.assoc _ _ _).symm
      _ = (i ≫ g) ≫ p := by rw [commonBoundaryToLambda_inclusion]
      _ = _ := by rw [Category.assoc, (commonToLambda_isPullback π j u).w, ← Category.assoc]
  have hβU : Set.range β ⊆ Set.range ((b ⁻¹ᵁ U).ι) := by
    rintro _ ⟨y, rfl⟩
    rw [Opens.range_ι]
    change b (β y) ∈ U
    rw [show b (β y) = u (pullback.fst (commonProjection π j u) π (i y)) from
      congrArg (fun f => f y) hβ]
    exact (pullback.fst (commonProjection π j u) π (i y)).2
  let βU := IsOpenImmersion.lift (b ⁻¹ᵁ U).ι β hβU
  have hβUfac : βU ≫ (b ⁻¹ᵁ U).ι = β := IsOpenImmersion.lift_fac _ _ _
  have hSquare : i ≫ g = βU ≫ ((b ⁻¹ᵁ U).ι ≫ i₀) := by
    rw [← Category.assoc, hβUfac]
    exact (commonBoundaryToLambda_inclusion π j u s d).symm
  let e (M : (P).Modules) (E : ((Modules.pullback i₀).obj M).restrict (b ⁻¹ᵁ V).ι ≅
      SheafOfModules.unit (b ⁻¹ᵁ V).toScheme.ringCatSheaf) :=
    sourceChangedBoundaryFrame g _ i βU hSquare M
      (wholeBoundaryPullbackFrame b i₀ M U (Stacks.SheafOfModules.restrictIsoUnitOfLE
        ((Modules.pullback i₀).obj M) (fun _ h => hUV h) E))
  let F' := (Modules.pullback g).obj F
  let E₀ := e F eF
  let r : Z' ⟶ D' ⨿ Z' := coprod.inr
  let eZ : (Modules.pullback iZ).obj F' ≅ SheafOfModules.unit Z'.ringCatSheaf :=
    ((Modules.pullbackCongr (coprod.inr_desc iD iZ)).app F').symm ≪≫
      ((Modules.pullbackComp r i).app F').symm ≪≫ Modules.framePullback r E₀
  let βD := constantInfinitySourceMap u (j ≫ π) π (commonProjection π j u) rfl d
  have hD : iD ≫ g = βD ≫ infinityProductMap π j d :=
    (constantInfinitySourceMap_fst u (j ≫ π) π (commonProjection π j u) rfl d).symm
  let eD := sourceChangedBoundaryFrame g (infinityProductMap π j d) iD βD hD F
    (compactificationInfinityDivisorFrame π j d hd)
  have heD : eD.hom.app ⊤ (pullbackGlobalSections iD F' (pullbackGlobalSections g F σ)) =
      (1 : Γ(D', ⊤)) := by
    rw [sourceChangedBoundaryFrame_coordinate, compactificationInfinityDivisorFrame_coordinate,
      map_one]
  obtain ⟨E, hED, _⟩ := exists_boundaryCoprod_frame iD iZ F' eD eZ
  exact ⟨⟨U, hU⟩, hxU, E,
    (boundaryCoprodFrame_inl_coordinate iD iZ F' E eD hED _).trans heD, ⟨e L eL⟩⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
