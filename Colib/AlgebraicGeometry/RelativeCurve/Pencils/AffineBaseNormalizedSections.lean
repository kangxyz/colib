/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FiniteBoundaryFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedCoordinateUnit
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.NormalizedBoundarySections
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic

/-!
# Actual normalized sections after one affine base neighbourhood

Finiteness of the entire boundary produces a coefficient frame above a base
neighbourhood. Refining that neighbourhood to an affine open retains its full
inverse image. Native affine base change preserves ampleness and properness.
Only then is the Serre exponent chosen. Consequently no coefficient-power
frames or global sections are supplied as hypotheses.

The fixed factor retains the actual original whole-boundary frame through the
canonical commuting-square pullback comparison. A neighbourhood of the image
of a field-valued mark retains the whole mark and the entire designated fibre.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.AlgebraicGeometry.RelativeSerreVanishing

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

variable {S X Z : Scheme.{u}}

/-- Tag 0BUT can be refined to one affine base neighbourhood without discarding
any points or scheme structure of its inverse image. -/
theorem exists_affine_wholeFiniteBoundary_frame (b : Z ⟶ S) [IsFinite b]
    (M : Z.Modules) [IsInvertibleModule Z M] (x : S) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧
      Nonempty (M.restrict (b ⁻¹ᵁ U.1).ι ≅
        SheafOfModules.unit (b ⁻¹ᵁ U.1).toScheme.ringCatSheaf) := by
  letI : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).2 inferInstance
  obtain ⟨U, hx, ⟨e⟩⟩ := Stacks.Divisors.hasTrivializingTargetCover_of_isFinite b M x
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  exact ⟨⟨V, hV⟩, hxV, ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE M
    (fun _ hz => hVU hz) e⟩⟩

/-- The literal restriction of the complete boundary to the base neighbourhood. -/
abbrev baseRestrictedBoundary (f : X ⟶ S) (i : Z ⟶ X) (U : S.Opens) :=
  i ∣_ (f ⁻¹ᵁ U)

/-- The fixed-factor frame after actual base restriction. -/
def baseRestrictedBoundaryFrame (f : X ⟶ S) (i : Z ⟶ X) (U : S.Opens)
    (F : X.Modules)
    (e : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (Modules.pullback (baseRestrictedBoundary f i U)).obj
      ((Modules.pullback (f ⁻¹ᵁ U).ι).obj F) ≅
        SheafOfModules.unit (i ⁻¹ᵁ (f ⁻¹ᵁ U)).toScheme.ringCatSheaf :=
  sourceChangedBoundaryFrame (f ⁻¹ᵁ U).ι i (baseRestrictedBoundary f i U)
    (i ⁻¹ᵁ (f ⁻¹ᵁ U)).ι (morphismRestrict_ι i (f ⁻¹ᵁ U)) F e

/-- Actual normalized global pairs after one affine base shrink. The coefficient
frame is produced from the finite whole boundary, and the fixed factor need not
be ample. The whole boundary zero schemes are empty, not merely generically so. -/
theorem exists_affineBase_normalized_sections (f : X ⟶ S)
    [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ f)]
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    (F : X.Modules) [IsInvertibleModule X F]
    (e : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf) (x : S) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧
      let LU := (Modules.pullback (f ⁻¹ᵁ U.1).ι).obj L
      let FU := (Modules.pullback (f ⁻¹ᵁ U.1).ι).obj F
      let iU := baseRestrictedBoundary f i U.1
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ a : Γ((twistFunctor LU (n : ℤ)).obj FU, ⊤),
        ∃ b : Γ(tensorPowModule (f ⁻¹ᵁ U.1).toScheme LU (n : ℤ), ⊤),
          (fixedFactorBoundaryIso iU FU
            (tensorPowModule (f ⁻¹ᵁ U.1).toScheme LU (n : ℤ))
            (baseRestrictedBoundaryFrame f i U.1 F e)).hom.app ⊤
              (pullbackGlobalSections iU _ a) = pullbackGlobalSections iU _ b ∧
          zeroScheme (i ⁻¹ᵁ (f ⁻¹ᵁ U.1)).toScheme
            ((Modules.pullback iU).obj ((twistFunctor LU (n : ℤ)).obj FU))
            (pullbackGlobalSections iU _ a) = ⊤ ∧
          zeroScheme (i ⁻¹ᵁ (f ⁻¹ᵁ U.1)).toScheme
            ((Modules.pullback iU).obj (tensorPowModule (f ⁻¹ᵁ U.1).toScheme LU (n : ℤ)))
            (pullbackGlobalSections iU _ b) = ⊤ := by
  obtain ⟨U, hx, ⟨eL⟩⟩ := exists_affine_wholeFiniteBoundary_frame (i ≫ f)
    ((Modules.pullback i).obj L) x
  rw [Scheme.Hom.comp_preimage] at eL
  let g := (f ⁻¹ᵁ U.1).ι
  let β := (i ⁻¹ᵁ (f ⁻¹ᵁ U.1)).ι
  let iU := baseRestrictedBoundary f i U.1
  let LU := (Modules.pullback g).obj L
  let FU := (Modules.pullback g).obj F
  letI : IsAffine U.1.toScheme := U.2
  letI : IsProper (f ∣_ U.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U.1).flip inferInstance
  letI : IsClosedImmersion iU :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict i (f ⁻¹ᵁ U.1)).flip
      inferInstance
  letI : IsAffineHom g :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U.1) inferInstance
  have hLU : IsAmple (f ⁻¹ᵁ U.1).toScheme LU :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom g L hL
  let eLU : (Modules.pullback iU).obj LU ≅
      SheafOfModules.unit (i ⁻¹ᵁ (f ⁻¹ᵁ U.1)).toScheme.ringCatSheaf :=
    boundaryPullbackSquareIso g i iU β (morphismRestrict_ι i (f ⁻¹ᵁ U.1)) L ≪≫
      ((Modules.restrictFunctorIsoPullback β).app ((Modules.pullback i).obj L)).symm ≪≫ eL
  obtain ⟨N, hN⟩ := exists_eventually_normalized_boundary_sections iU (f ∣_ U.1) LU hLU FU
    (baseRestrictedBoundaryFrame f i U.1 F e)
  refine ⟨U, hx, N, fun n hn => ?_⟩
  obtain ⟨en⟩ := Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_pullback_tensorPower
    iU LU ⟨eLU⟩ (n : ℤ)
  exact hN n hn en

end AlgebraicGeometry.Scheme.RelativeCurvePencil
