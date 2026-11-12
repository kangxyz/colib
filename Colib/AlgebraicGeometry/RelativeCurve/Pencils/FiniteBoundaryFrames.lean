/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.InverseSections
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FixedFactorRestriction

/-!
# Frames on the entire finite boundary above one base neighbourhood

Pinned Tag 0BUT trivializes an invertible module on the full inverse image of a
base neighbourhood. Apply it to the actual pulled-back ample line and the fixed
factor, intersect the two neighbourhoods, and propagate the ample-line frame to
all tensor powers. The result is the coefficient-frame input of the original
Serre construction, now produced from finiteness rather than assumed.

The original relative graph frame uses the same finite-base-neighbourhood route
in `Modules/Invertible/Frames/RelativeCurve/BoundaryFrame.lean`, blob
`4267a7b7abd741f65b7f1a9ae7b95a10608a8540`, at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
The prescribed marked graph coordinate is not replaced by an arbitrary frame here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.SheafOfModules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

variable {B C Z : Scheme.{u}} (b : Z ⟶ B) [IsFinite b]

/-- Two actual invertible boundary modules admit frames on the same entire
inverse image of a neighbourhood. No frame or fibre-triviality is an input. -/
theorem exists_wholeFiniteBoundary_pair_frames
    (M N : Z.Modules) [hM : IsInvertibleModule Z M] [hN : IsInvertibleModule Z N] (x : B) :
    ∃ U : B.Opens, x ∈ U ∧
      Nonempty (M.restrict (b ⁻¹ᵁ U).ι ≅
        SheafOfModules.unit (b ⁻¹ᵁ U).toScheme.ringCatSheaf) ∧
      Nonempty (N.restrict (b ⁻¹ᵁ U).ι ≅
        SheafOfModules.unit (b ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  let : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry Z.presheaf Z.ringCatSheaf.2 M).2 hM
  let : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 N :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry Z.presheaf Z.ringCatSheaf.2 N).2 hN
  obtain ⟨U, hxU, ⟨eM⟩⟩ := Stacks.Divisors.hasTrivializingTargetCover_of_isFinite b M x
  obtain ⟨V, hxV, ⟨eN⟩⟩ := Stacks.Divisors.hasTrivializingTargetCover_of_isFinite b N x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact Stacks.SheafOfModules.restrictIsoUnitOfLE M
      (fun _ h => h.1) eM
  · exact Stacks.SheafOfModules.restrictIsoUnitOfLE N
      (fun _ h => h.2) eN

/-- The frame above a whole inverse image is a frame of the literal composite
pullback, through the canonical restriction and pullback-composition maps. -/
def wholeBoundaryPullbackFrame (i : Z ⟶ C) (L : C.Modules) (U : B.Opens)
    (e : ((Modules.pullback i).obj L).restrict (b ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit (b ⁻¹ᵁ U).toScheme.ringCatSheaf) :
    (Modules.pullback ((b ⁻¹ᵁ U).ι ≫ i)).obj L ≅
      SheafOfModules.unit (b ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  ((Modules.pullbackComp (b ⁻¹ᵁ U).ι i).app L).symm ≪≫
    ((Modules.restrictFunctorIsoPullback (b ⁻¹ᵁ U).ι).app
      ((Modules.pullback i).obj L)).symm ≪≫ e

/-- An actual boundary frame trivializes the pullback of the ample tensor power.
The canonical Stacks comparison identifies the two constructions of the power. -/
theorem exists_tensorPowModule_boundaryFrame {X Y : Scheme.{u}} (i : Y ⟶ X)
    (L : X.Modules) [IsInvertibleModule X L]
    (e : (Modules.pullback i).obj L ≅ SheafOfModules.unit Y.ringCatSheaf) (n : ℤ) :
    Nonempty ((Modules.pullback i).obj (tensorPowModule X L n) ≅
      SheafOfModules.unit Y.ringCatSheaf) := by
  obtain ⟨e'⟩ := Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_pullback_tensorPower
    i L ⟨e⟩ n
  let e'' : (Modules.pullback i).obj (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L n) ≅
      SheafOfModules.unit Y.ringCatSheaf := e'
  exact ⟨((Modules.pullback i).mapIso (Stacks.PowerFamilyBridge.tensorPowerModuleIso X L n)).symm
    ≪≫ e''⟩

/-- Every ample coefficient power and its fixed-factor twist has an actual frame
on one common whole boundary neighbourhood. This quantifies over all powers
after choosing the neighbourhood, as required before choosing the Serre bound. -/
theorem exists_wholeFiniteBoundary_power_frames (i : Z ⟶ C)
    (L F : C.Modules) [IsInvertibleModule C L] [IsInvertibleModule C F] (x : B) :
    ∃ U : B.Opens, x ∈ U ∧ ∀ n : ℤ,
      Nonempty ((Modules.pullback ((b ⁻¹ᵁ U).ι ≫ i)).obj
          (tensorPowModule C L n) ≅
        SheafOfModules.unit (b ⁻¹ᵁ U).toScheme.ringCatSheaf) ∧
      Nonempty ((Modules.pullback ((b ⁻¹ᵁ U).ι ≫ i)).obj
          ((Stacks.AlgebraicGeometry.RelativeSerreVanishing.twistFunctor L n).obj F) ≅
        SheafOfModules.unit (b ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  obtain ⟨U, hx, ⟨eL⟩, ⟨eF⟩⟩ := exists_wholeFiniteBoundary_pair_frames b
    ((Modules.pullback i).obj L) ((Modules.pullback i).obj F) x
  let j := (b ⁻¹ᵁ U).ι ≫ i
  let eL' := wholeBoundaryPullbackFrame b i L U eL
  let eF' := wholeBoundaryPullbackFrame b i F U eF
  refine ⟨U, hx, fun n => ?_⟩
  obtain ⟨en⟩ := exists_tensorPowModule_boundaryFrame j L eL' n
  refine ⟨⟨en⟩, ⟨?_⟩⟩
  exact Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso j F
      (tensorPowModule C L n) ≪≫
    tensorProductIso _ _ eF' en ≪≫ tensorProductLeftUnitor _ _ _

/-- A neighbourhood of one point of the image of `Spec K` contains the entire
marked field-valued map, with no finite-extension or rational-point assumption. -/
theorem fieldMark_range_subset {K : Type u} [Field K] (z : Spec (.of K) ⟶ B)
    (a : Spec (.of K)) (U : B.Opens) (h : z a ∈ U) : Set.range z ⊆ U := by
  let : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  rintro _ ⟨a', rfl⟩
  change z a' ∈ U
  rwa [Subsingleton.elim a' a]

omit [IsFinite b] in
/-- The same neighbourhood retains every point of the designated whole fibre. -/
theorem wholeFiniteBoundary_fiber_retained (x : B) (U : B.Opens) (hx : x ∈ U) :
    b ⁻¹' {x} ⊆ (b ⁻¹ᵁ U : Set Z) := by
  intro z hz
  change b z ∈ U
  have hz' : b z = x := hz
  simpa only [hz'] using hx

/-- The frame-producing neighbourhood retains the complete field-valued mark and
the whole finite fibre, while its power frames have been genuinely constructed. -/
theorem exists_wholeFiniteBoundary_power_frames_at_fieldMark (i : Z ⟶ C)
    (L F : C.Modules) [IsInvertibleModule C L] [IsInvertibleModule C F]
    {K : Type u} [Field K] (z : Spec (.of K) ⟶ B) (a : Spec (.of K)) :
    ∃ U : B.Opens, Set.range z ⊆ U ∧ b ⁻¹' {z a} ⊆ (b ⁻¹ᵁ U : Set Z) ∧
      ∀ n : ℤ,
        Nonempty ((Modules.pullback ((b ⁻¹ᵁ U).ι ≫ i)).obj
            (tensorPowModule C L n) ≅
          SheafOfModules.unit (b ⁻¹ᵁ U).toScheme.ringCatSheaf) ∧
        Nonempty ((Modules.pullback ((b ⁻¹ᵁ U).ι ≫ i)).obj
            ((Stacks.AlgebraicGeometry.RelativeSerreVanishing.twistFunctor L n).obj F) ≅
          SheafOfModules.unit (b ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  obtain ⟨U, hx, he⟩ := exists_wholeFiniteBoundary_power_frames b i L F (z a)
  exact ⟨U, fieldMark_range_subset z a U hx,
    wholeFiniteBoundary_fiber_retained b (z a) U hx, he⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
