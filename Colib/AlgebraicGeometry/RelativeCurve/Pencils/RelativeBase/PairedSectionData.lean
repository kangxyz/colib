/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionData

/-!
# The original source and target section pairs on the same affine base

The two compactifications use one marked parameter line and one graph
frame. On the target side the original marking is the Cartesian
identity square. The source and target section pairs are constructed
by the same native whole-boundary Serre theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

/-- Serre constructs actual source and target section data on the same
coefficient open from their two pairs of whole boundary frames. -/
theorem nonempty_pairedSectionData
    {S X Y A Z C₁ C₂ D₁ D₂ : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    [IsAffine X] [IsAffine Y] [IsAffine A]
    (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (π₁ : C₁ ⟶ S) [IsProper π₁]
    (j₁ : Y ⟶ C₁) [IsOpenImmersion j₁] [SmoothOfRelativeDimension 1 (j₁ ≫ π₁)]
    (p : Y ⟶ X) (hq₁ : j₁ ≫ π₁ = p ≫ q)
    (π₂ : C₂ ⟶ S) [IsProper π₂]
    (j₂ : X ⟶ C₂) [IsOpenImmersion j₂] [SmoothOfRelativeDimension 1 (j₂ ≫ π₂)]
    (hq₂ : j₂ ≫ π₂ = (𝟙 X) ≫ q)
    (a : A ⟶ X) [IsOpenImmersion a] (z : Z ⟶ X)
    (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
    (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
      SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
    (d₁ : D₁ ⟶ C₁) [IsClosedImmersion d₁] [IsClosedImmersion (s ≫ j₁)]
    (hd₁ : Disjoint (Set.range j₁) (Set.range d₁))
    (d₂ : D₂ ⟶ C₂) [IsClosedImmersion d₂] [IsClosedImmersion (z ≫ j₂)]
    (hd₂ : Disjoint (Set.range j₂) (Set.range d₂))
    (ha : Disjoint (Set.range a) (Set.range z))
    (L₁ : C₁.Modules) [IsInvertibleModule C₁ L₁] (hL₁ : IsAmple C₁ L₁)
    (eD₁ : (Modules.pullback d₁).obj L₁ ≅ SheafOfModules.unit D₁.ringCatSheaf)
    (eZ₁ : (Modules.pullback (s ≫ j₁)).obj L₁ ≅ SheafOfModules.unit Z.ringCatSheaf)
    (L₂ : C₂.Modules) [IsInvertibleModule C₂ L₂] (hL₂ : IsAmple C₂ L₂)
    (eD₂ : (Modules.pullback d₂).obj L₂ ≅ SheafOfModules.unit D₂.ringCatSheaf)
    (eZ₂ : (Modules.pullback (z ≫ j₂)).obj L₂ ≅ SheafOfModules.unit Z.ringCatSheaf) :
    Nonempty (SectionData q π₁ j₁ p hq₁ a z s hs H e d₁ hd₁ ha ×
      SectionData q π₂ j₂ (𝟙 X) hq₂ a z z (Category.comp_id z)
        (IsPullback.of_id_snd (f := z)) e d₂ hd₂ ha) := by
  obtain ⟨source⟩ := nonempty_sectionData q π₁ j₁ p hq₁ a z s hs H e d₁ hd₁ ha
    L₁ hL₁ eD₁ eZ₁
  obtain ⟨target⟩ := nonempty_sectionData q π₂ j₂ (𝟙 X) hq₂ a z z (Category.comp_id z)
    (IsPullback.of_id_snd (f := z)) e d₂ hd₂ ha L₂ hL₂ eD₂ eZ₂
  exact ⟨(source, target)⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
