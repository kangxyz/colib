/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFullOpenBassLocalization

/-!
# Signed localization boundary on the original fine coefficient telescopes

The original signed same-null cone boundary is expressed on the actual full-open
telescope by the established cone comparison. Exactness uses the literal
restriction and support-forgetting maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The same-null signed boundary, expressed on the actual fine full-open telescope. -/
def boundedAboveFlatCoefficientFineLocalizationConnecting (a : Under R) (d : ℤ) :
    stableHomotopyGroup ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)
      (d + 1) ⟶
      stableHomotopyGroup ((boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f).obj a) d :=
  let := boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence
    f a (d + 1)
  inv ((stableHomotopyFunctor (d + 1)).map
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a)) ≫
      stableMappingConeConnecting
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
        (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a)
          d

/-- The fixed full-open boundary is exact after the original telescope restriction. -/
theorem boundedAboveFlatCoefficientFineLocalizationConnecting_exact_open (a : Under R) (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map
      ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a))
      (boundedAboveFlatCoefficientFineLocalizationConnecting f a d) := by
  let H := stableHomotopyFunctor (d + 1)
  let c := H.map ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a)
  let : IsIso c :=
    boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a (d + 1)
  have hi : H.map (mappingConeInclusion
      ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)) ≫ c =
      H.map ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a) := by
    rw [← H.map_comp]
    exact congrArg H.map
      (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_inclusion f a)
  have he := stableMappingConeConnecting_exact_cone
    ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
    (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
  intro y
  change stableMappingConeConnecting
    ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
    (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
      (inv c y) = 0 ↔ _
  rw [he]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hi, ConcreteCategory.comp_apply, hx]
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id c) y
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    rw [← hi, ConcreteCategory.comp_apply]
    exact (ConcreteCategory.congr_hom (IsIso.hom_inv_id c) _).symm

/-- The fixed boundary is exact before the original telescope support-forgetting map. -/
theorem boundedAboveFlatCoefficientFineLocalizationConnecting_exact_supported
    (a : Under R) (d : ℤ) :
    Function.Exact (boundedAboveFlatCoefficientFineLocalizationConnecting f a d)
      ((stableHomotopyFunctor d).map
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)) := by
  let c := (stableHomotopyFunctor (d + 1)).map
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a)
  let : IsIso c :=
    boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a (d + 1)
  have he := stableMappingConeConnecting_exact_source
    ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
    (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
  intro y
  rw [he]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨c z, ?_⟩
    change stableMappingConeConnecting
      ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
      (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
        (inv c (c z)) = y
    rw [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply]
    exact hz
  · rintro ⟨z, hz⟩
    exact ⟨inv c z, hz⟩

/-- The original same-null fine localization maps are exact at the ambient telescope group. -/
theorem boundedAboveFlatCoefficientSupportedBassTelescope_fullOpen_exact
    (a : Under R) (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a))
      ((stableHomotopyFunctor d).map
        ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)) := by
  let H := stableHomotopyFunctor d
  let j := (boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a
  let c := (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a
  let : IsIso (H.map c) :=
    boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a d
  have hb := stableMappingCone_exact_target j
    (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d
  have he := hb.comp_injective (H.map c)
    (ConcreteCategory.bijective_of_isIso (H.map c)).injective (map_zero (H.map c).hom)
  have hc : H.map (mappingConeInclusion j) ≫ H.map c =
      H.map ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a) := by
    rw [← H.map_comp]
    exact congrArg H.map
      (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_inclusion f a)
  change Function.Exact (H.map j)
    (H.map ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a))
  rw [← hc]
  exact he

end AlgebraicGeometry.Scheme.Modules
