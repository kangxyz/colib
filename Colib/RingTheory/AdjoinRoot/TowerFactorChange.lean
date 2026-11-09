/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactor

/-!
# Changing the actual upper presentation over a fixed root field

The two selected native factors have their actual quotient rings identified with
the original top fields. Composing these identifications with the supplied
base-field equivalence gives an equivalence over the original lower root field.
Its coefficient identity and its square with the two literal `AdjoinRoot.map`
homomorphisms are proved. No lower-field algebra on either top field is introduced.

This supplies the actual relative comparison used in
`Aglib/KTheory/MilnorK/Norm/Polynomial/PrimeSubfieldInduction.lean` at revision
`52e09db47998f139064acf48a2d3a64494d0dd9a`, using only native quotient objects.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

variable {k : Type*} [Field k] (p h₁ h₂ : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h₁)] [Fact (Irreducible h₂)]
  (e : AdjoinRoot h₁ ≃ₐ[k] AdjoinRoot h₂)
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h₁)

local notation "E" => AdjoinRoot p
local notation "q₁" => towerFactor p h₁ f
local notation "q₂" => towerFactor p h₂ (e.toAlgHom.comp f)

/-- Compare the actual relative quotient rings through the original top fields. -/
def towerFactorChangeRingEquiv :
    AdjoinRoot (poly q₁.1.2) ≃+* AdjoinRoot (poly q₂.1.2) :=
  ((towerFactorRingEquiv p h₁ f).trans e.toRingEquiv).trans
    (towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)).symm

/-- The actual lower coefficient maps commute, by the two original embedding formulas. -/
theorem towerFactorChangeRingEquiv_algebraMap (a : AdjoinRoot p) :
    towerFactorChangeRingEquiv p h₁ h₂ e f
      (algebraMap E (AdjoinRoot (poly q₁.1.2)) a) =
        algebraMap E (AdjoinRoot (poly q₂.1.2)) a := by
  apply (towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)).injective
  change towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)
      ((towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)).symm
        (e (towerFactorRingEquiv p h₁ f
          (algebraMap E (AdjoinRoot (poly q₁.1.2)) a)))) =
    towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)
      (algebraMap E (AdjoinRoot (poly q₂.1.2)) a)
  rw [RingEquiv.apply_symm_apply, towerFactorRingEquiv_algebraMap,
    towerFactorRingEquiv_algebraMap]
  rfl

/-- The original upper presentation change gives an actual lower-field algebra equivalence. -/
def towerFactorChangeAlgEquiv :
    AdjoinRoot (poly q₁.1.2) ≃ₐ[AdjoinRoot p] AdjoinRoot (poly q₂.1.2) :=
  { towerFactorChangeRingEquiv p h₁ h₂ e f with
    commutes' := towerFactorChangeRingEquiv_algebraMap p h₁ h₂ e f }

/-- The algebra equivalence retains the constructed quotient ring equivalence. -/
theorem towerFactorChangeAlgEquiv_toRingEquiv :
    (towerFactorChangeAlgEquiv p h₁ h₂ e f).toRingEquiv =
      towerFactorChangeRingEquiv p h₁ h₂ e f := rfl

/-- Cancellation identifies the maps to the second original top field. -/
theorem towerFactorChangeAlgEquiv_comp_towerFactorRingEquiv :
    (towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)).toRingHom.comp
        (towerFactorChangeAlgEquiv p h₁ h₂ e f).toRingHom =
      e.toRingHom.comp (towerFactorRingEquiv p h₁ f).toRingHom := by
  apply RingHom.ext
  intro x
  change towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)
      ((towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)).symm
        (e (towerFactorRingEquiv p h₁ f x))) = e (towerFactorRingEquiv p h₁ f x)
  exact RingEquiv.apply_symm_apply _ _

/-- The actual relative equivalence intertwines the original coefficient-factor maps. -/
theorem towerFactorChangeAlgEquiv_map (b : AdjoinRoot h₁) :
    towerFactorChangeAlgEquiv p h₁ h₂ e f
      (AdjoinRoot.map (algebraMap k E) h₁ (poly q₁.1.2) q₁.2 b) =
    AdjoinRoot.map (algebraMap k E) h₂ (poly q₂.1.2) q₂.2 (e b) := by
  apply (towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)).injective
  change towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)
      ((towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)).symm
        (e (towerFactorRingEquiv p h₁ f
          (AdjoinRoot.map (algebraMap k E) h₁ (poly q₁.1.2) q₁.2 b)))) =
    towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)
      (AdjoinRoot.map (algebraMap k E) h₂ (poly q₂.1.2) q₂.2 (e b))
  rw [RingEquiv.apply_symm_apply, towerFactorRingEquiv_map, towerFactorRingEquiv_map]

/-- The commuting square is equality of the literal original ring homomorphisms. -/
theorem towerFactorChangeAlgEquiv_comp_adjoinRootMap :
    (towerFactorChangeAlgEquiv p h₁ h₂ e f).toRingHom.comp
        (AdjoinRoot.map (algebraMap k E) h₁ (poly q₁.1.2) q₁.2) =
      (AdjoinRoot.map (algebraMap k E) h₂ (poly q₂.1.2) q₂.2).comp e.toRingHom := by
  apply RingHom.ext
  intro b
  exact towerFactorChangeAlgEquiv_map p h₁ h₂ e f b

/-- The relative root is carried to the original changed top root through its actual map. -/
theorem towerFactorChangeAlgEquiv_root :
    towerFactorChangeAlgEquiv p h₁ h₂ e f (root (poly q₁.1.2)) =
      AdjoinRoot.map (algebraMap k E) h₂ (poly q₂.1.2) q₂.2 (e (root h₁)) := by
  simpa only [AdjoinRoot.map_root] using
    towerFactorChangeAlgEquiv_map p h₁ h₂ e f (root h₁)

end AdjoinRoot

end
