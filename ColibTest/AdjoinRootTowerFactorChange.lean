module

import Colib.RingTheory.AdjoinRoot.TowerFactorChange

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

variable {k : Type*} [Field k] (p h₁ h₂ : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h₁)] [Fact (Irreducible h₂)]
  (e : AdjoinRoot h₁ ≃ₐ[k] AdjoinRoot h₂)
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h₁)

local notation "E" => AdjoinRoot p
local notation "q₁" => towerFactor p h₁ f
local notation "q₂" => towerFactor p h₂ (e.toAlgHom.comp f)

/-- Both objects remain the native factors with their actual divisibility proofs. -/
example : poly q₁.1.2 ∣ h₁.map (algebraMap k E) := q₁.2

example : poly q₂.1.2 ∣ h₂.map (algebraMap k E) := q₂.2

/-- This is literally the composition through the two original top fields. -/
example : towerFactorChangeRingEquiv p h₁ h₂ e f =
    ((towerFactorRingEquiv p h₁ f).trans e.toRingEquiv).trans
      (towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)).symm := rfl

example (a : AdjoinRoot p) :
    towerFactorChangeRingEquiv p h₁ h₂ e f
      (algebraMap E (AdjoinRoot (poly q₁.1.2)) a) =
        algebraMap E (AdjoinRoot (poly q₂.1.2)) a :=
  towerFactorChangeRingEquiv_algebraMap p h₁ h₂ e f a

/-- The base is the actual root field, without an algebra structure on either top field. -/
example : AdjoinRoot (poly q₁.1.2) ≃ₐ[AdjoinRoot p] AdjoinRoot (poly q₂.1.2) :=
  towerFactorChangeAlgEquiv p h₁ h₂ e f

example : (towerFactorChangeAlgEquiv p h₁ h₂ e f).toRingEquiv =
    towerFactorChangeRingEquiv p h₁ h₂ e f :=
  towerFactorChangeAlgEquiv_toRingEquiv p h₁ h₂ e f

example (a : AdjoinRoot p) :
    towerFactorChangeAlgEquiv p h₁ h₂ e f
      (algebraMap E (AdjoinRoot (poly q₁.1.2)) a) =
        algebraMap E (AdjoinRoot (poly q₂.1.2)) a :=
  (towerFactorChangeAlgEquiv p h₁ h₂ e f).commutes a

example :
    (towerFactorRingEquiv p h₂ (e.toAlgHom.comp f)).toRingHom.comp
        (towerFactorChangeAlgEquiv p h₁ h₂ e f).toRingHom =
      e.toRingHom.comp (towerFactorRingEquiv p h₁ f).toRingHom :=
  towerFactorChangeAlgEquiv_comp_towerFactorRingEquiv p h₁ h₂ e f

example (b : AdjoinRoot h₁) :
    towerFactorChangeAlgEquiv p h₁ h₂ e f
      (AdjoinRoot.map (algebraMap k E) h₁ (poly q₁.1.2) q₁.2 b) =
    AdjoinRoot.map (algebraMap k E) h₂ (poly q₂.1.2) q₂.2 (e b) :=
  towerFactorChangeAlgEquiv_map p h₁ h₂ e f b

/-- The literal original homomorphisms, not assumed abstract comparison maps. -/
example :
    (towerFactorChangeAlgEquiv p h₁ h₂ e f).toRingHom.comp
        (AdjoinRoot.map (algebraMap k E) h₁ (poly q₁.1.2) q₁.2) =
      (AdjoinRoot.map (algebraMap k E) h₂ (poly q₂.1.2) q₂.2).comp e.toRingHom :=
  towerFactorChangeAlgEquiv_comp_adjoinRootMap p h₁ h₂ e f

example : towerFactorChangeAlgEquiv p h₁ h₂ e f (root (poly q₁.1.2)) =
    AdjoinRoot.map (algebraMap k E) h₂ (poly q₂.1.2) q₂.2 (e (root h₁)) :=
  towerFactorChangeAlgEquiv_root p h₁ h₂ e f

/-- The reverse map square follows from the same actual equivalence. -/
example (b : AdjoinRoot h₁) :
    (towerFactorChangeAlgEquiv p h₁ h₂ e f).symm
      (AdjoinRoot.map (algebraMap k E) h₂ (poly q₂.1.2) q₂.2 (e b)) =
    AdjoinRoot.map (algebraMap k E) h₁ (poly q₁.1.2) q₁.2 b := by
  rw [← towerFactorChangeAlgEquiv_map]
  exact (towerFactorChangeAlgEquiv p h₁ h₂ e f).symm_apply_apply _

end
