/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# Exact integral closed supports on open neighborhoods

New recovery reconstruction from the retained proof route, 2026-11-08. Uncompiled.
The previous corresponding next-stage draft was also unvalidated. This file is not
asserted to be byte-identical to that draft.

A nonempty actual open inverse image of an integral closed subscheme is integral.
Native `integralComponentAt_genericPointOf` identifies its actual ideal sheaf, not
merely its topological support. Products and later inverse-image schemes retain
all nilpotents. The source map is native `IdealSheafData.subschemeMap`.

Native references: Mathlib `IdealSheafData.comapIso_hom_snd`,
`Scheme.Pullback.range_snd`, `isIntegral_of_isOpenImmersion`; Stacks
`Chow.integralComponentAt_genericPointOf` (the uniqueness clause of Tag 01J3).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

/-- Construct a point indexing the exact inverse-image ideal and an actual open support
map, including its precise range and a lift of the specified original support point. -/
theorem exists_openIntegralComponentAt {X U : Scheme.{u}}
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (u : U ⟶ X) [IsOpenImmersion u]
    (t : I.subscheme) (ht : I.subschemeι t ∈ Set.range u) :
    ∃ z : U, integralComponentAt z = I.comap u ∧
    ∃ v : (integralComponentAt z).subscheme ⟶ I.subscheme,
      IsOpenImmersion v ∧
      v ≫ I.subschemeι = (integralComponentAt z).subschemeι ≫ u ∧
      Set.range v = I.subschemeι ⁻¹' Set.range u ∧
      ∃ t', v t' = t := by
  let v := (I.comap u).subschemeMap I u (I.le_map_comap u)
  have hv : IsOpenImmersion v := by
    dsimp [v]
    rw [← I.comapIso_hom_snd u]
    infer_instance
  let := hv
  have hr : Set.range v = I.subschemeι ⁻¹' Set.range u := by
    rw [← Scheme.Pullback.range_snd u I.subschemeι]
    ext s
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨(I.comapIso u).hom q, ?_⟩
      change ((I.comapIso u).hom ≫ pullback.snd u I.subschemeι) q = v q
      rw [I.comapIso_hom_snd]
    · rintro ⟨q, hq⟩
      refine ⟨(I.comapIso u).inv q, ?_⟩
      change ((I.comap u).subschemeMap I u (I.le_map_comap u))
        ((I.comapIso u).inv q) = s
      rw [← I.comapIso_hom_snd u]
      change pullback.snd u I.subschemeι
        ((I.comapIso u).hom ((I.comapIso u).inv q)) = s
      rw [Scheme.inv_hom_apply, hq]
  have ht' : t ∈ Set.range v := by rw [hr]; exact ht
  obtain ⟨t', ht'⟩ := ht'
  let : Nonempty (I.comap u).subscheme := ⟨t'⟩
  have hI : IsIntegral (I.comap u).subscheme := isIntegral_of_isOpenImmersion v
  let z := genericPointOf (I.comap u) hI
  have hz : integralComponentAt z = I.comap u :=
    integralComponentAt_genericPointOf (I.comap u) hI
  refine ⟨z, hz, ?_⟩
  rw [hz]
  exact ⟨v, hv, (I.comap u).subschemeMap_subschemeι I u (I.le_map_comap u),
    hr, t', ht'⟩

end Stacks.Chow
