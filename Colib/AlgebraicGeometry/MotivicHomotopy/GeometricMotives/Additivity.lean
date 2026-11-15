/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Coproducts.Finite
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Representable
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Triangulated

/-! # Additivity of smooth correspondence motives -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

instance effectiveMotive_additive : (effectiveMotive k).Additive where
  map_add := by
    intro X Y f g
    let : (representableLarge k).Additive := ⟨by
      intro U V α β
      ext Z a
      change ULift.up (a.down ≫ (α + β)) = ULift.up (a.down ≫ α + a.down ≫ β)
      rw [Preadditive.comp_add]⟩
    let : (singularSheafCochainFunctor k 0).Additive := by
      unfold singularSheafCochainFunctor singularCochainFunctor
      infer_instance
    apply (effectiveMotivesMinusToDerived k).map_injective
    exact (representableLarge k ⋙ singularSheafCochainFunctor k 0 ⋙
      DerivedCategory.Q).map_add

/-- Motives of the actual component inclusions exhibit the finite disjoint-union motive
as a coproduct, including the empty union. -/
def effectiveMotiveFiniteCoproductIsColimit {n : ℕ}
    (Y : Fin n → SmoothSite (Spec (.of k))) :
    IsColimit (Cofan.mk ((effectiveMotive k).obj (Cor.mk (SmoothSite.finiteCoproduct Y)))
      (fun i => (effectiveMotive k).map ((Cor.graphFunctor k).map
        (SmoothSite.finiteCoproductι Y i)))) :=
  isColimitCofanMkObjOfIsColimit (effectiveMotive k) (fun i => Cor.mk (Y i))
    (fun i => (Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i))
    (Cor.finiteCoproductIsColimit k Y)

end AlgebraicGeometry.MotivicHomotopy
