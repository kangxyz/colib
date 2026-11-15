/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.ReflectionNaturality
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Transfer

/-!
# Effective motives of open pairs

Applying effective reflection to the original transfer quotient sheaf in
degree zero gives the relative motive, functorial in the actual pairs.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "NST(" field ")" => LargeSheaves field

variable [HasDerivedCategory.{w'} NST(k)]

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The effective reflection of a transfer sheaf placed in degree zero. -/
abbrev effectiveTransferSheaf : NST(k) ⥤ EffectiveMotivesMinus k :=
  singleTransferSheafMinus k ⋙ effectiveReflection k

/-- The effective reflection is additive, by transposing through its actual adjunction. -/
private theorem reflection_additive_of_inclusion {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    [R.Additive] : L.Additive where
  map_add {X Y f g} := by
    apply (a.homEquiv X (L.obj Y)).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R.map_add,
      Preadditive.comp_add, a.unit_naturality f, a.unit_naturality g,
      a.unit_naturality (f + g), Preadditive.add_comp]

/-- The original effective reflection preserves sums of maps. -/
instance effectiveReflection_additive : (effectiveReflection k).Additive := by
  let : (effectiveMotivesMinusInclusion k).Additive :=
    inferInstanceAs (Functor.Additive ((effectiveCohomologyCondition k).ι))
  exact reflection_additive_of_inclusion (effectiveReflectionAdjunction k)

/-- Effective reflection of transfer sheaves in degree zero preserves sums of maps. -/
instance effectiveTransferSheaf_additive : (effectiveTransferSheaf k).Additive :=
  inferInstanceAs ((singleTransferSheafMinus k ⋙ effectiveReflection k).Additive)

/-- The relative effective motive, functorial in maps of the original pairs. -/
def effectivePairMotiveFunctor : Arrow Sm(k) ⥤ EffectiveMotivesMinus k :=
  transferPairCokernelFunctor k ⋙ effectiveTransferSheaf k

/-- The relative effective motive of the indicated open pair. -/
def effectivePairMotive {U X : Sm(k)} (j : U ⟶ X) : EffectiveMotivesMinus k :=
  (effectiveTransferSheaf k).obj (transferPairCokernel k j)

/-- The actual relative motive map induced by a commuting square of smooth schemes. -/
def effectivePairMotiveMap (sq : Square Sm(k)) :
    effectivePairMotive k sq.f₁₃ ⟶ effectivePairMotive k sq.f₂₄ :=
  (effectiveTransferSheaf k).map (transferPairCokernelMap k sq)

end AlgebraicGeometry.MotivicHomotopy
