/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Excision
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ClosedPair

/-! # Étale excision for closed supports -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

/-- An étale morphism that induces an isomorphism over the closed support
induces an isomorphism on the actual motives of the complementary open pairs. -/
theorem isIso_effectivePairMotiveMap_closedPairSquare {X Y : Sm(k)} {Z W : Scheme.{u}}
    {z : Z ⟶ X.left} {w : W ⟶ Y.left} [IsClosedImmersion z] [IsClosedImmersion w]
    {f : X ⟶ Y} {g : Z ⟶ W} (h : IsPullback z g f.left w) [Etale f.left] [IsIso g] :
    IsIso (effectivePairMotiveMap k (closedPairSquare h)) := by
  let sq := closedPairSquare h
  let : IsOpenImmersion sq.f₂₄.left :=
    inferInstanceAs (IsOpenImmersion (closedPairOpenInclusion w).left)
  let : Etale sq.f₃₄.left := inferInstanceAs (Etale f.left)
  let : IsIso (Limits.pullback.snd sq.f₃₄.left w) := isIso_closedPair_pullbackSnd h
  have hc : Set.range w = (Set.range sq.f₂₄.left)ᶜ := by
    change Set.range w = (Set.range (closedPairOpenInclusion w).left)ᶜ
    rw [range_closedPairOpenInclusion, compl_compl]
  exact @effectivePairMotiveMap_isIso k _ _ _ _ _ sq
    (closedPairSquare_isPullback h) ‹IsOpenImmersion sq.f₂₄.left› ‹Etale sq.f₃₄.left›
    W w ‹IsClosedImmersion w› hc ‹IsIso (Limits.pullback.snd sq.f₃₄.left w)›

end AlgebraicGeometry.MotivicHomotopy
