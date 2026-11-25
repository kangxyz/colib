/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Path.AssociatorEvaluation
public import Colib.Topology.Prespectrum.ConeCompositionPieces
public import Colib.Topology.Prespectrum.HomotopySquareBoundary
public import Colib.Topology.Prespectrum.HomotopySquarePathPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyOperationEvaluation

/-!
# Original square operations at mapped support points

A supplied equality at two specified source points, after an actual target map, survives
original path pasting, relative concatenation, boundary collapse and square lifting. Both
source and target may differ. Every time coordinate and actual collapse is retained.

Adapted from `Quillen/Topology/Prespectrum/HomotopySquareMappedSupport.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
namespace Homotopy.Square

/-- Both path pieces retain their actual halves at the two specified mapped support points. -/
theorem pastePaths_mapped_points {E F E' F' : LoopPrespectrum.{u}}
    {a b c d e f : E ⟶ F} {a' b' c' d' e' f' : E' ⟶ F'}
    {H : Homotopy a b} {K : Homotopy b c} {L : Homotopy d e} {M : Homotopy e f}
    {A : Homotopy a d} {B : Homotopy b e} {C : Homotopy c f}
    {H' : Homotopy a' b'} {K' : Homotopy b' c'}
    {L' : Homotopy d' e'} {M' : Homotopy e' f'}
    {A' : Homotopy a' d'} {B' : Homotopy b' e'} {C' : Homotopy c' f'}
    (S : H.Square L A B) (T : K.Square M B C)
    (S' : H'.Square L' A' B') (T' : K'.Square M' B' C')
    (j : F ⟶ F') (n : ℕ) (x : E.space n) (y : E'.space n)
    (hS : ∀ r s, j.map n (S.level n (r, (s, x))) = S'.level n (r, (s, y)))
    (hT : ∀ r s, j.map n (T.level n (r, (s, x))) = T'.level n (r, (s, y)))
    (r s : unitInterval) :
    j.map n ((S.pastePaths T).level n (r, (s, x))) =
      (S'.pastePaths T').level n (r, (s, y)) := by
  unfold pastePaths
  dsimp only [ContinuousMap.coe_mk]
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact hS r _
  · exact hT r _

/-- Boundary collapse preserves the same two source points and the actual target map. -/
theorem toBoundary_mapped_points {E F E' F' : LoopPrespectrum.{u}}
    {a b c d : E ⟶ F} {a' b' c' d' : E' ⟶ F'}
    {H : Homotopy a b} {K : Homotopy c d} {L : Homotopy a c} {M : Homotopy b d}
    {H' : Homotopy a' b'} {K' : Homotopy c' d'}
    {L' : Homotopy a' c'} {M' : Homotopy b' d'}
    (S : H.Square K L M) (S' : H'.Square K' L' M')
    (j : F ⟶ F') (n : ℕ) (x : E.space n) (y : E'.space n)
    (hS : ∀ r s, j.map n (S.level n (r, (s, x))) = S'.level n (r, (s, y)))
    (r s : unitInterval) :
    j.map n (S.toBoundary.level n (r, (s, x))) =
      S'.toBoundary.level n (r, (s, y)) := by
  rw [toBoundary_apply, toBoundary_apply]
  exact hS (Topology.ThreeSideSquare.collapse (r, s)).1
    (Topology.ThreeSideSquare.collapse (r, s)).2

end Homotopy.Square
namespace Homotopy.RelHomotopy

/-- Relative concatenation retains its full comparison-time subdivision at mapped points. -/
theorem trans_mapped_points {E F E' F' : LoopPrespectrum.{u}}
    {a b : E ⟶ F} {a' b' : E' ⟶ F'}
    {H K L : Homotopy a b} {H' K' L' : Homotopy a' b'}
    (J : H.RelHomotopy K) (N : K.RelHomotopy L)
    (J' : H'.RelHomotopy K') (N' : K'.RelHomotopy L')
    (j : F ⟶ F') (n : ℕ) (x : E.space n) (y : E'.space n)
    (hJ : ∀ r s, j.map n (J.level n (r, (s, x))) = J'.level n (r, (s, y)))
    (hN : ∀ r s, j.map n (N.level n (r, (s, x))) = N'.level n (r, (s, y)))
    (r s : unitInterval) :
    j.map n ((J.trans N).level n (r, (s, x))) =
      (J'.trans N').level n (r, (s, y)) := by
  change j.map n (((J.level n).trans (N.level n)) (r, (s, x))) =
    ((J'.level n).trans (N'.level n)) (r, (s, y))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hJ _ s
  · exact hN _ s

/-- Horizontal relative pasting preserves its actual path-time halves at mapped points. -/
theorem hcomp_mapped_points {E F E' F' : LoopPrespectrum.{u}}
    {a b c : E ⟶ F} {a' b' c' : E' ⟶ F'}
    {H K : Homotopy a b} {L M : Homotopy b c}
    {H' K' : Homotopy a' b'} {L' M' : Homotopy b' c'}
    (J : H.RelHomotopy K) (N : L.RelHomotopy M)
    (J' : H'.RelHomotopy K') (N' : L'.RelHomotopy M')
    (j : F ⟶ F') (n : ℕ) (x : E.space n) (y : E'.space n)
    (hJ : ∀ r s, j.map n (J.level n (r, (s, x))) = J'.level n (r, (s, y)))
    (hN : ∀ r s, j.map n (N.level n (r, (s, x))) = N'.level n (r, (s, y)))
    (r s : unitInterval) :
    j.map n ((J.hcomp N).level n (r, (s, x))) =
      (J'.hcomp N').level n (r, (s, y)) := by
  rw [hcomp_apply_path, hcomp_apply_path,
    Path.Homotopy.hcomp_apply, Path.Homotopy.hcomp_apply]
  split
  · exact hJ r _
  · exact hN r _

/-- The actual square lift preserves mapped support using its fixed collapse, without a new lift. -/
theorem toSquare_mapped_points {E F E' F' : LoopPrespectrum.{u}}
    {a b c d : E ⟶ F} {a' b' c' d' : E' ⟶ F'}
    {H : Homotopy a b} {K : Homotopy c d} {L : Homotopy a c} {M : Homotopy b d}
    {H' : Homotopy a' b'} {K' : Homotopy c' d'}
    {L' : Homotopy a' c'} {M' : Homotopy b' d'}
    (J : H.RelHomotopy ((L.trans K).trans M.symm))
    (J' : H'.RelHomotopy ((L'.trans K').trans M'.symm))
    (j : F ⟶ F') (n : ℕ) (x : E.space n) (y : E'.space n)
    (hJ : ∀ r s, j.map n (J.level n (r, (s, x))) = J'.level n (r, (s, y)))
    (r s : unitInterval) :
    j.map n (J.toSquare.level n (r, (s, x))) =
      J'.toSquare.level n (r, (s, y)) := by
  obtain ⟨z, hz⟩ := Topology.ThreeSideSquare.collapse_surjective (r, s)
  have hr := congrArg Prod.fst hz
  have hs := congrArg Prod.snd hz
  change (Topology.ThreeSideSquare.collapse z).1 = r at hr
  change (Topology.ThreeSideSquare.collapse z).2 = s at hs
  rw [← hr, ← hs, toSquare_collapse, toSquare_collapse]
  exact hJ z.1 z.2

/-- The actual original dyadic associator preserves image identities at different source points. -/
theorem transAssoc_mapped_points {E F E' F' : LoopPrespectrum.{u}}
    {a b c d : E ⟶ F} {a' b' c' d' : E' ⟶ F'}
    (H : Homotopy a b) (K : Homotopy b c) (L : Homotopy c d)
    (H' : Homotopy a' b') (K' : Homotopy b' c') (L' : Homotopy c' d')
    (j : F ⟶ F') (n : ℕ) (x : E.space n) (y : E'.space n)
    (hH : ∀ s, j.map n (H.level n (s, x)) = H'.level n (s, y))
    (hK : ∀ s, j.map n (K.level n (s, x)) = K'.level n (s, y))
    (hL : ∀ s, j.map n (L.level n (s, x)) = L'.level n (s, y))
    (r s : unitInterval) :
    j.map n ((transAssoc H K L).level n (r, (s, x))) =
      (transAssoc H' K' L').level n (r, (s, y)) := by
  rw [transAssoc_apply_path, transAssoc_apply_path]
  exact Path.Evaluation.transAssoc (j.map n) (H.path n x) (K.path n x) (L.path n x)
    (H'.path n y) (K'.path n y) (L'.path n y) hH hK hL r s

end Homotopy.RelHomotopy

/-- The original three-piece cone-null associator retains mapped support whenever each of
its three actual pieces does. The hypotheses compare concrete values, not a replacement filler. -/
theorem coneSquareCompositionNullComparison_mapped_points
    {E F E' F' E'' F'' D G D' G' D'' G'' : LoopPrespectrum.{u}}
    (f₀ : E ⟶ F) (g₀ : E' ⟶ F') (h₀ : E'' ⟶ F'')
    (a₀ : E ⟶ E') (b₀ : F ⟶ F') (c₀ : E' ⟶ E'') (d₀ : F' ⟶ F'')
    (H₀ : Homotopy (f₀ ≫ b₀) (a₀ ≫ g₀)) (K₀ : Homotopy (g₀ ≫ d₀) (c₀ ≫ h₀))
    (f₁ : D ⟶ G) (g₁ : D' ⟶ G') (h₁ : D'' ⟶ G'')
    (a₁ : D ⟶ D') (b₁ : G ⟶ G') (c₁ : D' ⟶ D'') (d₁ : G' ⟶ G'')
    (H₁ : Homotopy (f₁ ≫ b₁) (a₁ ≫ g₁)) (K₁ : Homotopy (g₁ ≫ d₁) (c₁ ≫ h₁))
    (j : mappingCone h₀ ⟶ mappingCone h₁) (n : ℕ) (x : E.space n) (y : D.space n)
    (hA : ∀ s, j.map n ((mappingConeInclusion h₀).map n (d₀.map n (H₀.level n (s, x)))) =
      (mappingConeInclusion h₁).map n (d₁.map n (H₁.level n (s, y))))
    (hB : ∀ s, j.map n ((mappingConeInclusion h₀).map n (K₀.level n (s, a₀.map n x))) =
      (mappingConeInclusion h₁).map n (K₁.level n (s, a₁.map n y)))
    (hC : ∀ s, j.map n ((mappingConeHomotopy h₀).level n (s, c₀.map n (a₀.map n x))) =
      (mappingConeHomotopy h₁).level n (s, c₁.map n (a₁.map n y)))
    (r s : unitInterval) :
    j.map n ((coneSquareCompositionNullComparison f₀ g₀ h₀ a₀ b₀ c₀ d₀ H₀ K₀).level n
      (r, (s, x))) =
    (coneSquareCompositionNullComparison f₁ g₁ h₁ a₁ b₁ c₁ d₁ H₁ K₁).level n (r, (s, y)) := by
  rw [ConeCompositionPieces.correction_apply, ConeCompositionPieces.correction_apply]
  exact Path.Evaluation.transAssoc (j.map n)
    ((ConeCompositionPieces.first h₀ a₀ d₀ H₀).path n x)
    ((ConeCompositionPieces.second h₀ a₀ c₀ d₀ K₀).path n x)
    ((ConeCompositionPieces.third h₀ a₀ c₀).path n x)
    ((ConeCompositionPieces.first h₁ a₁ d₁ H₁).path n y)
    ((ConeCompositionPieces.second h₁ a₁ c₁ d₁ K₁).path n y)
    ((ConeCompositionPieces.third h₁ a₁ c₁).path n y)
    hA hB hC r s

end Topology.LoopPrespectrum
