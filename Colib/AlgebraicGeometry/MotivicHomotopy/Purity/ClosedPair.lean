/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.PunctureComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Open complements of smooth closed pairs

A cartesian square of closed supports gives a cartesian square of their
open complements, with the original map of ambient schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [IsNoetherian S]

/-- The open complement of the image of the indicated closed immersion. -/
def closedPairOpen {X : SmoothSite S} {Z : Scheme.{u}} (z : Z ⟶ X.left)
    [IsClosedImmersion z] : X.left.Opens :=
  ⟨(Set.range z)ᶜ, (Scheme.Hom.isClosedEmbedding z).isClosed_range.isOpen_compl⟩

/-- The original inclusion of the open complement into the ambient smooth scheme. -/
abbrev closedPairOpenInclusion {X : SmoothSite S} {Z : Scheme.{u}} (z : Z ⟶ X.left)
    [IsClosedImmersion z] :
    (opensFunctor X).obj (closedPairOpen z) ⟶ X :=
  openInclusion X (closedPairOpen z)

instance {X : SmoothSite S} {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsClosedImmersion z] :
    IsOpenImmersion (closedPairOpenInclusion z).left :=
  inferInstanceAs (IsOpenImmersion (closedPairOpen z).ι)

/-- The inclusion has the open range complementary to the original support. -/
theorem range_closedPairOpenInclusion {X : SmoothSite S} {Z : Scheme.{u}}
    (z : Z ⟶ X.left) [IsClosedImmersion z] :
    Set.range (closedPairOpenInclusion z).left = (Set.range z)ᶜ :=
  Scheme.Opens.range_ι (closedPairOpen z)

section Map

variable {X Y : SmoothSite S} {Z W : Scheme.{u}}
  {z : Z ⟶ X.left} {w : W ⟶ Y.left} [IsClosedImmersion z] [IsClosedImmersion w]
  {f : X ⟶ Y} {g : Z ⟶ W} (h : IsPullback z g f.left w)

include h in
/-- The complement in the source is the inverse image of the complement in the target. -/
theorem range_closedPairOpenInclusion_preimage :
    Set.range (closedPairOpenInclusion z).left =
      f.left ⁻¹' Set.range (closedPairOpenInclusion w).left := by
  rw [range_closedPairOpenInclusion, range_closedPairOpenInclusion,
    Set.preimage_compl, range_fst_of_cartesian h]

include h in
private theorem closedPairOpen_map_range :
    Set.range ((closedPairOpenInclusion z).left ≫ f.left) ⊆
      Set.range (closedPairOpenInclusion w).left := by
  rintro _ ⟨x, rfl⟩
  have hx : (closedPairOpenInclusion z).left x ∈
      Set.range (closedPairOpenInclusion z).left := Set.mem_range_self x
  rw [range_closedPairOpenInclusion_preimage h] at hx
  exact hx

/-- The restriction of the original ambient morphism to the open complements. -/
@[no_expose] def closedPairOpenMap (h' : IsPullback z g f.left w) :
    (opensFunctor X).obj (closedPairOpen z) ⟶ (opensFunctor Y).obj (closedPairOpen w) :=
  let i := closedPairOpenInclusion z
  let j := closedPairOpenInclusion w
  let a := IsOpenImmersion.lift j.left (i.left ≫ f.left) (closedPairOpen_map_range h')
  homMk a (by
    rw [← MorphismProperty.Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac,
      Category.assoc, MorphismProperty.Over.w f, MorphismProperty.Over.w i])

/-- Restriction commutes with the two open immersions. -/
theorem closedPairOpenMap_comm :
    closedPairOpenMap h ≫ closedPairOpenInclusion w = closedPairOpenInclusion z ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- The square of original ambient schemes and their complementary opens. -/
def closedPairSquare (h' : IsPullback z g f.left w) : Square (SmoothSite S) where
  f₁₂ := closedPairOpenMap h'
  f₁₃ := closedPairOpenInclusion z
  f₂₄ := closedPairOpenInclusion w
  f₃₄ := f
  fac := closedPairOpenMap_comm h'

/-- A cartesian square of closed supports induces a cartesian square of open complements. -/
theorem closedPairSquare_isPullback : (closedPairSquare h).IsPullback := by
  apply IsPullback.of_map_of_faithful (forgetScheme S)
  apply IsOpenImmersion.isPullback (closedPairOpenMap h).left
    (closedPairOpenInclusion z).left (closedPairOpenInclusion w).left f.left
  · exact congrArg (fun a => a.left) (closedPairOpenMap_comm h).symm
  · apply SetLike.coe_injective
    rw [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange]
    exact (range_closedPairOpenInclusion_preimage h).symm

end Map

omit [IsNoetherian S] in
/-- The support square of an isomorphism over the closed part supplies the
original pullback projection used in Nisnevich excision. -/
theorem isIso_closedPair_pullbackSnd {X Y : SmoothSite S} {Z W : Scheme.{u}}
    {z : Z ⟶ X.left} {w : W ⟶ Y.left} {f : X ⟶ Y} {g : Z ⟶ W}
    (h : IsPullback z g f.left w) [IsIso g] :
    IsIso (pullback.snd f.left w) := by
  have : IsIso (h.isoPullback.hom ≫ pullback.snd f.left w) := by
    rw [h.isoPullback_hom_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left h.isoPullback.hom _

end AlgebraicGeometry.Scheme.SmoothSite
