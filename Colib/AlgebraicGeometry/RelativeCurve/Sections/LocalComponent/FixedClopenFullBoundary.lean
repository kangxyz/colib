/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.FixedClopenRetainedTarget

/-! # The original full finite boundary on the same literal clopen model -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme
variable {C C' A A' U Y Z : Scheme.{u}}
  (F : C' ⟶ C) (q' : C' ⟶ A') (q : C ⟶ A) (v : A' ⟶ A)
  (hp : IsPullback F q' q v)
  (k : U ⟶ C') [IsClosedImmersion k]
  (j : Y ⟶ C) (d : Z ⟶ C) [IsFinite (d ≫ q)]

include hp in
/-- Finiteness is transported for the full original boundary scheme, not only its support. -/
theorem fixedClopen_fullBoundary_finite :
    IsFinite (pullback.fst k (pullback.fst F d) ≫ k ≫ q') := by
  have hpb : IsPullback (pullback.snd F d) (pullback.fst F d ≫ q') (d ≫ q) v :=
    (IsPullback.of_hasPullback F d).flip.paste_vert hp
  let hfin : IsFinite (pullback.fst F d ≫ q') :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have h : IsFinite (pullback.snd k (pullback.fst F d) ≫
      (pullback.fst F d ≫ q')) := inferInstance
  simpa only [← Category.assoc, ← pullback.condition] using h

omit [IsClosedImmersion k] in
/-- The retained open and full boundary use the same two literal pullbacks. -/
theorem fixedClopen_fullBoundary_complement
    (hd : Set.range d = (Set.range j)ᶜ) :
    Set.range (pullback.fst k (pullback.fst F d)) =
      (Set.range (pullback.fst k (pullback.fst F j)))ᶜ := by
  rw [Pullback.range_fst, Pullback.range_fst, Pullback.range_fst,
    Pullback.range_fst, hd]
  rfl

end AlgebraicGeometry.Scheme
