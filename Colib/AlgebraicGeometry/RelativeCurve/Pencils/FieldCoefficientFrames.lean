/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FiniteBoundaryFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedCoordinateUnit

/-!
# Coefficient frames on the entire original sources over a field

An invertible module on a scheme finite over a field is globally trivial: the
Tag 0BUT neighbourhood of the unique base point is the entire base. Pulling
these field-boundary frames to each product supplies coefficient frames on the
whole original lambda and psi boundaries, before a Serre exponent is chosen.
In particular the independent correction source is not shrunk.

The first lemma uses the narrow native proof also appearing privately in pinned
StacksFrontier/AlgebraicGeometry/Curves/LinearSeries.lean, lines 525-558. The
application replaces the projective twist-base-change route in the original
RelativeCurve/Sections/Normalized/FixedOpen/SectionPair.lean.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

/-- A finite scheme over a field has no nontrivial invertible modules. The
entire scheme, including its nilpotents, is retained. -/
theorem nonempty_frame_of_finite_over_field {k : Type u} [Field k] {Z : Scheme.{u}}
    (b : Z ⟶ Spec (.of k)) [IsFinite b] (M : Z.Modules) [IsInvertibleModule Z M] :
    Nonempty (M ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  letI : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).2 inferInstance
  obtain ⟨U, hx, ⟨e⟩⟩ := Stacks.Divisors.hasTrivializingTargetCover_of_isFinite
    b M (default : Spec (.of k))
  have hU : U = ⊤ := by
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    simpa only [Subsingleton.elim x (default : Spec (.of k))] using hx
  have hpre : b ⁻¹ᵁ U = ⊤ := by rw [hU]; ext x; simp
  rw [hpre] at e
  let g := (Scheme.topIso Z).symm
  let eM := (Modules.pullback g.hom).mapIso
      ((Modules.restrictFunctorIsoPullback (Scheme.topIso Z).hom).app M) ≪≫
    (Modules.pullbackComp g.hom (Scheme.topIso Z).hom).app M ≪≫
    (Modules.pullbackCongr (Scheme.topIso Z).inv_hom_id).app M ≪≫
    (Modules.pullbackId Z).app M
  let eO := ((Modules.restrictFunctorIsoPullback g.hom).app
      (SheafOfModules.unit (⊤ : Z.Opens).toScheme.ringCatSheaf)).symm ≪≫
    Modules.restrictUnitIso g.hom
  exact ⟨eM.symm ≪≫ (Modules.pullback g.hom).mapIso e ≪≫ eO⟩

variable {k : Type u} [Field k] {C Y D Z X A : Scheme.{u}}
  (π : C ⟶ Spec (.of k)) (j : Y ⟶ C) (s : Z ⟶ Y) (d : D ⟶ C)
  [IsFinite (d ≫ π)] [IsFinite (s ≫ j ≫ π)]
  (L : C.Modules) [IsInvertibleModule C L]

/-- A coefficient frame on the original whole lambda boundary. It comes from
the finite field boundary, not from an additional local frame hypothesis. -/
theorem nonempty_lambdaCoefficientBoundaryFrame :
    Nonempty ((Modules.pullback (fullGraphBoundaryMap π j s d)).obj
      ((Modules.pullback (pullback.snd (j ≫ π) π)).obj L) ≅
        SheafOfModules.unit
          ((pullback (pullback.snd (j ≫ π) π) d) ⨿
            pullback (j ≫ π) (s ≫ j ≫ π)).ringCatSheaf) := by
  obtain ⟨eD⟩ := nonempty_frame_of_finite_over_field (d ≫ π) ((Modules.pullback d).obj L)
  haveI : IsFinite ((s ≫ j) ≫ π) := by simpa only [Category.assoc] using inferInstanceAs
    (IsFinite (s ≫ j ≫ π))
  obtain ⟨eZ⟩ := nonempty_frame_of_finite_over_field ((s ≫ j) ≫ π)
    ((Modules.pullback (s ≫ j)).obj L)
  let eI := sourceChangedBoundaryFrame (pullback.snd (j ≫ π) π) d
    (infinityProductMap π j d) (pullback.snd _ _) (pullback.condition) L eD
  let eS := sourceChangedBoundaryFrame (pullback.snd (j ≫ π) π) (s ≫ j)
    (markedProductMap π j s) (pullback.snd _ _) (by simp [markedProductMap]) L eZ
  obtain ⟨E, -, -⟩ := exists_boundaryCoprod_frame (infinityProductMap π j d)
    (markedProductMap π j s) ((Modules.pullback (pullback.snd (j ≫ π) π)).obj L) eI eS
  exact ⟨E⟩

variable (q : X ⟶ Spec (.of k)) (p : Y ⟶ X) (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) (z : Z ⟶ X) (hs : s ≫ p = z)

/-- The independent whole psi boundary has its own coefficient frame, on the
unchanged correction source A. No open subset of A is substituted. -/
theorem nonempty_psiCoefficientBoundaryFrame :
    Nonempty ((Modules.pullback (psiBoundaryInclusion q π j p hq a z s hs d)).obj
      ((Modules.pullback (pullback.snd (a ≫ q) π)).obj L) ≅
        SheafOfModules.unit
          ((pullback (pullback.snd (a ≫ q) π) d) ⨿ pullback (a ≫ q) (z ≫ q)).ringCatSheaf) := by
  obtain ⟨eD⟩ := nonempty_frame_of_finite_over_field (d ≫ π) ((Modules.pullback d).obj L)
  haveI : IsFinite ((s ≫ j) ≫ π) := by simpa only [Category.assoc] using inferInstanceAs
    (IsFinite (s ≫ j ≫ π))
  obtain ⟨eZ⟩ := nonempty_frame_of_finite_over_field ((s ≫ j) ≫ π)
    ((Modules.pullback (s ≫ j)).obj L)
  let eI := sourceChangedBoundaryFrame (pullback.snd (a ≫ q) π) d
    (pullback.fst (pullback.snd (a ≫ q) π) d) (pullback.snd _ _) pullback.condition L eD
  let eS := sourceChangedBoundaryFrame (pullback.snd (a ≫ q) π) (s ≫ j)
    (psiZeroInclusion q π j p hq a z s hs) (pullback.snd _ _)
    (by simp [psiZeroInclusion]) L eZ
  obtain ⟨E, -, -⟩ := exists_boundaryCoprod_frame (pullback.fst (pullback.snd (a ≫ q) π) d)
    (psiZeroInclusion q π j p hq a z s hs)
    ((Modules.pullback (pullback.snd (a ≫ q) π)).obj L) eI eS
  exact ⟨E⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
