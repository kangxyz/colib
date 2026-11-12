/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ProjectiveLine
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.Boundary
/-!
# Projective-line covers on actual Cartesian models

Transport a finite cover to the specified curve and keep the original chart nonempty on
its marked normal component, without identifying components in different ambient curves.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- A finite projective-line cover transported to a specified actual Cartesian
model, not to a newly substituted curve. Use X=the fixed clopen U and X'=Cnew. -/
def projectiveLineCoverOfActualCartesian
    {A R : Type u} [CommRing A] [CommRing R] {X X' : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) (f : A →+* R)
    (v : X' ⟶ X) (q : X' ⟶ Spec (.of R))
    (h : IsPullback v q p (Spec.map (CommRingCat.ofHom f)))
    (π : X ⟶ projectiveLine A)
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    X' ⟶ projectiveLine R :=
  h.isoPullback.hom ≫ projectiveLineCoverBaseChange p f π hπ

instance projectiveLineCoverOfActualCartesian_isFinite
    {A R : Type u} [CommRing A] [CommRing R] {X X' : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) (f : A →+* R)
    (v : X' ⟶ X) (q : X' ⟶ Spec (.of R))
    (h : IsPullback v q p (Spec.map (CommRingCat.ofHom f)))
    (π : X ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    IsFinite (projectiveLineCoverOfActualCartesian p f v q h π hπ) := by
  unfold projectiveLineCoverOfActualCartesian
  infer_instance

theorem projectiveLineCoverOfActualCartesian_structure
    {A R : Type u} [CommRing A] [CommRing R] {X X' : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) (f : A →+* R)
    (v : X' ⟶ X) (q : X' ⟶ Spec (.of R))
    (h : IsPullback v q p (Spec.map (CommRingCat.ofHom f)))
    (π : X ⟶ projectiveLine A)
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    projectiveLineCoverOfActualCartesian p f v q h π hπ ≫
      (projectiveLine R ↘ Spec (.of R)) = q := by
  rw [projectiveLineCoverOfActualCartesian, Category.assoc,
    projectiveLineCoverBaseChange_structure]
  exact h.isoPullback_hom_snd

/-- The original nonempty chart meets the SAME actual Cnew component. No equality
between normalComponentOpen objects on different ambient curves is needed. -/
theorem nonempty_actual_component_chart_of_flat_original
    {Cnew N E : Scheme.{u}} [IsLocallyNoetherian Cnew] [IsNormal Cnew]
    [IrreducibleSpace N] (T : Cnew ⟶ N) [Flat T]
    (e : E ⟶ N) [IsOpenImmersion e] [Nonempty E] (x : Cnew) :
    Nonempty (pullback (normalComponentOpen x).ι (pullback.fst T e) : Scheme.{u}) := by
  have hn := nonempty_pullback_normalComponent_chart_of_flat T e x
  exact hn.map (pullbackRightPullbackFstIso T e (normalComponentOpen x).ι).inv

end AlgebraicGeometry.Scheme
