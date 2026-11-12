/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.FiniteIsomorphisms

/-!
# Descent of frames on an entire compatible boundary diagram

The boundary is a diagram of schemes with its original maps to the ambient diagram, not its
reduction. A frame given only on the limit is descended to an actual restriction of the ambient
stage module. The conclusion records the original limit frame and finitely many prescribed
equations, through the native pullback comparisons. Neither a stage frame nor a locality
hypothesis on a stage is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace Stacks.AlgebraicGeometry.ModuleLimits

attribute [local implicit_reducible] TopCat.Sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.unitModule

/-- The actual comparison of the two iterated pullbacks in a commutative scheme square. -/
def pullbackSquareIso {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ D)
    (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k) (M : D.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback k).obj M) :=
  canIso f g (h ≫ k) w M ≪≫ (canIso h k (h ≫ k) rfl M).symm

/-- Normalize a frame on the other side of a commutative square as an isomorphism
between pullbacks from the boundary stage. Both the square and the unit comparison are retained. -/
def framePullbackIso {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ D)
    (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k) (M : D.Modules)
    (e : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback k).obj M) ≅
      SheafOfModules.unit A.ringCatSheaf) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback f).obj (SheafOfModules.unit B.ringCatSheaf) :=
  pullbackSquareIso f g h k w M ≪≫ e ≪≫ (Scheme.Modules.pullbackUnitIso f).symm

private theorem frame_descent_aux {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {A U : C} {B V : D} {W T : E}
    (m : F.obj A ≅ F.obj U) (s : F.obj A ≅ B) (u : F.obj U ≅ V)
    (v : G.obj V ≅ T) (w : G.obj (F.obj U) ≅ W) (t : W ≅ T)
    (a : G.obj (F.obj A) ⟶ T)
    (hm : G.map m.hom ≫ w.hom = a ≫ t.inv)
    (hu : G.map u.hom ≫ v.hom = w.hom ≫ t.hom) :
    G.map (s.hom ≫ (s.symm ≪≫ m ≪≫ u).hom) ≫ v.hom = a := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, Functor.map_comp,
    Category.assoc]
  rw [hu, ← Category.assoc, hm]
  simp

/-- Descend an actual frame on the full limit boundary, together with finitely many original
equations. The stage frame is on the pullback along the original boundary component `b.app j`.
The ambient scheme need not be local, and the boundary need not be reduced. -/
@[colib_tag "COL-1101"]
theorem exists_boundary_frame_comp_eq_of_isLimit_finite
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Cone C) (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (M : (C.obj i).Modules) [M.IsFinitePresentation]
    (eLim : (Scheme.Modules.pullback bLim).obj
      ((Scheme.Modules.pullback (cC.π.app i)).obj M) ≅
        SheafOfModules.unit cB.pt.ringCatSheaf)
    {κ : Type w} [Finite κ] (P : κ → (B.obj i).Modules)
    [∀ x, (P x).IsFinitePresentation]
    (a : ∀ x, P x ⟶ (Scheme.Modules.pullback (b.app i)).obj M)
    (t : ∀ x, P x ⟶ SheafOfModules.unit (B.obj i).ringCatSheaf)
    (hat : ∀ x, (Scheme.Modules.pullback (cB.π.app i)).map (a x) ≫
        (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M).hom ≫
        eLim.hom = (Scheme.Modules.pullback (cB.π.app i)).map (t x) ≫
          (Scheme.Modules.pullbackUnitIso (cB.π.app i)).hom) :
    ∃ (j : I) (f : j ⟶ i)
      (e : (Scheme.Modules.pullback (b.app j)).obj
        ((Scheme.Modules.pullback (C.map f)).obj M) ≅
          SheafOfModules.unit (B.obj j).ringCatSheaf),
      ((Scheme.Modules.pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M).hom ≫ e.hom) ≫
          (Scheme.Modules.pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((Scheme.Modules.pullback (b.app i)).obj M) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M).hom ≫
          eLim.hom) ∧
      ∀ x, (Scheme.Modules.pullback (B.map f)).map (a x) ≫
          (pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M).hom ≫ e.hom =
        (Scheme.Modules.pullback (B.map f)).map (t x) ≫
          (Scheme.Modules.pullbackUnitIso (B.map f)).hom := by
  let A := (Scheme.Modules.pullback (b.app i)).obj M
  let U := SheafOfModules.unit (B.obj i).ringCatSheaf
  have : A.IsFinitePresentation := isFinitePresentation_pullback _ M
  have : U.IsFinitePresentation := isFinitePresentation_unit _
  let N := pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M ≪≫
    eLim ≪≫ (Scheme.Modules.pullbackUnitIso (cB.π.app i)).symm
  have hN (x : κ) : (Scheme.Modules.pullback (cB.π.app i)).map (a x) ≫ N.hom =
      (Scheme.Modules.pullback (cB.π.app i)).map (t x) := by
    change _ ≫ _ ≫ _ ≫ (Scheme.Modules.pullbackUnitIso (cB.π.app i)).inv = _
    rw [← Category.assoc _ eLim.hom, ← Category.assoc, hat x, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  obtain ⟨j, f, m, hm, hmt⟩ :=
    exists_iso_pullback_canonical_comp_eq_of_isLimit_finite B cB hcB i A U N P a t hN
  let S := pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f) (b.naturality f) M
  refine ⟨j, f, S.symm ≪≫ m ≪≫ Scheme.Modules.pullbackUnitIso (B.map f), ?_, ?_⟩
  · have hu : (Scheme.Modules.pullback (cB.π.app j)).map
        (Scheme.Modules.pullbackUnitIso (B.map f)).hom ≫
        (Scheme.Modules.pullbackUnitIso (cB.π.app j)).hom =
      (canIso (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) U).hom ≫
        (Scheme.Modules.pullbackUnitIso (cB.π.app i)).hom :=
      by
        apply (cancel_epi (canIso (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) U).inv).mp
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        simpa only [U, Scheme.unitModule, canIso, Iso.trans_inv, Iso.app, Category.assoc] using
          Scheme.Modules.pullbackUnitIso_comp_eq (cB.π.app j) (B.map f)
            (cB.π.app i) (cB.w f)
    exact frame_descent_aux (Scheme.Modules.pullback (B.map f))
      (Scheme.Modules.pullback (cB.π.app j)) m S
      (Scheme.Modules.pullbackUnitIso (B.map f))
      (Scheme.Modules.pullbackUnitIso (cB.π.app j))
      (canIso (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) U)
      (Scheme.Modules.pullbackUnitIso (cB.π.app i)) _ hm hu
  · intro x
    simp only [S, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hmt x]

end Stacks.AlgebraicGeometry.ModuleLimits
