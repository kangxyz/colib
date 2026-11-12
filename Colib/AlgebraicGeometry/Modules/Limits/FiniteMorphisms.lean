/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.FiniteEquations
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible

/-!
# Canonical simultaneous descent of finitely many module morphisms

A finite family of actual morphisms on the limit descends at one common transition. The source
and target modules may depend on the family index. In particular this descends finitely many
sections of modules defined at a stage, by presenting sections as maps from the structure sheaf.
The canonical comparison is retained separately for every morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u w

namespace Stacks.AlgebraicGeometry.ModuleLimits

attribute [local implicit_reducible] TopCat.Sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.unitModule

/-- Finitely many actual morphisms between pullbacks of finitely presented modules descend
simultaneously, with the original pullback identifications. -/
theorem exists_maps_pullback_canonical_of_isLimit_finite {I : Type u} [Category.{v} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) {κ : Type w} [Finite κ] (A B : κ → (D.obj i).Modules)
    [∀ x, (A x).IsFinitePresentation] [∀ x, (B x).IsFinitePresentation]
    (φ : ∀ x, (Scheme.Modules.pullback (c.π.app i)).obj (A x) ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj (B x)) :
    ∃ (j : I) (e : j ⟶ i)
      (φj : ∀ x, (Scheme.Modules.pullback (D.map e)).obj (A x) ⟶
        (Scheme.Modules.pullback (D.map e)).obj (B x)),
      ∀ x, (Scheme.Modules.pullback (c.π.app j)).map (φj x) ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) (B x) =
        canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) (A x) ≫ φ x := by
  classical
  let := Fintype.ofFinite κ
  choose j e m hm using fun x =>
    exists_map_of_pullback_canonical_of_isLimit' D c hc i (A x) (B x) (φ x)
  let k (x : κ) : Over i := Over.mk (e x)
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.image k Finset.univ)
  have t (x : κ) : l ⟶ k x :=
    (hl (Finset.mem_image_of_mem k (Finset.mem_univ x))).some
  have ht (x : κ) : D.map (t x).left ≫ D.map (e x) = D.map l.hom := by
    rw [← D.map_comp]
    exact congrArg D.map (Over.w (t x))
  refine ⟨l.left, l.hom,
    fun x => canStep (D.map (t x).left) (D.map (e x)) (D.map l.hom) (ht x) (m x),
    fun x => ?_⟩
  exact canonical_eq_of_further_step (c.π.app l.left) (D.map (t x).left)
    (c.π.app (j x)) (c.w (t x).left) (D.map (e x)) (c.π.app i) (c.w (e x))
    (D.map l.hom) (ht x) (c.w l.hom) (m x) (φ x) (hm x)

/-- The inverse structure-sheaf pullback comparison respects the canonical composition
comparison. This is the inverse of the native `pullbackUnitIso_comp_eq` equation. -/
theorem pullbackUnitIso_inv_comp_canHom {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X)
    (p : W ⟶ X) (hp : q ≫ g = p) :
    (Scheme.Modules.pullbackUnitIso q).inv ≫
        (Scheme.Modules.pullback q).map (Scheme.Modules.pullbackUnitIso g).inv ≫
        canHom q g p hp (SheafOfModules.unit X.ringCatSheaf) =
      (Scheme.Modules.pullbackUnitIso p).inv := by
  have h : (canIso q g p hp (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
      (Scheme.Modules.pullback q).mapIso (Scheme.Modules.pullbackUnitIso g) ≪≫
      Scheme.Modules.pullbackUnitIso q = Scheme.Modules.pullbackUnitIso p := by
    apply Iso.ext
    simpa only [Scheme.unitModule, canIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Functor.mapIso, Iso.app, Category.assoc]
      using Scheme.Modules.pullbackUnitIso_comp_eq q g p hp
  have hi := congrArg (fun e => e.inv) h
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso, canIso_hom, Category.assoc]
    using hi

private theorem map_comp_assoc {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {X Y Z : C} {W T : E} (a : W ⟶ F.obj X) (b : X ⟶ Y) (d : Y ⟶ Z)
    (e : F.obj Z ⟶ T) :
    (a ≫ F.map (b ≫ d)) ≫ e = (a ≫ F.map b) ≫ F.map d ≫ e := by
  rw [F.map_comp]
  simp only [Category.assoc]

private theorem triangle_comp {C : Type*} [Category C] {A B B' P Q : C}
    {ν : A ⟶ B} {m : B ⟶ B'} {g : B' ⟶ P} {f : B ⟶ Q} {φ : Q ⟶ P} {u : A ⟶ Q}
    (h : m ≫ g = f ≫ φ) (hu : ν ≫ f = u) : ν ≫ m ≫ g = u ≫ φ := by
  rw [h, ← Category.assoc, hu]

/-- Finitely many actual global sections of pullbacks descend to one stage. Their pullbacks
recover the original sections through the canonical comparisons; the equation is written using
the native equivalence between global sections and morphisms from the structure sheaf. -/
theorem exists_sections_pullback_canonical_of_isLimit_finite {I : Type u} [Category.{v} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) {κ : Type w} [Finite κ] (B : κ → (D.obj i).Modules)
    [∀ x, (B x).IsFinitePresentation]
    (s : ∀ x, ((Scheme.Modules.pullback (c.π.app i)).obj (B x)).sections) :
    ∃ (j : I) (e : j ⟶ i)
      (t : ∀ x, ((Scheme.Modules.pullback (D.map e)).obj (B x)).sections), ∀ x,
      (Scheme.Modules.pullbackUnitIso (c.π.app j)).inv ≫
          (Scheme.Modules.pullback (c.π.app j)).map ((SheafOfModules.unitHomEquiv _).symm (t x)) ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) (B x) =
        (SheafOfModules.unitHomEquiv _).symm (s x) := by
  have : (SheafOfModules.unit (D.obj i).ringCatSheaf).IsFinitePresentation :=
    isFinitePresentation_unit _
  obtain ⟨j, e, φ, hφ⟩ := exists_maps_pullback_canonical_of_isLimit_finite D c hc i
    (fun _ : κ => SheafOfModules.unit (D.obj i).ringCatSheaf) B
    (fun x => (Scheme.Modules.pullbackUnitIso (c.π.app i)).hom ≫
      (SheafOfModules.unitHomEquiv _).symm (s x))
  refine ⟨j, e, fun x => SheafOfModules.unitHomEquiv _
    ((Scheme.Modules.pullbackUnitIso (D.map e)).inv ≫ φ x), fun x => ?_⟩
  rw [Equiv.symm_apply_apply]
  have hunit : ((Scheme.Modules.pullbackUnitIso (c.π.app j)).inv ≫
      (Scheme.Modules.pullback (c.π.app j)).map
        (Scheme.Modules.pullbackUnitIso (D.map e)).inv) ≫
      canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e)
        (SheafOfModules.unit (D.obj i).ringCatSheaf) =
      (Scheme.Modules.pullbackUnitIso (c.π.app i)).inv :=
    (Category.assoc _ _ _).trans (pullbackUnitIso_inv_comp_canHom _ _ _ _)
  have key : ((Scheme.Modules.pullbackUnitIso (c.π.app j)).inv ≫
      (Scheme.Modules.pullback (c.π.app j)).map
        ((Scheme.Modules.pullbackUnitIso (D.map e)).inv ≫ φ x)) ≫
      canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) (B x) =
      (SheafOfModules.unitHomEquiv _).symm (s x) :=
    (map_comp_assoc (Scheme.Modules.pullback (c.π.app j)) _ _ _ _).trans
      ((triangle_comp (hφ x) hunit).trans (Iso.inv_hom_id_assoc _ _))
  exact (Category.assoc _ _ _).symm.trans key

end Stacks.AlgebraicGeometry.ModuleLimits
