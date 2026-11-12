/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.Modules.Limits.FiniteMorphisms
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional

/-!
# Canonical isomorphism descent with finitely many prescribed equations

The canonical isomorphism descent argument is kept at the module-limit layer, without importing
the polarized-family application. The proof adapts the pinned Stacks argument in
`AlgebraicGeometry/Quot/PolarizedLimitDescentHom.lean:248-289` and its one-equation refinement in
`AlgebraicGeometry/Limits/EventualModuleIsoSection.lean:132-182`. A common refinement in the over
category makes every prescribed equation hold for the same isomorphism and transition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u w

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- A specified isomorphism on the limit descends with its canonical pullback equation.
This uses only the native module-descent suppliers, not polarized-family descent. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/Quot/PolarizedLimitDescentHom.lean:248-289"
  "adaptation" "Canonical isomorphism descent at the lower module-limit interface"]
theorem exists_iso_pullback_canonical_of_isLimit (hc : IsLimit c) (i : I)
    (A B : (D.obj i).Modules) [A.IsFinitePresentation] [B.IsFinitePresentation]
    (N : (Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B) :
    ∃ (j : I) (e : j ⟶ i)
      (m : (Scheme.Modules.pullback (D.map e)).obj A ≅
        (Scheme.Modules.pullback (D.map e)).obj B),
      (Scheme.Modules.pullback (c.π.app j)).map m.hom ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) B =
        canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) A ≫ N.hom := by
  obtain ⟨j₁, e₁, m₁, h₁⟩ :=
    exists_map_of_pullback_canonical_of_isLimit' D c hc i A B N.hom
  have hA₁ : ((Scheme.Modules.pullback (D.map e₁)).obj A).IsFinitePresentation :=
    isFinitePresentation_pullback _ A
  have hB₁ : ((Scheme.Modules.pullback (D.map e₁)).obj B).IsFinitePresentation :=
    isFinitePresentation_pullback _ B
  have hiso : IsIso ((Scheme.Modules.pullback (c.π.app j₁)).map m₁) := by
    have he : (Scheme.Modules.pullback (c.π.app j₁)).map m₁ =
        canHom (c.π.app j₁) (D.map e₁) (c.π.app i) (c.w e₁) A ≫ N.hom ≫
          inv (canHom (c.π.app j₁) (D.map e₁) (c.π.app i) (c.w e₁) B) := by
      rw [← Category.assoc, ← h₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [he]
    infer_instance
  obtain ⟨j₂, e₂, h₂⟩ := exists_isIso_pullback_of_isLimit D c hc j₁ _ _ hA₁ hB₁ m₁ hiso
  let := h₂
  refine ⟨j₂, e₂ ≫ e₁,
    (canIso (D.map e₂) (D.map e₁) (D.map (e₂ ≫ e₁)) (D.map_comp e₂ e₁).symm A).symm ≪≫
      asIso ((Scheme.Modules.pullback (D.map e₂)).map m₁) ≪≫
        canIso (D.map e₂) (D.map e₁) (D.map (e₂ ≫ e₁)) (D.map_comp e₂ e₁).symm B, ?_⟩
  exact canonical_eq_of_further_step (c.π.app j₂) (D.map e₂) (c.π.app j₁) (c.w e₂)
    (D.map e₁) (c.π.app i) (c.w e₁) (D.map (e₂ ≫ e₁)) (D.map_comp e₂ e₁).symm
    (c.w (e₂ ≫ e₁)) m₁ N.hom h₁

/-- A specified limit isomorphism descends together with any finite family of prescribed
morphism equations. Taking the source modules to be structure sheaves gives prescribed sections.
No reducedness hypothesis is used, so the diagram may consist of whole nonreduced boundaries. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/Limits/EventualModuleIsoSection.lean:132-182"
  "generalization"
    "Simultaneous finite prescribed morphism equations with the original limit isomorphism"]
theorem exists_iso_pullback_canonical_comp_eq_of_isLimit_finite (hc : IsLimit c) (i : I)
    (A B : (D.obj i).Modules) [A.IsFinitePresentation] [B.IsFinitePresentation]
    (N : (Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B)
    {κ : Type w} [Finite κ] (P : κ → (D.obj i).Modules)
    [∀ a, (P a).IsFinitePresentation] (a : ∀ x, P x ⟶ A) (b : ∀ x, P x ⟶ B)
    (hab : ∀ x, (Scheme.Modules.pullback (c.π.app i)).map (a x) ≫ N.hom =
      (Scheme.Modules.pullback (c.π.app i)).map (b x)) :
    ∃ (j : I) (e : j ⟶ i)
      (m : (Scheme.Modules.pullback (D.map e)).obj A ≅
        (Scheme.Modules.pullback (D.map e)).obj B),
      ((Scheme.Modules.pullback (c.π.app j)).map m.hom ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) B =
        canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) A ≫ N.hom) ∧
      ∀ x, (Scheme.Modules.pullback (D.map e)).map (a x) ≫ m.hom =
        (Scheme.Modules.pullback (D.map e)).map (b x) := by
  obtain ⟨j₁, e₁, m₁, h₁⟩ := exists_iso_pullback_canonical_of_isLimit D c hc i A B N
  have hkey (x : κ) : (Scheme.Modules.pullback (c.π.app j₁)).map
        ((Scheme.Modules.pullback (D.map e₁)).map (a x) ≫ m₁.hom) =
      (Scheme.Modules.pullback (c.π.app j₁)).map
        ((Scheme.Modules.pullback (D.map e₁)).map (b x)) := by
    refine (cancel_mono (canHom (c.π.app j₁) (D.map e₁) (c.π.app i) (c.w e₁) B)).mp ?_
    rw [Functor.map_comp, Category.assoc, h₁, ← Category.assoc,
      canHom_naturality _ _ _ _ (a x), Category.assoc, hab x,
      canHom_naturality _ _ _ _ (b x)]
  have : ∀ x, ((Scheme.Modules.pullback (D.map e₁)).obj (P x)).IsFinitePresentation :=
    fun x => isFinitePresentation_pullback _ (P x)
  have : ((Scheme.Modules.pullback (D.map e₁)).obj B).IsFinitePresentation :=
    isFinitePresentation_pullback _ B
  obtain ⟨j₂, e₂, h₂⟩ := exists_pullback_map_eq_of_isLimit_finite D c hc j₁
    (fun x => (Scheme.Modules.pullback (D.map e₁)).obj (P x))
    (fun _ : κ => (Scheme.Modules.pullback (D.map e₁)).obj B)
    (fun x => (Scheme.Modules.pullback (D.map e₁)).map (a x) ≫ m₁.hom)
    (fun x => (Scheme.Modules.pullback (D.map e₁)).map (b x)) hkey
  refine ⟨j₂, e₂ ≫ e₁,
    (canIso (D.map e₂) (D.map e₁) (D.map (e₂ ≫ e₁)) (D.map_comp e₂ e₁).symm A).symm ≪≫
      asIso ((Scheme.Modules.pullback (D.map e₂)).map m₁.hom) ≪≫
        canIso (D.map e₂) (D.map e₁) (D.map (e₂ ≫ e₁)) (D.map_comp e₂ e₁).symm B, ?_, ?_⟩
  · exact canonical_eq_of_further_step (c.π.app j₂) (D.map e₂) (c.π.app j₁) (c.w e₂)
      (D.map e₁) (c.π.app i) (c.w e₁) (D.map (e₂ ≫ e₁)) (D.map_comp e₂ e₁).symm
      (c.w (e₂ ≫ e₁)) m₁.hom N.hom h₁
  · intro x
    refine (cancel_epi (canHom (D.map e₂) (D.map e₁) (D.map (e₂ ≫ e₁))
      (D.map_comp e₂ e₁).symm (P x))).mp ?_
    change _ ≫ _ ≫ canStep _ _ _ _ m₁.hom = _
    rw [← Category.assoc, ← canHom_naturality _ _ _ _ (a x),
      ← canHom_naturality _ _ _ _ (b x), canStep]
    simp only [Category.assoc, ← canIso_hom]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← Functor.map_comp, h₂ x, canIso_hom]

end Stacks.AlgebraicGeometry.ModuleLimits
