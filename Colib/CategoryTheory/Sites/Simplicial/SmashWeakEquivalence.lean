/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.PointedSmashFunctor
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseWeakEquivalence
import Colib.CategoryTheory.Limits.PointedSmashWedge
import Colib.CategoryTheory.Sites.Simplicial.ReducedConeContraction
import Colib.Topology.Realization.ProductWeakEquivalence

/-!
# Stalkwise weak equivalences of actual smash products

A site fiber preserves the wedge and smash pushouts and compares the
product with the product of the original fibers. The basepoint inclusions
and the wedge of the axes are monomorphisms. Applying realization gluing to
the two pushouts proves weak equivalence of the original smash map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : J.Point.{w})

private theorem mono_presheafFiber_map_point (X : PointedSimplicialPresheaf.{w} C) :
    Mono ((Φ.presheafFiber (A := SSet.{w})).map X.hom) := by
  let F := Φ.presheafFiber (A := SSet.{w})
  have h : X.hom ≫ terminal.from X.right = 𝟙 _ := terminalIsTerminal.hom_ext _ _
  have hF : F.map X.hom ≫ F.map (terminal.from X.right) = 𝟙 _ := by
    rw [← F.map_comp, h, F.map_id]
  exact mono_of_mono_fac hF

private theorem isRealizationWeakEquivalence_fiber_wedgeAxesMap
    {X X' Y Y' : PointedSimplicialPresheaf.{w} C} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : SSet.IsRealizationWeakEquivalence ((fiberAtPoint C Φ).map f))
    (hg : SSet.IsRealizationWeakEquivalence ((fiberAtPoint C Φ).map g)) :
    SSet.IsRealizationWeakEquivalence ((Φ.presheafFiber (A := SSet.{w})).map
      (Under.wedgeAxesMap f g)) := by
  let F := Φ.presheafFiber (A := SSet.{w})
  let : Mono (F.map X.hom) := mono_presheafFiber_map_point Φ X
  let : Mono (F.map X'.hom) := mono_presheafFiber_map_point Φ X'
  refine SSet.IsRealizationWeakEquivalence.pushout
    (F.map_isPushout (IsPushout.of_hasPushout X.hom Y.hom))
    (F.map_isPushout (IsPushout.of_hasPushout X'.hom Y'.hom))
    (𝟙 _) (F.map f.right) (F.map g.right) (F.map (Under.wedgeAxesMap f g))
    ?_ ?_ ?_ ?_ (SSet.IsRealizationWeakEquivalence.id _) hf hg
  · rw [Category.id_comp, ← F.map_comp, Under.w f]
  · rw [Category.id_comp, ← F.map_comp, Under.w g]
  · rw [← F.map_comp, ← F.map_comp, Under.inl_wedgeAxesMap]
  · rw [← F.map_comp, ← F.map_comp, Under.inr_wedgeAxesMap]

variable [LocallySmall.{w} C] (J)

/-- The actual smash map of two stalkwise weak equivalences is a stalkwise weak equivalence. -/
theorem stalkwiseWeakEquivalences_smashMap
    {X X' Y Y' : PointedSimplicialPresheaf.{w} C} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : stalkwiseWeakEquivalences C J f) (hg : stalkwiseWeakEquivalences C J g) :
    stalkwiseWeakEquivalences C J (Under.smashMap f g) := by
  intro Φ
  let F := Φ.presheafFiber (A := SSet.{w})
  let : Mono (Under.wedgeToProduct X Y) := Under.mono_wedgeToProduct X Y
  let : Mono (Under.wedgeToProduct X' Y') := Under.mono_wedgeToProduct X' Y'
  let : Mono (F.map (Under.wedgeToProduct X Y)) := preserves_mono_of_preservesLimit _ _
  let : Mono (F.map (Under.wedgeToProduct X' Y')) := preserves_mono_of_preservesLimit _ _
  have hf' : SSet.IsRealizationWeakEquivalence (F.map f.right) := hf Φ
  have hg' : SSet.IsRealizationWeakEquivalence (F.map g.right) := hg Φ
  have hb : SSet.IsRealizationWeakEquivalence (F.map (prod.map f.right g.right)) := by
    refine SSet.IsRealizationWeakEquivalence.of_iso_square _ _
      (PreservesLimitPair.iso F X.right Y.right) (PreservesLimitPair.iso F X'.right Y'.right)
      ?_ (hf'.prodMap hg')
    simpa only [PreservesLimitPair.iso_hom] using
      (Limits.prodComparison_natural F f.right g.right)
  change SSet.IsRealizationWeakEquivalence (F.map (Under.smashMap f g).right)
  refine SSet.IsRealizationWeakEquivalence.pushout
    (F.map_isPushout (Under.smash_isPushout_wedge X Y))
    (F.map_isPushout (Under.smash_isPushout_wedge X' Y'))
    (F.map (Under.wedgeAxesMap f g)) (F.map (prod.map f.right g.right)) (𝟙 _)
    (F.map (Under.smashMap f g).right) ?_ ?_ ?_ ?_
    (isRealizationWeakEquivalence_fiber_wedgeAxesMap Φ f g hf' hg') hb
    (SSet.IsRealizationWeakEquivalence.id _)
  · rw [← F.map_comp, ← F.map_comp, Under.wedgeToProduct_naturality]
  · rw [Category.comp_id, ← F.map_comp, terminal.comp_from]
  · rw [← F.map_comp, ← F.map_comp, Under.toSmash_smashMap]
  · rw [Category.id_comp, ← F.map_comp, Under.w (Under.smashMap f g)]

/-- Smash with a fixed right factor preserves the original stalkwise weak equivalences. -/
theorem stalkwiseWeakEquivalences_smashRightFunctor_map
    (Y : PointedSimplicialPresheaf.{w} C) {X X' : PointedSimplicialPresheaf.{w} C}
    {f : X ⟶ X'} (hf : stalkwiseWeakEquivalences C J f) :
    stalkwiseWeakEquivalences C J ((Under.smashRightFunctor Y).map f) :=
  stalkwiseWeakEquivalences_smashMap J hf ((stalkwiseWeakEquivalences C J).id_mem Y)

end CategoryTheory.PointedSimplicialPresheaf
