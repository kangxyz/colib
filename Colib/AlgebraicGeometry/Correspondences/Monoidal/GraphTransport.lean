/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Isomorphism
import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction

/-!
# Cycle transport by graph isomorphisms

Precomposition by a graph isomorphism pushes a signed cycle through the
inverse source change. Postcomposition pushes it through the target change.
Together they transport the original cycles through the actual map of products.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
variable {X X' Y Y' : SmoothSite (Spec (.of k))}

/-- A graph isomorphism acts on the source by native pushforward along its inverse. -/
theorem graph_iso_comp_val (e : X' ≅ X) (a : Cor.mk X ⟶ Cor.mk Y) :
    letI : IsIso (SmoothSite.productMap e.inv (𝟙 Y)).left :=
      productMap_left_isIso e.inv (𝟙 Y)
    ((graphFunctor k).map e.hom ≫ a).val =
      finiteCyclePushforward (SmoothSite.productMap e.inv (𝟙 Y)).left a.val := by
  classical
  let r := (SmoothSite.productMap e.inv (𝟙 Y)).left
  let : IsIso r := productMap_left_isIso e.inv (𝟙 Y)
  let F : finiteCorrespondences X.hom Y.hom →+
      AlgebraicCycle (pullback (C := Scheme) X'.hom Y.hom) ℤ :=
    (finiteCorrespondences X'.hom Y.hom).subtype.comp
      (Preadditive.leftComp (Cor.mk Y) ((graphFunctor k).map e.hom))
  let G : finiteCorrespondences X.hom Y.hom →+
      AlgebraicCycle (pullback (C := Scheme) X'.hom Y.hom) ℤ :=
    (finiteCyclePushforward r).comp (finiteCorrespondences X.hom Y.hom).subtype
  have h : F = G := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    change ((graphFunctor k).map e.hom ≫ singleFiniteCorrespondence X.hom Y.hom z hz 1).val =
      finiteCyclePushforward r (Function.locallyFinsuppWithin.single z 1)
    rw [finiteCyclePushforward_single_of_isClosedImmersion]
    exact graph_iso_comp_single_val e z hz
  exact DFunLike.congr_fun h a

/-- A graph isomorphism acts on the target by native pushforward along its underlying map. -/
theorem comp_graph_iso_val (e : Y ≅ Y') (a : Cor.mk X ⟶ Cor.mk Y) :
    letI : IsIso (SmoothSite.productMap (𝟙 X) e.hom).left :=
      productMap_left_isIso (𝟙 X) e.hom
    (a ≫ (graphFunctor k).map e.hom).val =
      finiteCyclePushforward (SmoothSite.productMap (𝟙 X) e.hom).left a.val := by
  classical
  let r := (SmoothSite.productMap (𝟙 X) e.hom).left
  let : IsIso r := productMap_left_isIso (𝟙 X) e.hom
  let F : finiteCorrespondences X.hom Y.hom →+
      AlgebraicCycle (pullback (C := Scheme) X.hom Y'.hom) ℤ :=
    (finiteCorrespondences X.hom Y'.hom).subtype.comp
      (Preadditive.rightComp (Cor.mk X) ((graphFunctor k).map e.hom))
  let G : finiteCorrespondences X.hom Y.hom →+
      AlgebraicCycle (pullback (C := Scheme) X.hom Y'.hom) ℤ :=
    (finiteCyclePushforward r).comp (finiteCorrespondences X.hom Y.hom).subtype
  have h : F = G := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    change ((singleFiniteCorrespondence X.hom Y.hom z hz 1 : Cor.mk X ⟶ Cor.mk Y) ≫
        (graphFunctor k).map e.hom).val =
      finiteCyclePushforward r (Function.locallyFinsuppWithin.single z 1)
    rw [finiteCyclePushforward_single_of_isClosedImmersion]
    exact single_comp_graph_iso_val e z hz
  exact DFunLike.congr_fun h a

/-- Simultaneous source and target transport computes the graph naturality square. -/
theorem comp_graph_iso_eq_graph_iso_comp (e : X ≅ X') (d : Y ≅ Y')
    (a : Cor.mk X ⟶ Cor.mk Y) (b : Cor.mk X' ⟶ Cor.mk Y')
    (h : letI : IsIso (SmoothSite.productMap e.hom d.hom).left :=
        productMap_left_isIso e.hom d.hom
      finiteCyclePushforward (SmoothSite.productMap e.hom d.hom).left a.val = b.val) :
    a ≫ (graphFunctor k).map d.hom = (graphFunctor k).map e.hom ≫ b := by
  let E := (graphFunctor k).mapIso e
  let p := (SmoothSite.productMap e.hom (𝟙 Y)).left
  let q := (SmoothSite.productMap (𝟙 X') d.hom).left
  let r := (SmoothSite.productMap e.hom d.hom).left
  let : IsIso p := productMap_left_isIso e.hom (𝟙 Y)
  let : IsIso q := productMap_left_isIso (𝟙 X') d.hom
  let : IsIso r := productMap_left_isIso e.hom d.hom
  have hpq : p ≫ q = r := by
    have hpq := (SmoothSite.productMap_comp e.hom (𝟙 X') (𝟙 Y) d.hom).symm
    simp only [Category.comp_id, Category.id_comp] at hpq
    exact congrArg (fun m => m.left) hpq
  apply (cancel_epi E.inv).mp
  change E.inv ≫ a ≫ (graphFunctor k).map d.hom = E.inv ≫ E.hom ≫ b
  rw [Iso.inv_hom_id_assoc, ← Category.assoc]
  apply Subtype.ext
  change (((graphFunctor k).map e.inv ≫ a) ≫ (graphFunctor k).map d.hom).val = b.val
  calc
    _ = finiteCyclePushforward q (finiteCyclePushforward p a.val) :=
      (comp_graph_iso_val d ((graphFunctor k).map e.inv ≫ a)).trans
        (congrArg (finiteCyclePushforward q) (graph_iso_comp_val e.symm a))
    _ = finiteCyclePushforward r a.val :=
      (finiteCyclePushforward_comp_apply p q _).trans
        (finiteCyclePushforward_congr _ _ hpq _)
    _ = _ := h

end AlgebraicGeometry.Cor
