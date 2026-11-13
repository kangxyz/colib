/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatSingleFiber
public import Colib.AlgebraicGeometry.Chow.IntegralFundamental
public import Colib.AlgebraicGeometry.Sites.Smooth.Products
import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward
import Colib.AlgebraicGeometry.Correspondences.Graph.Postcomposition
import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-!
# Transport of a prime by graph isomorphisms

The graph of a source isomorphism has the original full support fibre,
and a target isomorphism sends the original closed support to its
closed image. Both operations preserve the actual prime coefficient.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open Function.locallyFinsuppWithin

universe u

attribute [local instance] Classical.propDecidable

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite AlgebraicCycle

variable {S : Scheme.{u}} {A A' B B' : SmoothSite S}

/-- The actual scheme product map of two smooth-site isomorphisms is an
isomorphism. -/
theorem productMap_left_isIso (f : A ⟶ A') (g : B ⟶ B') [IsIso f] [IsIso g] :
    IsIso (SmoothSite.productMap f g).left := by
  let : IsIso (SmoothSite.productMap f g) :=
    ⟨SmoothSite.productMap (inv f) (inv g),
      by simp only [← SmoothSite.productMap_comp, IsIso.hom_inv_id, SmoothSite.productMap_id],
      by simp only [← SmoothSite.productMap_comp, IsIso.inv_hom_id, SmoothSite.productMap_id]⟩
  exact inferInstanceAs (IsIso ((forgetScheme S).map (SmoothSite.productMap f g)))

variable {k : Type u} [Field k] {X X' Y Y' : SmoothSite (Spec (.of k))}

/-- Flat graph precomposition by a source isomorphism transports a prime
through the actual inverse map on the source factor. -/
theorem graph_iso_comp_single_val (e : X' ≅ X)
    (w : pullback (C := Scheme) X.hom Y.hom)
    (hw : IsFiniteCorrespondencePoint X.hom Y.hom w) :
    ((graphFunctor k).map e.hom ≫ singleFiniteCorrespondence X.hom Y.hom w hw 1).val =
      single ((SmoothSite.productMap e.inv (𝟙 Y)).left w) (1 : ℤ) := by
  classical
  let P := (integralComponentAt w).subscheme
  let j := (integralComponentAt w).subschemeι
  let p := j ≫ pullback.fst X.hom Y.hom
  let a := (SmoothSite.productMap e.inv (𝟙 Y)).left
  let V := correspondenceGraphFiber X.hom Y.hom w e.hom.left
  let F := correspondenceGraphFiberMap X'.hom X.hom Y.hom w e.hom.left
    (MorphismProperty.Over.w e.hom)
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((forgetScheme (Spec (.of k))).mapIso e).hom)
  let : IsIso a := productMap_left_isIso e.inv (𝟙 Y)
  let : IsFinite p := hw.1
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := SmoothSite.isNoetherian_overField k X
  let : IsNoetherian P := Scheme.isNoetherian_of_finiteType_of_isNoetherian p
  let : IsIntegral P := isIntegral_integralComponentAt w
  let : IsNoetherian X'.left := SmoothSite.isNoetherian_overField k X'
  let : IsNoetherian V := isNoetherian_correspondenceGraphFiber X.hom Y.hom w e.hom.left hw
  let : IsFinite F := isFinite_correspondenceGraphFiberMap X'.hom X.hom Y.hom w e.hom.left
    (MorphismProperty.Over.w e.hom) hw
  let eP : P ≅ V := (asIso (pullback.snd e.hom.left p)).symm
  have hs : eP.hom ≫ pullback.snd e.hom.left p = 𝟙 P :=
    (asIso (pullback.snd e.hom.left p)).inv_hom_id
  have hp : eP.hom ≫ pullback.fst e.hom.left p = p ≫ e.inv.left := by
    have he : e.inv.left ≫ e.hom.left = 𝟙 X.left := congrArg (fun m => m.left) e.inv_hom_id
    apply (cancel_mono e.hom.left).mp
    simp only [Category.assoc, pullback.condition (f := e.hom.left) (g := p), he]
    rw [← Category.assoc, hs, Category.id_comp]
    exact (Category.comp_id p).symm
  have ha₁ : a ≫ pullback.fst X'.hom Y.hom = pullback.fst X.hom Y.hom ≫ e.inv.left :=
    congrArg (fun m => m.left) (SmoothSite.productMap_fst e.inv (𝟙 Y))
  have ha₂ : a ≫ pullback.snd X'.hom Y.hom = pullback.snd X.hom Y.hom := by
    have h := congrArg (fun m => m.left) (SmoothSite.productMap_snd e.inv (𝟙 Y))
    change a ≫ pullback.snd X'.hom Y.hom = pullback.snd X.hom Y.hom ≫ 𝟙 _ at h
    exact h.trans (Category.comp_id _)
  have houter : eP.hom ≫ F = j ≫ a := by
    apply pullback.hom_ext (f := X'.hom) (g := Y.hom)
    · simp only [Category.assoc, F, correspondenceGraphFiberMap_fst, ha₁]
      change eP.hom ≫ pullback.fst e.hom.left p = _
      exact hp.trans (Category.assoc _ _ _)
    · simp only [Category.assoc, F, correspondenceGraphFiberMap_snd, ha₂]
      change eP.hom ≫ pullback.snd e.hom.left p ≫ j ≫ pullback.snd X.hom Y.hom = _
      rw [reassoc_of% hs]
  calc
    _ = finiteCyclePushforward F (fundamentalCycle V) :=
      graph_comp_single_val_eq_fiber_of_flat e.hom w hw
    _ = finiteCyclePushforward F (finiteCyclePushforward eP.hom (fundamentalCycle P)) :=
      congrArg (finiteCyclePushforward F) (finiteCyclePushforward_fundamentalCycle_iso eP).symm
    _ = finiteCyclePushforward (eP.hom ≫ F) (fundamentalCycle P) :=
      finiteCyclePushforward_comp_apply eP.hom F _
    _ = finiteCyclePushforward (j ≫ a) (fundamentalCycle P) :=
      DFunLike.congr_fun (AlgebraicCycle.finiteCyclePushforward_congr _ _ houter) _
    _ = _ := by
      rw [fundamentalCycle_eq_single_genericPoint,
        finiteCyclePushforward_single_of_isClosedImmersion]
      change single (a (genericPointOf (integralComponentAt w)
        (isIntegral_integralComponentAt w))) 1 = _
      rw [genericPointOf_integralComponentAt]

/-- Target graph composition by an isomorphism transports the prime
through the actual map on the target factor. -/
theorem single_comp_graph_iso_val (e : Y ≅ Y')
    (w : pullback (C := Scheme) X.hom Y.hom)
    (hw : IsFiniteCorrespondencePoint X.hom Y.hom w) :
    ((singleFiniteCorrespondence X.hom Y.hom w hw 1 : Cor.mk X ⟶ Cor.mk Y) ≫
      (graphFunctor k).map e.hom).val =
        single ((SmoothSite.productMap (𝟙 X) e.hom).left w) (1 : ℤ) := by
  classical
  let a := (SmoothSite.productMap (𝟙 X) e.hom).left
  let j := (integralComponentAt w).subschemeι
  let : IsIntegral (integralComponentAt w).subscheme := isIntegral_integralComponentAt w
  let F := correspondenceGraphPostcompositionMap X.hom Y.hom Y'.hom
    e.hom.left (MorphismProperty.Over.w e.hom) w
  let : IsIso a := productMap_left_isIso (𝟙 X) e.hom
  let : IsFinite F := isFinite_correspondenceGraphPostcompositionMap X.hom Y.hom Y'.hom
    e.hom.left (MorphismProperty.Over.w e.hom) w hw
  have ha₁ : a ≫ pullback.fst X.hom Y'.hom = pullback.fst X.hom Y.hom := by
    have h := congrArg (fun m => m.left) (SmoothSite.productMap_fst (𝟙 X) e.hom)
    change a ≫ pullback.fst X.hom Y'.hom = pullback.fst X.hom Y.hom ≫ 𝟙 _ at h
    exact h.trans (Category.comp_id _)
  have ha₂ : a ≫ pullback.snd X.hom Y'.hom = pullback.snd X.hom Y.hom ≫ e.hom.left :=
    congrArg (fun m => m.left) (SmoothSite.productMap_snd (𝟙 X) e.hom)
  have hF : F = j ≫ a := by
    apply pullback.hom_ext
    · simp only [F, Category.assoc, correspondenceGraphPostcompositionMap_fst, ha₁, j]
    · simp only [F, Category.assoc, correspondenceGraphPostcompositionMap_snd, ha₂, j]
  calc
    _ = finiteCyclePushforward F (single (genericPoint (integralComponentAt w).subscheme) 1) :=
      incidenceTorPairing_single_graph_right_val X.hom Y.hom Y'.hom e.hom.left
        (MorphismProperty.Over.w e.hom) (finite_genericPoints k (Cor.mk Y)) w hw
    _ = finiteCyclePushforward (j ≫ a)
        (single (genericPoint (integralComponentAt w).subscheme) 1) :=
      DFunLike.congr_fun (AlgebraicCycle.finiteCyclePushforward_congr _ _ hF) _
    _ = _ := by
      rw [finiteCyclePushforward_single_of_isClosedImmersion]
      change single (a (genericPointOf (integralComponentAt w)
        (isIntegral_integralComponentAt w))) 1 = _
      rw [genericPointOf_integralComponentAt]

end AlgebraicGeometry.Cor
