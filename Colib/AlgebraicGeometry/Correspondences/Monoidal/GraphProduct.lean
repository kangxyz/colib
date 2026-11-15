/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.ClopenFundamental
import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor
public import Colib.AlgebraicGeometry.Correspondences.Graph.NormalIncidence
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Exterior
public import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Exterior products of ordinary graphs

The graph components project isomorphically to their open and closed source
components. The products of these open components partition the product
scheme. Summing their fundamental cycles gives the whole fundamental cycle
of the product, whose graph pushforward is the native graph correspondence.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
variable {X Y U V : SmoothSite (Spec (.of k))} (f : X ⟶ Y) (g : U ⟶ V)

private abbrev graphComponent (a : X.left) :=
  integralComponentAt (correspondenceGraphMap X.hom Y.hom f.left (MorphismProperty.Over.w f) a)

private abbrev graphComponentSource (a : X.left) :=
  exteriorSupportSourceProjection X Y (graphComponent f a)

private abbrev graphProductSupport (a : X.left) (b : U.left) : Scheme.{u} :=
  correspondenceExteriorSupport X Y U V (graphComponent f a) (graphComponent g b)

private abbrev graphProductSource (a : X.left) (b : U.left) :
    graphProductSupport f g a b ⟶ (SmoothSite.product X U).left :=
  correspondenceExteriorSource X Y U V (graphComponent f a) (graphComponent g b)

private abbrev graphProductInclusion (a : X.left) (b : U.left) :
    graphProductSupport f g a b ⟶
      pullback (SmoothSite.product X U).hom (SmoothSite.product Y V).hom :=
  correspondenceExteriorInclusion X Y U V (graphComponent f a) (graphComponent g b)

private instance graphComponentSource_isOpenImmersion (a : genericPoints X.left) :
    IsOpenImmersion (graphComponentSource f a.val) := by
  let : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    SmoothSite.isLocallyNoetherian_overField k X
  let : IsNormal ((𝟭 Scheme).obj X.left) := SmoothSite.isNormal_overField k X
  exact isOpenImmersion_integralComponentAt_graphMap_fst X.hom Y.hom f.left
    (MorphismProperty.Over.w f) a

private instance graphComponentSource_isFinite (a : genericPoints X.left) :
    IsFinite (graphComponentSource f a.val) :=
  (isFiniteCorrespondencePoint_graphMap X.hom Y.hom f.left (MorphismProperty.Over.w f) a).1

private instance graphProductSource_isOpenImmersion (a : genericPoints X.left)
    (b : genericPoints U.left) : IsOpenImmersion (graphProductSource f g a.val b.val) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion (graphComponentSource f a.val))
    (inferInstance : IsOpenImmersion (graphComponentSource g b.val)) rfl rfl

private instance graphProductSource_isFinite (a : genericPoints X.left) (b : genericPoints U.left) :
    IsFinite (graphProductSource f g a.val b.val) :=
  correspondenceExteriorSource_isFinite X Y U V (graphComponent f a.val) (graphComponent g b.val)

private instance graphProductSource_isClosedImmersion (a : genericPoints X.left)
    (b : genericPoints U.left) : IsClosedImmersion (graphProductSource f g a.val b.val) := by
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

private instance graphProductSupport_isNoetherian (a : genericPoints X.left)
    (b : genericPoints U.left) : IsNoetherian (graphProductSupport f g a.val b.val) :=
  Scheme.isNoetherian_of_finiteType_of_isNoetherian (graphProductSource f g a.val b.val)

private theorem graphProductSource_range (a : genericPoints X.left) (b : genericPoints U.left) :
    Set.range (graphProductSource f g a.val b.val) =
      (pullback.fst X.hom U.hom) ⁻¹' closure ({a.val} : Set X.left) ∩
        (pullback.snd X.hom U.hom) ⁻¹' closure ({b.val} : Set U.left) := by
  change Set.range (pullback.map _ _ X.hom U.hom (graphComponentSource f a.val)
    (graphComponentSource g b.val) (𝟙 _) (Category.comp_id _) (Category.comp_id _)) = _
  rw [Scheme.Pullback.range_map]
  have ha := range_integralComponentAt_graphMap_fst
    X.hom Y.hom f.left (MorphismProperty.Over.w f) a.val
  have hb := range_integralComponentAt_graphMap_fst
    U.hom V.hom g.left (MorphismProperty.Over.w g) b.val
  exact congrArg₂ (fun A B =>
    (pullback.fst X.hom U.hom) ⁻¹' A ∩ (pullback.snd X.hom U.hom) ⁻¹' B) ha hb

private theorem unique_component (A : SmoothSite (Spec (.of k))) (x : A.left) :
    ∃! a : genericPoints A.left, x ∈ closure ({a.val} : Set A.left) := by
  let C : irreducibleComponents A.left :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let a := genericPoints.ofComponent C
  have ha : closure ({a.val} : Set A.left) = irreducibleComponent x :=
    congrArg Subtype.val (genericPoints.component_ofComponent C)
  have hx : x ∈ closure ({a.val} : Set A.left) := ha.symm ▸ mem_irreducibleComponent
  refine ⟨a, hx, fun b hb => ?_⟩
  apply genericPoints.component_injective
  apply Subtype.ext
  by_contra hne
  exact (Set.disjoint_left.mp
    (SmoothSite.pairwiseDisjoint_irreducibleComponents k A b.property a.property hne)) hb hx

private theorem unique_graphProductSource (x : (SmoothSite.product X U).left) :
    ∃! ab : genericPoints X.left × genericPoints U.left,
      x ∈ Set.range (graphProductSource f g ab.1.val ab.2.val) := by
  obtain ⟨a, ha, ha'⟩ := unique_component X (pullback.fst X.hom U.hom x)
  obtain ⟨b, hb, hb'⟩ := unique_component U (pullback.snd X.hom U.hom x)
  refine ⟨(a, b), ?_, ?_⟩
  · change x ∈ Set.range (graphProductSource f g a.val b.val)
    rw [graphProductSource_range f g a b]
    exact ⟨ha, hb⟩
  · rintro ⟨a', b'⟩ h
    change x ∈ Set.range (graphProductSource f g a'.val b'.val) at h
    rw [graphProductSource_range f g a' b'] at h
    exact Prod.ext (ha' a' h.1) (hb' b' h.2)

private theorem graphProductInclusion_eq (a : genericPoints X.left) (b : genericPoints U.left) :
    graphProductInclusion f g a.val b.val = graphProductSource f g a.val b.val ≫
      correspondenceGraphMap (SmoothSite.product X U).hom (SmoothSite.product Y V).hom
        (SmoothSite.productMap f g).left (MorphismProperty.Over.w (SmoothSite.productMap f g)) := by
  let A := graphComponent f a.val
  let B := graphComponent g b.val
  let r := correspondenceExteriorInclusion X Y U V A B
  let p := correspondenceExteriorSource X Y U V A B
  let q := correspondenceExteriorTarget X Y U V A B
  let h := (SmoothSite.productMap f g).left
  have hf : h ≫ pullback.fst Y.hom V.hom = pullback.fst X.hom U.hom ≫ f.left :=
    congrArg (fun m => m.left) (SmoothSite.productMap_fst f g)
  have hg : h ≫ pullback.snd Y.hom V.hom = pullback.snd X.hom U.hom ≫ g.left :=
    congrArg (fun m => m.left) (SmoothSite.productMap_snd f g)
  have ha : exteriorSupportTargetProjection X Y A =
      exteriorSupportSourceProjection X Y A ≫ f.left :=
    integralComponentAt_graphMap_snd X.hom Y.hom f.left (MorphismProperty.Over.w f) a.val
  have hb : exteriorSupportTargetProjection U V B =
      exteriorSupportSourceProjection U V B ≫ g.left :=
    integralComponentAt_graphMap_snd U.hom V.hom g.left (MorphismProperty.Over.w g) b.val
  have hq : q = p ≫ h := by
    apply pullback.hom_ext
    · change correspondenceExteriorTarget X Y U V A B ≫ pullback.fst Y.hom V.hom =
        (correspondenceExteriorSource X Y U V A B ≫ h) ≫ pullback.fst Y.hom V.hom
      rw [Category.assoc, hf, correspondenceExteriorSource_fst_assoc,
        correspondenceExteriorTarget_fst]
      exact congrArg (pullback.fst
        (exteriorSupportSourceProjection X Y A ≫ X.hom)
        (exteriorSupportSourceProjection U V B ≫ U.hom) ≫ ·) ha
    · change correspondenceExteriorTarget X Y U V A B ≫ pullback.snd Y.hom V.hom =
        (correspondenceExteriorSource X Y U V A B ≫ h) ≫ pullback.snd Y.hom V.hom
      rw [Category.assoc, hg, correspondenceExteriorSource_snd_assoc,
        correspondenceExteriorTarget_snd]
      exact congrArg (pullback.snd
        (exteriorSupportSourceProjection X Y A ≫ X.hom)
        (exteriorSupportSourceProjection U V B ≫ U.hom) ≫ ·) hb
  let γ := correspondenceGraphMap (SmoothSite.product X U).hom (SmoothSite.product Y V).hom
    h (MorphismProperty.Over.w (SmoothSite.productMap f g))
  change r = p ≫ γ
  apply pullback.hom_ext
  · dsimp only [r, γ]
    rw [Category.assoc, correspondenceExteriorInclusion_fst, correspondenceGraphMap_fst,
      Category.comp_id]
  · dsimp only [r, γ]
    rw [Category.assoc, correspondenceExteriorInclusion_snd, correspondenceGraphMap_snd]
    exact hq

private theorem graphProduct_fundamentalCycle :
    letI := (Cor.finite_genericPoints k (Cor.mk X)).fintype
    letI := (Cor.finite_genericPoints k (Cor.mk U)).fintype
    (∑ ab : genericPoints X.left × genericPoints U.left,
        finiteCyclePushforward (graphProductSource f g ab.1.val ab.2.val)
          (AlgebraicCycle.fundamentalCycle (graphProductSupport f g ab.1.val ab.2.val))) =
      AlgebraicCycle.fundamentalCycle (SmoothSite.product X U).left := by
  let := (Cor.finite_genericPoints k (Cor.mk X)).fintype
  let := (Cor.finite_genericPoints k (Cor.mk U)).fintype
  exact (fundamentalCycle_eq_sum_clopen
    (fun ab : genericPoints X.left × genericPoints U.left =>
      graphProductSupport f g ab.1.val ab.2.val)
    (fun ab => graphProductSource f g ab.1.val ab.2.val)
    (unique_graphProductSource f g)).symm

/-- The exterior product of native ordinary graphs is the native product graph. -/
theorem exteriorProduct_graph (f : X ⟶ Y) (g : U ⟶ V) :
    exteriorProduct ((graphFunctor k).map f) ((graphFunctor k).map g) =
      (graphFunctor k).map (SmoothSite.productMap f g) := by
  classical
  let hX := Cor.finite_genericPoints k (Cor.mk X)
  let hU := Cor.finite_genericPoints k (Cor.mk U)
  let := hX.fintype
  let := hU.fintype
  simp only [graphFunctor_map, exteriorProduct]
  change correspondenceExterior X Y U V
      (graphCorrespondenceOfComponents X.hom Y.hom f.left (MorphismProperty.Over.w f) hX)
      (graphCorrespondenceOfComponents U.hom V.hom g.left (MorphismProperty.Over.w g) hU) = _
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence X.hom Y.hom,
    graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence U.hom V.hom]
  let c := correspondenceExterior X Y U V
  let p (a : genericPoints X.left) : finiteCorrespondences X.hom Y.hom :=
    singleFiniteCorrespondence X.hom Y.hom
      (correspondenceGraphMap X.hom Y.hom f.left (MorphismProperty.Over.w f) a.val)
      (isFiniteCorrespondencePoint_graphMap X.hom Y.hom f.left (MorphismProperty.Over.w f) a) 1
  let q (b : genericPoints U.left) : finiteCorrespondences U.hom V.hom :=
    singleFiniteCorrespondence U.hom V.hom
      (correspondenceGraphMap U.hom V.hom g.left (MorphismProperty.Over.w g) b.val)
      (isFiniteCorrespondencePoint_graphMap U.hom V.hom g.left (MorphismProperty.Over.w g) b) 1
  have hsum :
      c (∑ a, p a) (∑ b, q b) =
        ∑ ab : genericPoints X.left × genericPoints U.left, c (p ab.1) (q ab.2) := by
    rw [← AddMonoidHom.flip_apply, map_sum, Fintype.sum_prod_type' (fun a b => c (p a) (q b))]
    apply Finset.sum_congr rfl
    intro a _
    rw [AddMonoidHom.flip_apply, map_sum]
  change c (∑ a, p a) (∑ b, q b) = _
  rw [hsum]
  apply Subtype.ext
  let γ := correspondenceGraphMap (SmoothSite.product X U).hom (SmoothSite.product Y V).hom
    (SmoothSite.productMap f g).left (MorphismProperty.Over.w (SmoothSite.productMap f g))
  let : IsClosedImmersion γ := isClosedImmersion_correspondenceGraphMap _ _ _ _
  let : IsNoetherian ((𝟭 Scheme).obj (SmoothSite.product X U).left) :=
    SmoothSite.isNoetherian_overField k (SmoothSite.product X U)
  let : IsReduced ((𝟭 Scheme).obj (SmoothSite.product X U).left) :=
    inferInstanceAs (IsReduced (SmoothSite.product X U).left)
  have hΓ := finiteCyclePushforward_fundamentalCycle_graph
    (SmoothSite.product X U).hom (SmoothSite.product Y V).hom
    (SmoothSite.productMap f g).left (MorphismProperty.Over.w (SmoothSite.productMap f g))
  change finiteCyclePushforward γ (AlgebraicCycle.fundamentalCycle (SmoothSite.product X U).left) =
    _ at hΓ
  rw [← hΓ, ← graphProduct_fundamentalCycle f g]
  change (finiteCorrespondences (SmoothSite.product X U).hom (SmoothSite.product Y V).hom).subtype
    (∑ ab : genericPoints X.left × genericPoints U.left, c (p ab.1) (q ab.2)) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ _
  let z := correspondenceGraphMap X.hom Y.hom f.left (MorphismProperty.Over.w f) a.val
  let w := correspondenceGraphMap U.hom V.hom g.left (MorphismProperty.Over.w g) b.val
  have hz : IsFiniteCorrespondencePoint X.hom Y.hom z :=
    isFiniteCorrespondencePoint_graphMap X.hom Y.hom f.left (MorphismProperty.Over.w f) a
  have hw : IsFiniteCorrespondencePoint U.hom V.hom w :=
    isFiniteCorrespondencePoint_graphMap U.hom V.hom g.left (MorphismProperty.Over.w g) b
  change ((correspondenceExterior X Y U V)
    (singleFiniteCorrespondence X.hom Y.hom z hz 1)
    (singleFiniteCorrespondence U.hom V.hom w hw 1)).val =
      finiteCyclePushforward γ (finiteCyclePushforward (graphProductSource f g a.val b.val)
        (AlgebraicCycle.fundamentalCycle (graphProductSupport f g a.val b.val)))
  rw [correspondenceExterior_single, one_mul, one_smul]
  let c₀ := AlgebraicCycle.fundamentalCycle (graphProductSupport f g a.val b.val)
  have hcomp := finiteCyclePushforward_comp_apply (graphProductSource f g a.val b.val) γ c₀
  calc
    _ = finiteCyclePushforward (graphProductInclusion f g a.val b.val) c₀ :=
      correspondenceExteriorPrime_val X Y U V z w hz hw
    _ = _ :=
      (finiteCyclePushforward_congr _ _ (graphProductInclusion_eq f g a b) c₀).trans hcomp.symm

end AlgebraicGeometry.Cor
