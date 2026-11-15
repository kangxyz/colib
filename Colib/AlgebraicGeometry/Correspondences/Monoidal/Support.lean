/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Dominance
public import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian

/-!
# Supports of exterior products of finite correspondences

The support is the literal product of the two original integral closed
subschemes. Its map to the product of the sources is finite and universally
open. Consequently every generic component maps onto a source component,
even when the support product is reducible or nonreduced.

The argument uses the existing universal openness theorem for finite
correspondences over smooth schemes, whose input is Stacks 0F32. No geometric
integrality of the smooth factors or perfection of the field is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

/-- A finite open map sends each generic component onto a component of its target. -/
theorem finiteUniversallyOpen_range_integralComponentAt {A B : Scheme.{u}}
    (p : A ⟶ B) [IsFinite p] [UniversallyOpen p]
    (a : A) (ha : a ∈ genericPoints A) :
    Set.range ((integralComponentAt a).subschemeι ≫ p) ∈ irreducibleComponents B := by
  rw [finiteCyclePushforward_range_integralComponentAt, coe_support_integralComponentAt]
  have himage : p.base '' closure ({a} : Set A) = closure ({p a} : Set B) := by
    simpa only [Set.image_singleton] using
      (p.isClosedMap.closure_image_eq_of_continuous p.continuous ({a} : Set A)).symm
  rw [himage]
  exact mem_genericPoints_of_generalizingMap
    ((liftsGeneralizations_iff_generalizingMap p).mp
      (liftsGeneralizations_of_isOpenMap p p.isOpenMap)) ha

/-- The whole fundamental cycle of a finite universally open support span is admissible. -/
theorem finiteCyclePushforward_fundamentalCycle_mem_of_universallyOpen
    {A X Y S : Scheme.{u}} [IsNoetherian A] (f : X ⟶ S) (g : Y ⟶ S)
    [IsSeparated g] [LocallyOfFiniteType g]
    (r : A ⟶ pullback f g) [IsFinite r]
    [IsFinite (r ≫ pullback.fst f g)] [UniversallyOpen (r ≫ pullback.fst f g)] :
    finiteCyclePushforward r (AlgebraicCycle.fundamentalCycle A) ∈
      finiteCorrespondences f g := by
  apply finiteCyclePushforward_mem_finiteCorrespondences f g r _
    (AlgebraicCycle.finite_support_fundamentalCycle A)
  · intro a _
    rw [Category.assoc]
    infer_instance
  · intro a ha
    rw [Category.assoc]
    exact finiteUniversallyOpen_range_integralComponentAt (r ≫ pullback.fst f g) a
      (AlgebraicCycle.support_fundamentalCycle_subset A ha)

variable {k : Type u} [Field k] (X Y U V : SmoothSite (Spec (.of k)))
  (W : (pullback X.hom Y.hom).IdealSheafData)
  (Z : (pullback U.hom V.hom).IdealSheafData)

/-- The product of the original supports, with its scheme structure intact. -/
abbrev correspondenceExteriorSupport : Scheme.{u} :=
  pullback (exteriorSupportSourceProjection X Y W ≫ X.hom)
    (exteriorSupportSourceProjection U V Z ≫ U.hom)

/-- The source map of the product of the two supports. -/
def correspondenceExteriorSource :
    correspondenceExteriorSupport X Y U V W Z ⟶ (SmoothSite.product X U).left :=
  pullback.map _ _ _ _ (exteriorSupportSourceProjection X Y W)
    (exteriorSupportSourceProjection U V Z) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem correspondenceExteriorSource_fst :
    correspondenceExteriorSource X Y U V W Z ≫ pullback.fst X.hom U.hom =
      pullback.fst _ _ ≫ exteriorSupportSourceProjection X Y W :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceExteriorSource_snd :
    correspondenceExteriorSource X Y U V W Z ≫ pullback.snd X.hom U.hom =
      pullback.snd _ _ ≫ exteriorSupportSourceProjection U V Z :=
  pullback.lift_snd _ _ _

/-- Products preserve the finite source maps by two base changes. -/
instance correspondenceExteriorSource_isFinite
    [IsFinite (exteriorSupportSourceProjection X Y W)]
    [IsFinite (exteriorSupportSourceProjection U V Z)] :
    IsFinite (correspondenceExteriorSource X Y U V W Z) := by
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    (inferInstance : IsFinite (exteriorSupportSourceProjection X Y W))
    (inferInstance : IsFinite (exteriorSupportSourceProjection U V Z)) rfl rfl

/-- The same two base changes preserve universal openness. -/
instance correspondenceExteriorSource_universallyOpen
    [UniversallyOpen (exteriorSupportSourceProjection X Y W)]
    [UniversallyOpen (exteriorSupportSourceProjection U V Z)] :
    UniversallyOpen (correspondenceExteriorSource X Y U V W Z) := by
  exact MorphismProperty.pullbackMap (P := @UniversallyOpen)
    (inferInstance : UniversallyOpen (exteriorSupportSourceProjection X Y W))
    (inferInstance : UniversallyOpen (exteriorSupportSourceProjection U V Z)) rfl rfl

/-- The target map of the same product of supports. -/
def correspondenceExteriorTarget :
    correspondenceExteriorSupport X Y U V W Z ⟶ (SmoothSite.product Y V).left :=
  pullback.lift
    (pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom)
      (exteriorSupportSourceProjection U V Z ≫ U.hom) ≫
        exteriorSupportTargetProjection X Y W)
    (pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom)
      (exteriorSupportSourceProjection U V Z ≫ U.hom) ≫
        exteriorSupportTargetProjection U V Z) (by
      have h := (congrArg
        (pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom)
          (exteriorSupportSourceProjection U V Z ≫ U.hom) ≫ ·)
        (exteriorSupport_projection_base X Y W)).symm.trans
          (pullback.condition.trans (congrArg
            (pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom)
              (exteriorSupportSourceProjection U V Z ≫ U.hom) ≫ ·)
            (exteriorSupport_projection_base U V Z)))
      simpa only [Category.assoc] using h)

@[reassoc (attr := simp)]
theorem correspondenceExteriorTarget_fst :
    correspondenceExteriorTarget X Y U V W Z ≫ pullback.fst Y.hom V.hom =
      pullback.fst _ _ ≫ exteriorSupportTargetProjection X Y W :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceExteriorTarget_snd :
    correspondenceExteriorTarget X Y U V W Z ≫ pullback.snd Y.hom V.hom =
      pullback.snd _ _ ≫ exteriorSupportTargetProjection U V Z :=
  pullback.lift_snd _ _ _

/-- The canonical inclusion after exchanging the two middle factors. -/
def correspondenceExteriorInclusion : correspondenceExteriorSupport X Y U V W Z ⟶
    pullback (SmoothSite.product X U).hom (SmoothSite.product Y V).hom :=
  pullback.lift (correspondenceExteriorSource X Y U V W Z)
    (correspondenceExteriorTarget X Y U V W Z) (by
      simp only [SmoothSite.product_hom, ← Category.assoc,
        correspondenceExteriorSource_fst, correspondenceExteriorTarget_fst]
      simpa only [Category.assoc] using
        congrArg (pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom)
          (exteriorSupportSourceProjection U V Z ≫ U.hom) ≫ ·)
          (exteriorSupport_projection_base X Y W))

@[reassoc]
theorem correspondenceExteriorInclusion_fst :
    correspondenceExteriorInclusion X Y U V W Z ≫
      pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y V).hom =
        correspondenceExteriorSource X Y U V W Z :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem correspondenceExteriorInclusion_snd :
    correspondenceExteriorInclusion X Y U V W Z ≫
      pullback.snd (SmoothSite.product X U).hom (SmoothSite.product Y V).hom =
        correspondenceExteriorTarget X Y U V W Z :=
  pullback.lift_snd _ _ _

instance correspondenceExteriorInclusion_isFinite
    [IsFinite (exteriorSupportSourceProjection X Y W)]
    [IsFinite (exteriorSupportSourceProjection U V Z)] :
    IsFinite (correspondenceExteriorInclusion X Y U V W Z) := by
  have : IsFinite (correspondenceExteriorInclusion X Y U V W Z ≫
      pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y V).hom) := by
    rw [correspondenceExteriorInclusion_fst]
    infer_instance
  exact IsFinite.of_comp _ (pullback.fst _ _)

instance correspondenceExteriorInclusion_mono :
    Mono (correspondenceExteriorInclusion X Y U V W Z) where
  right_cancellation {A} f g h := by
    have hs := congrArg (fun a => a ≫
      pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y V).hom) h
    have ht := congrArg (fun a => a ≫
      pullback.snd (SmoothSite.product X U).hom (SmoothSite.product Y V).hom) h
    simp only [Category.assoc, correspondenceExteriorInclusion_fst] at hs
    simp only [Category.assoc, correspondenceExteriorInclusion_snd] at ht
    apply pullback.hom_ext
    · apply (cancel_mono W.subschemeι).mp
      apply pullback.hom_ext
      · simpa only [Category.assoc, correspondenceExteriorSource_fst,
          exteriorSupportSourceProjection] using
          congrArg (fun a => a ≫ pullback.fst X.hom U.hom) hs
      · simpa only [Category.assoc, correspondenceExteriorTarget_fst,
          exteriorSupportTargetProjection] using
          congrArg (fun a => a ≫ pullback.fst Y.hom V.hom) ht
    · apply (cancel_mono Z.subschemeι).mp
      apply pullback.hom_ext
      · simpa only [Category.assoc, correspondenceExteriorSource_snd,
          exteriorSupportSourceProjection] using
          congrArg (fun a => a ≫ pullback.snd X.hom U.hom) hs
      · simpa only [Category.assoc, correspondenceExteriorTarget_snd,
          exteriorSupportTargetProjection] using
          congrArg (fun a => a ≫ pullback.snd Y.hom V.hom) ht

/-- The whole support product embeds as a closed subscheme of the correspondence ambient. -/
instance correspondenceExteriorInclusion_isClosedImmersion
    [IsFinite (exteriorSupportSourceProjection X Y W)]
    [IsFinite (exteriorSupportSourceProjection U V Z)] :
    IsClosedImmersion (correspondenceExteriorInclusion X Y U V W Z) :=
  (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

end Stacks.Chow
