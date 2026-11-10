/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.Products
public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.GeometricallyIntegral
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The native prime support after adjoining an algebraic simplex

The support is the literal product of the native integral closed subscheme with
the existing simplex. Its two projections use the same simplex coordinate.
Its closed image is again finite and surjective onto a source component.
The component argument uses the equivalence of components under an open,
geometrically irreducible morphism, so it includes disconnected sources.

The support construction adapts
`Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Basic.lean`
at commit `a6805c4a87cdfd7717dd7a94039246a167f15380`. The component argument and
prime indexing here use the pinned native Mathlib and Stacks APIs directly.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  (z : pullback (C := Scheme) X.hom Y.hom) (n : ℕ)

/-- The original native integral support times the actual algebraic simplex. -/
abbrev simplexExteriorSupport : Scheme.{u} :=
  pullback ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom ≫ X.hom)
    (AlgebraicSimplex.smoothSiteObj k n).hom

/-- The projection to the source product is the base change of the original finite map. -/
def simplexExteriorSource : simplexExteriorSupport z n ⟶
    (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left :=
  pullback.map _ _ _ _ ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom)
    (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem simplexExteriorSource_fst :
    simplexExteriorSource z n ≫ pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem simplexExteriorSource_snd :
    simplexExteriorSource z n ≫ pullback.snd X.hom (AlgebraicSimplex.smoothSiteObj k n).hom =
      pullback.snd _ _ := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The source projection is an actual pullback square. -/
theorem simplexExteriorSource_isPullback :
    IsPullback (simplexExteriorSource z n) (pullback.fst _ _)
      (pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom)
      ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom) := by
  apply IsPullback.flip
  refine IsPullback.of_bot
    (t := IsPullback.of_hasPullback X.hom (AlgebraicSimplex.smoothSiteObj k n).hom) ?_
    (simplexExteriorSource_fst z n).symm
  simpa only [simplexExteriorSource_snd, Category.assoc] using
    (IsPullback.of_hasPullback
      ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom ≫ X.hom)
      (AlgebraicSimplex.smoothSiteObj k n).hom)

/-- The target projection retains the identical simplex coordinate. -/
def simplexExteriorTarget : simplexExteriorSupport z n ⟶
    (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).left :=
  pullback.lift
    (pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫ pullback.snd X.hom Y.hom)
    (pullback.snd _ _) (by
      simp only [Category.assoc]
      rw [← pullback.condition]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem simplexExteriorTarget_fst :
    simplexExteriorTarget z n ≫ pullback.fst Y.hom (AlgebraicSimplex.smoothSiteObj k n).hom =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫ pullback.snd X.hom Y.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem simplexExteriorTarget_snd :
    simplexExteriorTarget z n ≫ pullback.snd Y.hom (AlgebraicSimplex.smoothSiteObj k n).hom =
      pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The closed support map into the product of the two enlarged objects. -/
def simplexExteriorInclusion : simplexExteriorSupport z n ⟶
    pullback (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom :=
  pullback.lift (simplexExteriorSource z n) (simplexExteriorTarget z n) (by
    simp only [SmoothSite.product_hom, ← Category.assoc,
      simplexExteriorSource_fst, simplexExteriorTarget_fst]
    simp only [Category.assoc, pullback.condition])

@[reassoc]
theorem simplexExteriorInclusion_fst :
    simplexExteriorInclusion z n ≫
      pullback.fst (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom =
      simplexExteriorSource z n :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem simplexExteriorInclusion_snd :
    simplexExteriorInclusion z n ≫
      pullback.snd (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom =
      simplexExteriorTarget z n :=
  pullback.lift_snd _ _ _

instance simplexExteriorInclusion_mono : Mono (simplexExteriorInclusion z n) where
  right_cancellation {W} f g h := by
    have hs := congrArg (fun a => a ≫ pullback.fst
      (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom) h
    have ht := congrArg (fun a => a ≫ pullback.snd
      (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom) h
    simp only [Category.assoc, simplexExteriorInclusion_fst] at hs
    simp only [Category.assoc, simplexExteriorInclusion_snd] at ht
    apply pullback.hom_ext
    · apply (cancel_mono (integralComponentAt z).subschemeι).mp
      apply pullback.hom_ext
      · simpa only [Category.assoc, simplexExteriorSource_fst] using
          congrArg (fun a => a ≫ pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom) hs
      · simpa only [Category.assoc, simplexExteriorTarget_fst] using
          congrArg (fun a => a ≫ pullback.fst Y.hom (AlgebraicSimplex.smoothSiteObj k n).hom) ht
    · simpa only [Category.assoc, simplexExteriorSource_snd] using
        congrArg (fun a => a ≫ pullback.snd X.hom (AlgebraicSimplex.smoothSiteObj k n).hom) hs

/-- Adjoining the simplex preserves integrality of every native prime support. -/
instance simplexExteriorSupport_isIntegral : IsIntegral (simplexExteriorSupport z n) := by
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) X.hom
  let : IsLocallyNoetherian (pullback X.hom Y.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X.left) (pullback.fst X.hom Y.hom)
  let : IsLocallyNoetherian (integralComponentAt z).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt z).subschemeι
  exact inferInstanceAs (IsIntegral (pullback
    ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom ≫ X.hom)
    (AlgebraicSimplex.smoothSiteObj k n).hom))

variable (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

include hz

/-- The source projection remains finite, by base change. -/
theorem simplexExteriorSource_isFinite : IsFinite (simplexExteriorSource z n) := by
  let : IsFinite ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom) := hz.1
  exact MorphismProperty.of_isPullback (simplexExteriorSource_isPullback z n).flip inferInstance

/-- The support inclusion is finite, since its source projection is finite. -/
theorem simplexExteriorInclusion_isFinite : IsFinite (simplexExteriorInclusion z n) := by
  have : IsFinite (simplexExteriorInclusion z n ≫
      pullback.fst (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom) := by
    simpa only [simplexExteriorInclusion_fst] using simplexExteriorSource_isFinite z n hz
  exact IsFinite.of_comp _ (pullback.fst _ _)

/-- The actual support is a closed subscheme of the product, without a replacement model. -/
theorem simplexExteriorInclusion_isClosedImmersion :
    IsClosedImmersion (simplexExteriorInclusion z n) := by
  let := simplexExteriorInclusion_isFinite z n hz
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

omit hz in
/-- The projected image is the inverse image of the original source component. -/
theorem simplexExteriorSource_range :
    Set.range (simplexExteriorSource z n) =
      (pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom) ⁻¹'
        Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom) := by
  change Set.range (pullback.map (C := Scheme)
    ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom ≫ X.hom)
    (AlgebraicSimplex.smoothSiteObj k n).hom X.hom (AlgebraicSimplex.smoothSiteObj k n).hom
    ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom)
    (𝟙 _) (𝟙 _) (by simp) (by simp)) = _
  rw [Scheme.Pullback.range_map]
  simp only [Scheme.Hom.id_base, TopCat.hom_id, ContinuousMap.coe_id,
    Set.range_id, Set.preimage_univ, Set.inter_univ]

/-- The exterior support still dominates an actual component, including for disconnected `X`. -/
theorem simplexExteriorSource_range_mem :
    Set.range (simplexExteriorSource z n) ∈
      irreducibleComponents (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left := by
  rw [simplexExteriorSource_range]
  exact ((pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom).irreducibleComponentsEquiv
    (pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom).isOpenMap).symm
      ⟨_, hz.2⟩ |>.property

/-- The closed image is integral because the literal support maps isomorphically onto it. -/
theorem simplexExteriorImage_isIntegral : IsIntegral (simplexExteriorInclusion z n).image := by
  let := simplexExteriorInclusion_isClosedImmersion z n hz
  exact IsIntegral.of_isIso (simplexExteriorInclusion z n).toImage

/-- The native prime indexing the closed exterior support. -/
def simplexExteriorPoint :
    pullback (C := Scheme) (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom :=
  genericPointOf (simplexExteriorInclusion z n).ker (simplexExteriorImage_isIntegral z n hz)

/-- The native integral closed subscheme at the new point is precisely the closed image ideal. -/
@[simp]
theorem integralComponentAt_simplexExteriorPoint :
    integralComponentAt (simplexExteriorPoint z n hz) = (simplexExteriorInclusion z n).ker :=
  integralComponentAt_genericPointOf _ _

/-- The new prime has the required finiteness and source-component properties. -/
theorem simplexExteriorPoint_admissible :
    IsFiniteCorrespondencePoint
      (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom
      (simplexExteriorPoint z n hz) := by
  let e := simplexExteriorInclusion z n
  let p := pullback.fst (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
    (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom
  let : IsClosedImmersion e := simplexExteriorInclusion_isClosedImmersion z n hz
  have he : e.toImage ≫ e.imageι ≫ p = simplexExteriorSource z n := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact simplexExteriorInclusion_fst z n
  apply (isFiniteCorrespondencePoint_genericPointOf_iff _ _ _ _).mpr
  constructor
  · have : IsFinite (e.toImage ≫ e.imageι ≫ p) := by
      rw [he]
      exact simplexExteriorSource_isFinite z n hz
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsFinite) e.toImage (e.imageι ≫ p)).mp inferInstance
  · change Set.range (e.imageι ≫ p) ∈ _
    rw [← e.toImage.surjective.range_comp]
    change Set.range (e.toImage ≫ e.imageι ≫ p) ∈ _
    rw [he]
    exact simplexExteriorSource_range_mem z n hz

end Stacks.Chow
