/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Original integral clopen components and their radicial inverse images

Every original smooth object over a field has a finite partition by its integral clopen
component subschemes. Pulling that partition back along a universal homeomorphism gives
integral original smooth-site objects, with the actual pullback projections and square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- An actual irreducible component, bundled in the original smooth site. -/
def integralComponent (X : SmoothSite (Spec (.of k)))
    (Z : irreducibleComponents X.left) : SmoothSite (Spec (.of k)) :=
  mk ((componentOpen k X Z.val Z.property).ι ≫ X.hom)

/-- The original clopen component inclusion. -/
def integralComponentι (X : SmoothSite (Spec (.of k)))
    (Z : irreducibleComponents X.left) : integralComponent k X Z ⟶ X :=
  homMk (componentOpen k X Z.val Z.property).ι rfl

instance (X : SmoothSite (Spec (.of k))) (Z : irreducibleComponents X.left) :
    IsIntegral (integralComponent k X Z).left :=
  isIntegral_componentOpen k X Z.val Z.property

instance (X : SmoothSite (Spec (.of k))) (Z : irreducibleComponents X.left) :
    IsOpenImmersion (integralComponentι k X Z).left :=
  inferInstanceAs (IsOpenImmersion (componentOpen k X Z.val Z.property).ι)

@[simp]
theorem range_integralComponentι (X : SmoothSite (Spec (.of k)))
    (Z : irreducibleComponents X.left) :
    Set.range (integralComponentι k X Z).left = Z.val :=
  (componentOpen k X Z.val Z.property).range_ι

instance (X : SmoothSite (Spec (.of k))) (Z : irreducibleComponents X.left) :
    IsClosedImmersion (integralComponentι k X Z).left :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [range_integralComponentι]
    exact (isClopen_irreducibleComponent k X Z.property).isClosed)

/-- The component inclusions are pairwise disjoint on actual points. -/
theorem pairwiseDisjoint_integralComponentι (X : SmoothSite (Spec (.of k))) :
    Pairwise fun Z Z' => Disjoint (Set.range (integralComponentι k X Z).left)
      (Set.range (integralComponentι k X Z').left) := by
  intro Z Z' h
  simp only [range_integralComponentι]
  exact pairwiseDisjoint_irreducibleComponents k X Z.property Z'.property
    (fun e => h (Subtype.ext e))

/-- The original component inclusions cover all points. -/
theorem integralComponentι_covers (X : SmoothSite (Spec (.of k))) (x : X.left) :
    ∃ Z, x ∈ Set.range (integralComponentι k X Z).left := by
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  rw [range_integralComponentι]
  exact mem_irreducibleComponent

/-- A smooth source mapping homeomorphically to an integral target is integral. -/
theorem isIntegral_of_universalHomeomorphism
    {X Y : SmoothSite (Spec (.of k))} (q : X ⟶ Y)
    [UniversalHomeomorphism q.left] [IsIntegral Y.left] : IsIntegral X.left := by
  have : IsReduced X.left := isReduced_of_smooth_of_isAffine (Y := Spec (.of k)) X.hom
  have hq : UniversalHomeomorphism q.left := inferInstance
  have hhomeo : IsHomeomorph q.left :=
    hq.universally_isHomeomorph
      _ _ _ IsPullback.of_id_snd
  have : IrreducibleSpace X.left :=
    (IsHomeomorph.homeomorph q.left hhomeo).irreducibleSpace_iff.mpr inferInstance
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

variable {X Y : SmoothSite (Spec (.of k))} (q : X ⟶ Y)

/-- The actual inverse image of a target component, in the original smooth site. -/
def integralComponentPullback (Z : irreducibleComponents Y.left) :
    SmoothSite (Spec (.of k)) :=
  etalePullback (integralComponentι k Y Z) q

/-- Its original clopen inclusion into the source. -/
def integralComponentPullbackι (Z : irreducibleComponents Y.left) :
    integralComponentPullback k q Z ⟶ X :=
  etalePullbackSnd (integralComponentι k Y Z) q

/-- The actual base change of the given morphism to the target component. -/
def integralComponentMap (Z : irreducibleComponents Y.left) :
    integralComponentPullback k q Z ⟶ integralComponent k Y Z :=
  etalePullbackFst (integralComponentι k Y Z) q

instance (Z : irreducibleComponents Y.left) :
    IsOpenImmersion (integralComponentPullbackι k q Z).left :=
  inferInstanceAs (IsOpenImmersion (pullback.snd (integralComponentι k Y Z).left q.left))

instance (Z : irreducibleComponents Y.left) :
    IsClosedImmersion (integralComponentPullbackι k q Z).left :=
  inferInstanceAs (IsClosedImmersion (pullback.snd (integralComponentι k Y Z).left q.left))

instance (Z : irreducibleComponents Y.left) [IsFinite q.left] :
    IsFinite (integralComponentMap k q Z).left :=
  inferInstanceAs (IsFinite (pullback.fst (integralComponentι k Y Z).left q.left))

instance (Z : irreducibleComponents Y.left) [Flat q.left] :
    Flat (integralComponentMap k q Z).left :=
  inferInstanceAs (Flat (pullback.fst (integralComponentι k Y Z).left q.left))

instance (Z : irreducibleComponents Y.left) [UniversalHomeomorphism q.left] :
    UniversalHomeomorphism (integralComponentMap k q Z).left := by
  obtain ⟨hi, hr, hs⟩ := (universalHomeomorphism_iff_integral_universallyInjective_surjective
    q.left).mp inferInstance
  change UniversalHomeomorphism (pullback.fst (integralComponentι k Y Z).left q.left)
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
    ⟨inferInstance, MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @UniversallyInjective) (IsPullback.of_hasPullback _ _).flip hr, inferInstance⟩

instance (Z : irreducibleComponents Y.left) [UniversalHomeomorphism q.left] :
    UniversallyInjective (integralComponentMap k q Z).left :=
  ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
    (inferInstance : UniversalHomeomorphism (integralComponentMap k q Z).left)).2.1

instance (Z : irreducibleComponents Y.left) [UniversalHomeomorphism q.left] :
    IsIntegral (integralComponentPullback k q Z).left :=
  isIntegral_of_universalHomeomorphism k (integralComponentMap k q Z)

/-- The displayed maps satisfy the original scheme pullback square. -/
theorem integralComponentMap_comm (Z : irreducibleComponents Y.left) :
    integralComponentMap k q Z ≫ integralComponentι k Y Z =
      integralComponentPullbackι k q Z ≫ q := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.condition

/-- The component inverse image retains exactly the preimage of the original component. -/
theorem range_integralComponentPullbackι (Z : irreducibleComponents Y.left) :
    Set.range (integralComponentPullbackι k q Z).left = q.left ⁻¹' Z.val := by
  change Set.range (pullback.snd (integralComponentι k Y Z).left q.left) = _
  rw [Scheme.Pullback.range_snd, range_integralComponentι]

/-- The source component inverse images are disjoint, on the actual source points. -/
theorem pairwiseDisjoint_integralComponentPullbackι :
    Pairwise fun Z Z' => Disjoint (Set.range (integralComponentPullbackι k q Z).left)
      (Set.range (integralComponentPullbackι k q Z').left) := by
  intro Z Z' h
  simp only [range_integralComponentPullbackι]
  exact (pairwiseDisjoint_irreducibleComponents k Y Z.property Z'.property
    (fun e => h (Subtype.ext e))).preimage q.left

/-- The source component inverse images cover every actual source point. -/
theorem integralComponentPullbackι_covers (x : X.left) :
    ∃ Z, x ∈ Set.range (integralComponentPullbackι k q Z).left := by
  obtain ⟨Z, hZ⟩ := integralComponentι_covers k Y (q.left x)
  refine ⟨Z, ?_⟩
  rw [range_integralComponentPullbackι]
  simpa only [range_integralComponentι, Set.mem_preimage] using hZ

end AlgebraicGeometry.Scheme.SmoothSite
