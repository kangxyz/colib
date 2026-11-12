/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.CompactifiedMoving
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.MovingEndpoints
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.OpenImage
public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.PrescribedBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Retained.MissingBoundary
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf

/-!
# Local vanishing on the original target of an étale presentation

Apply the moving construction to the retained target and its actual
pulled-back good open. The section vanishes on the image of the
resulting affine neighborhood in the original target.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Presentation/Local.lean`
and `Motivic/Cohomology/A1/LocalVanishing/Presentation/OriginalOpen.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, blobs
`00e9f23b2999ea16a168a9838626f858a7846067` and
`f303f48a27e18299b760ea4d8dfaa6b8f33e5758`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample

universe u v

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

/-- A presentation gives a literal affine zero neighborhood of its marked point
for an affine-line invariant presheaf with transfers. -/
theorem exists_zero_on_original_open
    {k : Type u} [Field k] {X A : SmoothSite (Spec (.of k))}
    [IsAffine X.left] {Y Z : Scheme.{u}}
    (p : Y ⟶ X.left) (a : A ⟶ X) [IsOpenImmersion a.left]
    (z : Z ⟶ X.left) [IsClosedImmersion z] (s : Z ⟶ Y) (x : X.left)
    (e : OriginalEtalePresentation k X.hom p a.left z s x)
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    ∃ O : X.left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0 := by
  let π := e.projectiveMap ≫ (projectiveSpaceOverRing 1 e.base ↘ Spec e.base)
  let : IsNoetherianRing e.base := e.base_noetherian
  let : IsAffine e.target := e.target_affine
  let : IsOpenImmersion e.refinement := e.refinement_open
  let : IsOpenImmersion e.inclusion := e.inclusion_open
  let : IsFinite e.projectiveMap := e.projective_finite
  let : IsProper π := by dsimp [π]; infer_instance
  let : SmoothOfRelativeDimension 1 (e.inclusion ≫ π) := e.target_smooth
  have hbase : (e.inclusion ≫ π) ≫ e.toField = e.refinement ≫ X.hom := by
    simpa only [π, Category.assoc] using e.base_compatibility.symm
  let : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsAffine X.left)
  let : IsAffineHom e.refinement := isAffineHom_of_isAffine e.refinement
  let : Smooth ((e.inclusion ≫ π) ≫ e.toField) := by
    rw [hbase]
    infer_instance
  let : IsSeparated ((e.inclusion ≫ π) ≫ e.toField) := by
    rw [hbase]
    infer_instance
  let : QuasiCompact ((e.inclusion ≫ π) ≫ e.toField) := by
    rw [hbase]
    infer_instance
  let T := SmoothSite.mk ((e.inclusion ≫ π) ≫ e.toField)
  let r : T ⟶ X := SmoothSite.homMk e.refinement hbase.symm
  let j := SmoothSite.etalePullbackSnd a r
  let b := SmoothSite.etalePullbackFst a r
  let : IsOpenImmersion j.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd a.left e.refinement))
  have hj : j ≫ r = b ≫ a := (SmoothSite.etalePullbackCone a r).condition.symm
  have hv' : P.transfer ((Cor.graphFunctor k).map j)
      (P.transfer ((Cor.graphFunctor k).map r) v) = 0 := by
    have he := ConcreteCategory.congr_hom
      (congrArg P.transfer (congrArg (Cor.graphFunctor k).map hj)) v
    simpa only [Functor.map_comp, PresheafWithTransfers.transfer_comp,
      ConcreteCategory.comp_apply, hv, map_zero] using he
  let : IsClosedImmersion e.closedInclusion :=
    MorphismProperty.of_isPullback e.closed_cartesian inferInstance
  let : IsFinite (e.closedInclusion ≫ e.inclusion ≫ π) := e.closed_finite
  let : IsFinite ((e.closedInclusion ≫ e.inclusion) ≫ π) := by
    rw [Category.assoc]
    infer_instance
  let : IsClosedImmersion (e.closedInclusion ≫ e.inclusion) :=
    prescribed_closed_in_compactification e.inclusion π e.closedInclusion
  let : IsFinite (e.missingInclusion ≫ π) := e.missing_finite
  have hd : Disjoint (Set.range e.inclusion) (Set.range e.missingInclusion) := by
    rw [e.missing_range]
    exact disjoint_compl_right
  have hT : ∀ c, c ∈ Set.range e.inclusion ∨ c ∈ Set.range e.missingInclusion := by
    intro c
    rw [e.missing_range]
    exact Classical.em _
  have hA : ∀ c, c ∈ Set.range (j.left ≫ e.inclusion) ∨
      c ∈ Set.range e.missingInclusion ∨ c ∈ Set.range (e.closedInclusion ≫ e.inclusion) := by
    intro c
    rcases hT c with ⟨y, rfl⟩ | hc
    · rcases e.punctured_cover y with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact Or.inl ⟨u, rfl⟩
      · exact Or.inr (Or.inr ⟨u, rfl⟩)
    · exact Or.inr (Or.inl hc)
  let L := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 1 (Spec e.base)
  let M := (Modules.pullback e.projectiveMap).obj L
  let : IsInvertibleModule e.compact M :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ e.projectiveMap L
      (Stacks.ProjectiveSpace.isInvertibleModule_projectiveSpaceTwistingSheaf 1 (Spec e.base))
  have hM : IsAmple e.compact M :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom e.projectiveMap L
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf 1 (Spec e.base))
  obtain ⟨O, hx, β, α, h₀, h₁⟩ := Cor.exists_affine_open_hasMovingEndpoints π
    e.inclusion e.toField j e.closedInclusion e.missingInclusion hd hT hA M hM e.point
  let : IsAffine O.1.toScheme := O.2
  let : IsAffineHom O.1.ι := isAffineHom_of_isAffine O.1.ι
  let o : SmoothSite.mk (O.1.ι ≫ T.hom) ⟶ T := SmoothSite.homMk O.1.ι rfl
  let f := o ≫ r
  let : IsAffine (SmoothSite.mk (O.1.ι ≫ T.hom)).left := O.2
  let : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (O.1.ι ≫ e.refinement))
  have hzero : P.transfer ((Cor.graphFunctor k).map f) v = 0 := by
    rw [Functor.map_comp, PresheafWithTransfers.transfer_comp]
    exact P.section_zero_of_moving_endpoints hP o j β α h₀ h₁
      (P.transfer ((Cor.graphFunctor k).map r) v) hv'
  exact ⟨f.left.opensRange, isAffineOpen_opensRange f.left,
    ⟨⟨e.point, hx⟩, e.point_eq⟩, P.zero_on_open_image_general f v hzero⟩

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
