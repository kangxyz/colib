/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Points.CommonSupportCoverage
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Points.ControlledCechKernel
public import Colib.AlgebraicGeometry.Correspondences.Support.TargetControl
public import Colib.AlgebraicGeometry.Correspondences.Additive

/-!
# A controlled signed Cech boundary with its common support constructed

The finite common image and its point coverage are constructed from the
original nonzero support. The displayed residue-isomorphic target centers
then supply the actual chosen lifts. The zero cycle is handled by the zero
boundary on the identity neighborhood; no nonempty support premise is added.

Source: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Sheaf/Germs/Cech/AutomaticSupport.lean`,
blob `7ddf39a231b42e6c99f735e432e45091c4f20dd8`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

/-- A native signed kernel relation supported at designated target centers is
an actual pointed Cech boundary whose two target coordinates retain those centers. -/
theorem exists_pointed_cech_boundary_with_target_control
    (k : Type u) [Field k] {X Y V : Scheme.SmoothSite (Spec (.of k))}
    (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hzero : α ≫ (graphFunctor k).map q = 0)
    (x : X.left) (T : Set V.left)
    (hfirst : finiteCorrespondences.TargetsIn α x T)
    (hres : ∀ v ∈ T, IsIso (q.left.residueFieldMap v)) :
    ∃ (N : Scheme.SmoothSite.SmoothPointedEtaleNeighborhood X x)
      (β : Cor.mk ((Scheme.SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (Scheme.SmoothSite.etalePullback q q)),
      (graphFunctor k).map N.toBase ≫ α =
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
          β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) ∧
      finiteCorrespondences.TargetsIn β N.center
        {w | (Scheme.SmoothSite.etalePullbackFst q q).left w ∈ T ∧
          (Scheme.SmoothSite.etalePullbackSnd q q).left w ∈ T} := by
  classical
  by_cases hs : α.property.1.toFinset.Nonempty
  · obtain ⟨C, j, hj, hp, hr, hcover⟩ := exists_common_finite_image_with_coverage k α q hs
    let := hj
    let := hp
    choose r hr using hr
    have hq : ∀ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x →
        ∃ v : V.left, q.left v = (j ≫ pullback.snd X.hom Y.hom) z ∧
          IsIso (q.left.residueFieldMap v) ∧ v ∈ T := by
      intro z hz
      obtain ⟨a, w, ha⟩ := hcover z
      have hax : ((integralComponentAt a.val).subschemeι ≫ pullback.fst X.hom V.hom) w = x := by
        have he := congrArg (pullback.fst X.hom Y.hom) ha
        have hf := congrArg (fun e : (integralComponentAt a.val).subscheme ⟶ X.left => e w)
          (correspondenceGraphPostcompositionMap_fst X.hom V.hom Y.hom q.left
            (MorphismProperty.Over.w q) a.val)
        exact hf.symm.trans (he.symm.trans hz)
      have hat : ((integralComponentAt a.val).subschemeι ≫ pullback.snd X.hom V.hom) w ∈ T := by
        apply hfirst a.val ?_ w hax
        simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using a.property
      refine ⟨((integralComponentAt a.val).subschemeι ≫ pullback.snd X.hom V.hom) w,
        ?_, hres _ hat, hat⟩
      have he := congrArg (pullback.snd X.hom Y.hom) ha
      have hf := congrArg (fun e : (integralComponentAt a.val).subscheme ⟶ Y.left => e w)
        (correspondenceGraphPostcompositionMap_snd X.hom V.hom Y.hom q.left
          (MorphismProperty.Over.w q) a.val)
      exact hf.symm.trans he.symm
    obtain ⟨N, β, hβ, hpoints⟩ := exists_pointed_cech_boundary_with_point_property
      k α q hzero C j r hr x (fun v => v ∈ T) hq
    refine ⟨N, β, hβ, ?_⟩
    intro v hv z hz
    obtain ⟨a, w, has, hat, hsecond⟩ := hpoints v hv z hz
    refine ⟨?_, hsecond⟩
    have hne : α.val a.val ≠ 0 := by
      simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using a.property
    exact hat ▸ hfirst a.val hne w has
  · have hα : α = 0 := by
      apply Subtype.ext
      apply Function.locallyFinsuppWithin.ext
      intro a
      by_contra ha
      exact hs ⟨a, α.property.1.mem_toFinset.mpr ha⟩
    let N : Scheme.SmoothSite.SmoothPointedEtaleNeighborhood X x :=
      Scheme.SmoothSite.SmoothPointedEtaleNeighborhood.ofResidueFieldIso (𝟙 X) x (by simp)
    refine ⟨N, 0, ?_, finiteCorrespondences.TargetsIn.zero⟩
    let M := Cor.mk ((X.nisnevichNeighborhoodFunctor x).obj N)
    let W := Cor.mk (Scheme.SmoothSite.etalePullback q q)
    let g : M ⟶ Cor.mk X := (graphFunctor k).map N.toBase
    let a : W ⟶ Cor.mk V := (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q)
    let b : W ⟶ Cor.mk V := (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)
    change g ≫ α = (0 : M ⟶ W) ≫ a - (0 : M ⟶ W) ≫ b
    rw [hα, comp_zero, zero_comp, zero_comp, sub_zero]

end AlgebraicGeometry.Cor
