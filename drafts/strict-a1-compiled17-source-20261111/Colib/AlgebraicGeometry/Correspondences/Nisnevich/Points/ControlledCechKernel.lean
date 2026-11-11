/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.ControlledLifting
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.LocalPointControl

/-!
# A native signed Cech boundary with chosen-point control

Lift the whole finite common support while preserving the property of the
actual chosen residue lifts. The existing native signed contraction retains
all actual support-point preimages, so its second target has the chosen
property and its first target comes from the original support.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Points/ControlledCechKernel.lean`,
blob `a91284832520c67b65eac75c556601e81c9f2937`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

/-- A signed relation has a pointed genuine Cech boundary whose source-fiber
points retain both the original branch point and the chosen second-target property. -/
theorem exists_pointed_cech_boundary_with_point_property
    (k : Type u) [Field k] {X Y V : Scheme.SmoothSite (Spec (.of k))}
    (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hzero : α ≫ (graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ a ∈ α.val.support, (integralComponentAt a).subscheme ⟶ C)
    (hr : ∀ a ha, r a ha ≫ j = correspondenceGraphPostcompositionMap
      X.hom V.hom Y.hom q.left (MorphismProperty.Over.w q) a)
    (x : X.left) (Q : V.left → Prop)
    (hq : ∀ z : C, (j ≫ pullback.fst X.hom Y.hom) z = x →
      ∃ v : V.left, q.left v = (j ≫ pullback.snd X.hom Y.hom) z ∧
        IsIso (q.left.residueFieldMap v) ∧ Q v) :
    ∃ (N : Scheme.SmoothSite.NisnevichNeighborhood X x)
      (β : Cor.mk ((Scheme.SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (Scheme.SmoothSite.etalePullback q q)),
      (graphFunctor k).map N.toBase ≫ α =
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
          β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme,
        ((integralComponentAt v).subschemeι ≫
          pullback.fst ((Scheme.SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom
            (Scheme.SmoothSite.etalePullback q q).hom) z = N.center →
        ∃ a : α.property.1.toFinset, ∃ w : (integralComponentAt a.val).subscheme,
          ((integralComponentAt a.val).subschemeι ≫ pullback.fst X.hom V.hom) w = x ∧
          ((integralComponentAt a.val).subschemeι ≫ pullback.snd X.hom V.hom) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd ((Scheme.SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom
                (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackFst q q).left) z ∧
          Q (((integralComponentAt v).subschemeι ≫
              pullback.snd ((Scheme.SmoothSite.nisnevichNeighborhoodFunctor X x).obj N).hom
                (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackSnd q q).left) z) := by
  let p : C ⟶ X.left := j ≫ pullback.fst X.hom Y.hom
  let target : C ⟶ Y.left := j ≫ pullback.snd X.hom Y.hom
  let l : pullback target q.left ⟶ C := pullback.fst target q.left
  have : Etale l := by dsimp [l]; infer_instance
  have : IsSeparated l := by dsimp [l]; infer_instance
  have hl : ∀ z : C, p z = x → ∃ w : (pullback target q.left : Scheme),
      l w = z ∧ IsIso (l.residueFieldMap w) ∧ Q (pullback.snd target q.left w) := by
    intro z hz
    obtain ⟨v, hv, hres, hQ⟩ := hq z hz
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := target) (g := q.left) z v hv.symm
    refine ⟨w, hw₁, ?_, hw₂.symm ▸ hQ⟩
    exact isIso_residueFieldMap_pullback_fst_of_right target q.left w
      (by rw [hw₂]; exact hres)
  obtain ⟨N, b₀, hb₀, hpoint⟩ :=
    Scheme.SmoothSite.NisnevichNeighborhood.exists_lift_of_isFinite_with_point_property
      p l (fun w => Q (pullback.snd target q.left w)) hl
  let b : pullback p N.toBase.left ⟶ V.left := b₀ ≫ pullback.snd target q.left
  have hb : b ≫ q.left = pullback.fst p N.toBase.left ≫ target := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb₀]
  obtain ⟨β, hβ, hpoints⟩ := exists_cech_boundary_of_common_support_lift_with_point_lift
    k α q hzero C j r hr N.toBase b hb
  refine ⟨N, β, hβ, ?_⟩
  intro v hv z hz
  obtain ⟨a, w, d, has, hat, hds, hdt⟩ := hpoints v hv z
  refine ⟨a, w, ?_, hat, ?_⟩
  · rw [hz, N.toBase_center] at has
    exact has
  · rw [← hdt]
    exact hpoint d (hds.trans hz)

end AlgebraicGeometry.Cor
