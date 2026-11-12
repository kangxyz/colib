/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.ChosenLifting
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Families.GeneratorLift
public import Colib.AlgebraicGeometry.Correspondences.Support.TargetControl

/-!
# Chosen centers for genuine native signed prime family lifts

The actual finite clopen-piece lifting retains its chosen residue-lift values.
The native family construction retains all-point preimages in those pieces.
Combining them gives the exact designated center of every surviving branch
point over the original source point, with arbitrary integer multiplicity.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Points/ChosenGeneratorLift.lean`,
blob `e355c946bccac56ecbabccfae2c22538276575de`. The full lower family theorem
also retains closed-support factors; this endpoint exposes the center control
needed for arbitrary germ-tuple evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped BigOperators

universe u v

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme.SmoothSite.SmoothPointedEtaleNeighborhood

/-- Every signed native prime admits an actual finite family lift whose target
centers are the precise input residue-lift points, even at nonclosed points. -/
theorem exists_pointed_graph_family_factorization_at_chosen_points
    (k : Type u) [Field k] {X Y : Scheme.SmoothSite (Spec (.of k))}
    (a : pullback (C := Scheme) X.hom Y.hom)
    (ha : IsFiniteCorrespondencePoint X.hom Y.hom a) (c : ℤ) (x : X.left)
    {I : Type v} (V : I → Scheme.SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
    [∀ i, Etale (q i).left] (chosen : ∀ i, (V i).left)
    (hq : ∀ z : (integralComponentAt a).subscheme,
      ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) z = x →
      ∃ i : I, (q i).left (chosen i) =
        ((integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom) z ∧
        IsIso ((q i).left.residueFieldMap (chosen i))) :
    ∃ (N : Scheme.SmoothSite.SmoothPointedEtaleNeighborhood X x) (n : ℕ) (label : Fin n → I)
      (β : ∀ j, Cor.mk ((Scheme.SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶
        Cor.mk (V (label j))),
      (∑ j, β j ≫ (graphFunctor k).map (q (label j))) =
        (graphFunctor k).map N.toBase ≫ singleFiniteCorrespondence X.hom Y.hom a ha c ∧
      ∀ j, finiteCorrespondences.TargetsIn (β j) N.center {chosen (label j)} := by
  let p := (integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom
  let target := (integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom
  let : IsFinite p := ha.1
  let W (i : I) : Scheme := pullback target (q i).left
  let r (i : I) : W i ⟶ (integralComponentAt a).subscheme := pullback.fst target (q i).left
  let Q (i : I) (w : W i) : Prop := pullback.snd target (q i).left w = chosen i
  have : ∀ i, Etale (r i) := by intro i; dsimp [r, W]; infer_instance
  have : ∀ i, IsSeparated (r i) := by intro i; dsimp [r, W]; infer_instance
  have hr : ∀ z : (integralComponentAt a).subscheme, p z = x →
      ∃ (i : I) (w : W i), r i w = z ∧ IsIso ((r i).residueFieldMap w) ∧ Q i w := by
    intro z hz
    obtain ⟨i, hi, hres⟩ := hq z hz
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := target) (g := (q i).left) z (chosen i) hi.symm
    refine ⟨i, w, hw₁, ?_, hw₂⟩
    exact isIso_residueFieldMap_pullback_fst_of_right target (q i).left w
      (by rw [hw₂]; exact hres)
  obtain ⟨N, n, F, hF, _, htop, label, b₀, hb₀⟩ :=
    exists_family_lift_of_isFinite_with_point_property
      p W r Q hr
  let b (j : Fin n) : (F j).toScheme ⟶ (V (label j)).left :=
    b₀ j ≫ pullback.snd target (q (label j)).left
  have hb (j : Fin n) : b j ≫ (q (label j)).left =
      (F j).ι ≫ pullback.fst p N.toBase.left ≫ target := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, (hb₀ j).1]
    simp only [Category.assoc]
  obtain ⟨β, hβ, hpoints⟩ := exists_graph_family_factorization_with_fiber_lift_signed
    k a ha N.toBase V q n F (fun j => (hF j).1.1) htop label b hb c
  refine ⟨N, n, label, β, hβ, ?_⟩
  intro j B hB z hz
  obtain ⟨t, hts, htt⟩ := (hpoints j B hB).2 z
  obtain ⟨w, hw, hval⟩ := (hb₀ j).2
  have hbt : b j t = chosen (label j) := by
    change pullback.snd target (q (label j)).left (b₀ j t) = chosen (label j)
    rw [hval t (hts.trans hz)]
    exact hw
  exact htt.symm.trans hbt

end AlgebraicGeometry.Cor
