/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.GeneratorLift
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteLifting
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap

/-!
# Pointed Nisnevich lifting of actual prime correspondences

For a single étale target morphism with residue-field-isomorphism lifts at all
points, the existing finite-support lifting theorem supplies an actual pointed
smooth-site neighborhood and a map on the entire scheme-theoretic pulled-back
support. The existing native correspondence support-lift theorem then gives the
actual graph factorization. The original incidence Tor coefficients and all
finite-image residue degrees are retained by that theorem.

The target cover is first pulled back to the actual integral support. The
residue-field condition on this pullback uses the native Stacks base-change
lemma. The scheme-theoretic support pullback is neither reduced nor assumed
flat. Arbitrary base fields and disconnected or empty ambient schemes are allowed.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/LocalGeneratorLift.lean`,
blob `2deb6aad63a30ba4674a2efebdcef85edb779b43`. The source's generator cycle is
replaced by the existing native `singleFiniteCorrespondence`, not a second model.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y V : Scheme.SmoothSite (Spec (.of k))}

/-- An actual admissible prime lifts through a single Nisnevich covering arrow
on a pointed smooth-site Nisnevich neighborhood of every source point. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/LocalGeneratorLift.lean: exists_nisnevich_graph_factorization"
  "adaptation" "whole scheme-theoretic finite support and the actual native graph factorization"]
theorem exists_nisnevich_graph_factorization_single
    (a : pullback (C := Scheme) X.hom Y.hom) (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
    (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v)) (x : X.left) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 := by
  let p := (integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom
  let t := (integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom
  let r : pullback t q.left ⟶ (integralComponentAt a).subscheme := pullback.fst t q.left
  let : IsFinite p := ha.1
  have : Etale r := by dsimp only [r]; infer_instance
  have : IsSeparated r := by dsimp only [r]; infer_instance
  have hr : ∀ z : (integralComponentAt a).subscheme, p z = x →
      ∃ v : (pullback t q.left : Scheme), r v = z ∧ IsIso (r.residueFieldMap v) := by
    intro z _
    obtain ⟨v, hv, hres⟩ := hq (t z)
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := t) (g := q.left) z v hv.symm
    refine ⟨w, hw₁, ?_⟩
    exact isIso_residueFieldMap_pullback_fst_of_right t q.left w (by
      rw [hw₂]
      exact hres)
  obtain ⟨U, g, hg, u, hu, hgu, b₀, hb₀⟩ :=
    Scheme.SmoothSite.exists_nisnevich_lift_of_isFinite X p x r hr
  let b : pullback p g.left ⟶ V.left := b₀ ≫ pullback.snd t q.left
  have hb : b ≫ q.left = pullback.fst p g.left ≫ t := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb₀]
  obtain ⟨β, hβ⟩ := exists_graph_factorization_of_support_lift k a ha g q b hb
  exact ⟨U, g, hg, u, hu, hgu, β, hβ⟩

/-- Every signed multiplicity of a native prime has the same pointed local lifting property. -/
theorem exists_nisnevich_graph_factorization_single_signed
    (a : pullback (C := Scheme) X.hom Y.hom) (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
    (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v)) (x : X.left) (n : ℤ) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha n := by
  obtain ⟨U, g, hg, u, hu, hgu, β, hβ⟩ :=
    exists_nisnevich_graph_factorization_single k a ha q hq x
  let γ : Cor.mk U ⟶ Cor.mk X := (graphFunctor k).map g
  let δ : Cor.mk V ⟶ Cor.mk Y := (graphFunctor k).map q
  change β ≫ δ = γ ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 at hβ
  refine ⟨U, g, hg, u, hu, hgu, n • β, ?_⟩
  change (n • β) ≫ δ = γ ≫ singleFiniteCorrespondence X.hom Y.hom a ha n
  rw [singleFiniteCorrespondence_eq_zsmul, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, hβ]

end AlgebraicGeometry.Cor
