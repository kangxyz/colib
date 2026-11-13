/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FreeOnAffineOpen

/-!
# The finite locally free norm on actual global sections

The native determinant norm commutes with base change on global sections.
The compatible free affine charts are chosen in the actual open, and the
section module is that of the original composed pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme

/-- Global sections of the actual determinant norm. -/
abbrev normTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFiniteLocallyFree f] :
    Γ(X, ⊤) →* Γ(Y, ⊤) :=
  (Stacks.Norm.finiteLocallyFreeNorm f).app ⊤

/-- The norm on global sections commutes with the original pullback square. -/
theorem normTop_appTop_of_isPullback {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
    [IsFiniteLocallyFree f] [IsFiniteLocallyFree f'] (H : IsPullback g' f' f g)
    (s : Γ(X, ⊤)) : normTop f' (g'.appTop s) = g.appTop (normTop f s) := by
  change (Stacks.Norm.finiteLocallyFreeNorm f').app ⊤ (g'.appTop s) =
    g.appTop ((Stacks.Norm.finiteLocallyFreeNorm f).app ⊤ s)
  rw [Stacks.Norm.finiteLocallyFreeNorm_app f' ⊤, Stacks.Norm.finiteLocallyFreeNorm_app f ⊤]
  have h := Stacks.Norm.normApp_baseChange f f' g' g H ⊤ s
  change Stacks.Norm.normApp f' ⊤ (g'.appLE ⊤ ⊤ (by simp) s) =
    g.appTop (Stacks.Norm.normApp f ⊤ s) at h
  have hg' : g'.appLE ⊤ ⊤ (by simp) = g'.appTop := Hom.appLE_eq_app g'
  rwa [hg'] at h

/-- The same norm is the determinant on the actual finite free affine chart. -/
theorem normTop_eq_affineNorm {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFree f] [IsAffine Y] (s : Γ(X, ⊤)) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(Y, ⊤) Γ(X, ⊤)], normTop f s = Algebra.norm Γ(Y, ⊤) s := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : IsFinite f := IsFiniteLocallyFree.isFinite f
  intro h
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  exact (Stacks.Norm.finiteLocallyFreeNorm_app_affine f U s).trans
    ((Stacks.Norm.normApp_affine f U s).trans
      (Stacks.Norm.affineLocalNorm_eq_norm_of_free f U h f.finite_appTop s))

/-- Free affine charts of an actual open restrict the original finite morphism
through the composed open immersion. -/
theorem exists_freeAffineNormChart {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFree f] (U : Y.Opens) (x : U.toScheme) :
    ∃ V : U.toScheme.Opens, IsAffineOpen V ∧ x ∈ V ∧
      let q := pullback.snd f (V.ι ≫ U.ι)
      letI : Algebra Γ(V.toScheme, ⊤) Γ(pullback f (V.ι ≫ U.ι), ⊤) :=
        q.appTop.hom.toAlgebra
      Module.Free Γ(V.toScheme, ⊤) Γ(pullback f (V.ι ≫ U.ι), ⊤) := by
  let g := pullback.snd f U.ι
  let : IsFiniteLocallyFree g :=
    isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f U.ι) inferInstance
  obtain ⟨V, hV, hxV, _, hfree⟩ := exists_isAffineOpen_module_finite_and_free g x
  refine ⟨V, hV, hxV, ?_⟩
  let q := pullback.snd f (V.ι ≫ U.ι)
  let q' := pullback.fst V.ι g
  let : Algebra Γ(V.toScheme, ⊤) Γ(pullback f (V.ι ≫ U.ι), ⊤) :=
    q.appTop.hom.toAlgebra
  let : Algebra Γ(V.toScheme, ⊤) Γ(pullback V.ι g, ⊤) := q'.appTop.hom.toAlgebra
  let : Module.Free Γ(V.toScheme, ⊤) Γ(pullback V.ι g, ⊤) := hfree
  let e := (pullbackLeftPullbackSndIso f U.ι V.ι).symm ≪≫ pullbackSymmetry g V.ι
  have he : e.hom ≫ q' = q := by
    simp only [e, q', Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSymmetry_hom_comp_fst]
    exact pullbackLeftPullbackSndIso_inv_snd_snd f U.ι V.ι
  let E : Γ(pullback V.ι g, ⊤) ≃ₐ[Γ(V.toScheme, ⊤)] Γ(pullback f (V.ι ≫ U.ι), ⊤) :=
    { (asIso e.hom.appTop).commRingCatIsoToRingEquiv with
      commutes' := fun a ↦ by
        change (q'.appTop ≫ e.hom.appTop) a = q.appTop a
        rw [← Hom.comp_appTop, he] }
  exact Module.Free.of_equiv E.toLinearEquiv

end AlgebraicGeometry.Scheme
