/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.Monic.NeighborhoodLift
public import Colib.AlgebraicGeometry.Sites.Smooth.Injectives
public import Colib.CategoryTheory.Sites.Cohomology.LocalTriviality

/-! # Killing positive ordinary classes near the entire relative monic divisor -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Monic/NeighborhoodZero.lean`, blob
`5654a742d2335a01acb6075b60e5432a4b07b2dd`.
The source is the actual original scheme or ordinary free-Yoneda Ext group.
All monic quotient fibers retain their full scheme structure.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
universe w u
namespace AlgebraicGeometry.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
open _root_.Stacks.Cohomology.FreeYonedaUnivLE
open _root_.Algebra.Smooth _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- Every positive original ordinary cohomology class vanishes on an affine
étale neighborhood of the full monic divisor after one nonzero base localization. -/
theorem exists_relative_monic_neighborhood_restriction_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (f : R[X]) (hf : f.Monic)
    (e : (cohomologyPresheaf.{w, u + 1} F (n + 1)).obj (op (lineSite (k := k) (R := R)))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (Y : SmoothSite (Spec (.of k)))
      (p : Y ⟶ lineSite (k := k) (R := Localization.Away r)),
      IsAffine Y.left ∧ Etale p.left ∧
      IsIso (pullback.snd p.left (inclusion (f.map (algebraMap R (Localization.Away r))))) ∧
      (cohomologyPresheaf.{w, u + 1}
        F (n + 1)).map
          (p ≫ lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op e = 0 := by
  let X := lineSite (k := k) (R := R)
  let J := SmoothSite.nisnevichTopology (Spec (.of k))
  induction n generalizing F with
  | zero =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (((freeYoneda.{u + 1} J).obj X)) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨r, hr, Y, p, hY, hp, hZ, l, hl⟩ := exists_relative_monic_neighborhood_lift E.g f hf
      (extSectionsAddEquiv.{w, u + 1} X E.X₃ y)
    refine ⟨r, hr, Y, p, hY, hp, hZ, ?_⟩
    rw [← hy]
    exact boundary_restriction_eq_zero_of_imageSieve.{w, u + 1, u, u + 1} J hE y _ ⟨l, hl⟩
  | succ n ih =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (((freeYoneda.{u + 1} J).obj X)) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨r, hr, Y, p, hY, hp, hZ, hz⟩ := ih E.X₃ y
    let a := p ≫ lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))
    refine ⟨r, hr, Y, p, hY, hp, hZ, ?_⟩
    rw [← hy]
    change (Ext.mk₀ ((freeYoneda.{u + 1} J).map a)).comp
      (y.comp hE.extClass rfl) (zero_add (n + 1 + 1)) = 0
    rw [← Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl (by omega)]
    change ((cohomologyPresheaf.{w, u + 1} E.X₃ (n + 1)).map a.op y).comp hE.extClass rfl = 0
    rw [hz]
    exact Ext.zero_comp (((freeYoneda.{u + 1} J).obj Y)) (n + 1) hE.extClass _ rfl

end AlgebraicGeometry.SheafCohomology
