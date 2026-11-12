/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.CommSq
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

import Colib.CategoryTheory.Sites.FreeYonedaPushout
import Colib.CategoryTheory.Sites.RelativeCohomology.Monomorphisms

/-!
# The cohomology boundary of a smooth Nisnevich distinguished square

The free representing sheaves on a geometric distinguished square give the
short exact sequence with difference on the left and sum on the right.
The extension class gives the Mayer–Vietoris boundary for ordinary cohomology
with lifted coefficients. This uses the same sign convention as Mathlib's
`MayerVietorisSquare.δ` and applies to the native Stacks cohomology presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u t w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [HasSheafify (nisnevichTopology S) AddCommGrpCat.{max u t}]

/-- The native difference and sum complex of free representing sheaves on a square. -/
abbrev nisnevichFreeYonedaSquareComplex (sq : Square (SmoothSite S)) :
    ShortComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{max u t}) :=
  (sq.map (freeYoneda.{t} (nisnevichTopology S))).commSq.shortComplex

variable (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
  [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]

include hpb z hcomp

set_option backward.isDefEq.respectTransparency false in
/-- A geometric distinguished square has a short exact free representing sequence. -/
theorem nisnevichFreeYonedaSquareComplex_shortExact :
    (nisnevichFreeYonedaSquareComplex.{u, t} sq).ShortExact := by
  let J := nisnevichTopology S
  let Y := freeYoneda.{t} J
  have hp : IsPushout (Y.map sq.f₁₂) (Y.map sq.f₁₃) (Y.map sq.f₂₄) (Y.map sq.f₃₄) :=
    isPushout_map_freeYoneda J sq (fun F ↦ isPullback_op_map_of_iso_complement sq hpb z hcomp F)
  refine { exact := hp.exact_shortComplex, mono_f := ?_, epi_g := hp.epi_shortComplex_g }
  have : Mono sq.f₂₄ := (forgetScheme S).mono_of_mono_map (by
    change Mono sq.f₂₄.left
    infer_instance)
  have : Mono sq.f₁₃ := hpb.mono_f₁₃
  have : Mono (Y.map sq.f₁₃) := freeYoneda_map_mono J sq.f₁₃
  change Mono (biprod.lift (Y.map sq.f₁₂) (-(Y.map sq.f₁₃)))
  have : Mono (biprod.lift (Y.map sq.f₁₂) (-(Y.map sq.f₁₃)) ≫ biprod.snd) := by
    rw [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

variable [HasExt.{w} (Sheaf (nisnevichTopology S) AddCommGrpCat.{max u t})]

/-- The connecting map from the intersection to the base in the next degree. -/
def nisnevichCohomologyBoundary (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{max u t})
    (n : ℕ) :
    (cohomologyPresheaf.{w, t} F n).obj (op sq.X₁) ⟶
      (cohomologyPresheaf.{w, t} F (n + 1)).obj (op sq.X₄) :=
  AddCommGrpCat.ofHom
    ((nisnevichFreeYonedaSquareComplex_shortExact.{u, t} sq hpb z hcomp).extClass.precomp F
      (Nat.add_comm 1 n))

set_option backward.isDefEq.respectTransparency false in
/-- A cohomology class on the base that restricts to zero on both pieces
comes from the actual Mayer–Vietoris boundary. -/
theorem exists_nisnevichCohomologyBoundary_eq_of_restriction_zero
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ)
    (x : (cohomologyPresheaf.{w, t} F (n + 1)).obj (op sq.X₄))
    (h₂ : (cohomologyPresheaf.{w, t} F (n + 1)).map sq.f₂₄.op x = 0)
    (h₃ : (cohomologyPresheaf.{w, t} F (n + 1)).map sq.f₃₄.op x = 0) :
    ∃ y : (cohomologyPresheaf.{w, t} F n).obj (op sq.X₁),
      nisnevichCohomologyBoundary sq hpb z hcomp F n y = x := by
  let Y := freeYoneda.{t} (nisnevichTopology S)
  let Q := nisnevichFreeYonedaSquareComplex.{u, t} sq
  have hz : (Ext.mk₀ Q.g).comp x (zero_add (n + 1)) = 0 := by
    apply Ext.biprodAddEquiv.injective
    rw [map_zero]
    apply Prod.ext
    · change (Ext.mk₀ biprod.inl).comp
        ((Ext.mk₀ (biprod.desc (Y.map sq.f₂₄) (Y.map sq.f₃₄))).comp x
          (zero_add (n + 1))) (zero_add (n + 1)) = 0
      rw [Ext.mk₀_comp_mk₀_assoc, biprod.inl_desc]
      exact h₂
    · change (Ext.mk₀ biprod.inr).comp
        ((Ext.mk₀ (biprod.desc (Y.map sq.f₂₄) (Y.map sq.f₃₄))).comp x
          (zero_add (n + 1))) (zero_add (n + 1)) = 0
      rw [Ext.mk₀_comp_mk₀_assoc, biprod.inr_desc]
      exact h₃
  let hQ : Q.ShortExact := nisnevichFreeYonedaSquareComplex_shortExact.{u, t} sq hpb z hcomp
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hQ F x hz (Nat.add_comm 1 n)
  exact ⟨y, hy⟩

set_option backward.isDefEq.respectTransparency false in
/-- The connecting map commutes with restriction along a map of geometric
distinguished squares, in particular along an open refinement. -/
theorem nisnevichCohomologyBoundary_naturality
    (sq' : Square (SmoothSite S)) (hpb' : sq'.IsPullback)
    [IsOpenImmersion sq'.f₂₄.left] [Etale sq'.f₃₄.left]
    {Z' : Scheme.{u}} (z' : Z' ⟶ sq'.X₄.left) [IsClosedImmersion z']
    (hcomp' : Set.range z' = (Set.range sq'.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq'.f₃₄.left z')]
    (φ : sq ⟶ sq') (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ) :
    nisnevichCohomologyBoundary sq' hpb' z' hcomp' F n ≫
      (cohomologyPresheaf.{w, t} F (n + 1)).map φ.τ₄.op =
    (cohomologyPresheaf.{w, t} F n).map φ.τ₁.op ≫
      nisnevichCohomologyBoundary sq hpb z hcomp F n := by
  let Y := freeYoneda.{t} (nisnevichTopology S)
  let T := sq.map Y
  let T' := sq'.map Y
  let ψ : T ⟶ T' := Y.mapSquare.map φ
  let Q := nisnevichFreeYonedaSquareComplex.{u, t} sq
  let Q' := nisnevichFreeYonedaSquareComplex.{u, t} sq'
  let hQ : Q.ShortExact := nisnevichFreeYonedaSquareComplex_shortExact.{u, t} sq hpb z hcomp
  let hQ' : Q'.ShortExact := nisnevichFreeYonedaSquareComplex_shortExact.{u, t} sq' hpb' z' hcomp'
  let τ : Q ⟶ Q' := {
    τ₁ := ψ.τ₁
    τ₂ := biprod.map ψ.τ₂ ψ.τ₃
    τ₃ := ψ.τ₄
    comm₁₂ := by
      symm
      change biprod.lift T.f₁₂ (-T.f₁₃) ≫ biprod.map ψ.τ₂ ψ.τ₃ =
        ψ.τ₁ ≫ biprod.lift T'.f₁₂ (-T'.f₁₃)
      apply biprod.hom_ext <;> simp [ψ.comm₁₂, ψ.comm₁₃]
    comm₂₃ := by
      change biprod.map ψ.τ₂ ψ.τ₃ ≫ biprod.desc T'.f₂₄ T'.f₃₄ =
        biprod.desc T.f₂₄ T.f₃₄ ≫ ψ.τ₄
      apply biprod.hom_ext' <;> simp [ψ.comm₂₄, ψ.comm₃₄] }
  ext x
  change (Ext.mk₀ τ.τ₃).comp (hQ'.extClass.comp x (Nat.add_comm 1 n)) (zero_add (n + 1)) =
    hQ.extClass.comp ((Ext.mk₀ τ.τ₁).comp x (zero_add n)) (Nat.add_comm 1 n)
  rw [← Ext.comp_assoc (Ext.mk₀ τ.τ₃) hQ'.extClass x (zero_add 1) (Nat.add_comm 1 n) (by omega),
    ← hQ.extClass_naturality hQ' τ, Ext.comp_assoc_of_second_deg_zero]

end AlgebraicGeometry.Scheme.SmoothSite
