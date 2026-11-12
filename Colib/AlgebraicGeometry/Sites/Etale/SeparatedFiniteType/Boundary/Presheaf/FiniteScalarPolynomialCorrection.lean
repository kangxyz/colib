/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.Restriction
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.FiniteScalarBoundaryDescent
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.PolynomialTorusLifting
public import Colib.AlgebraicGeometry.Sites.Smooth.Presentations.ScalarPolynomialOverlap

/-!
# Transport of a whole polynomial correction to a scalar extension

The original polynomial torus square and its signed coefficient relation
become the actual scalar correction. The coefficient and ambient maps use
the canonical tensor-spectrum and scalar overlap comparisons.

Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/FinitePolynomialImage.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `ce22a1b5db4fcfe761f9e3150b18cc475d20f1bc`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance {R L : Type u} [CommRing R] [Field L] [Algebra k R] [Algebra k L]
    [Algebra.Smooth k R] : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

/-- Transport the whole marked polynomial correction to the actual scalar base change. -/
theorem exists_producedScalarCorrection_of_polynomial_lifting
    (P : PresheafWithTransfers.{u + 1} k)
    (R L : Type u) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [Field L] [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L]
    {Y D A : SmoothSite (Spec (.of k))}
    (p : Y ⟶ SmoothSite.lineSite (k := k) (R := R)) [Etale p.left]
    (z₀ : SmoothSite.affineSite k R ⟶ Y)
    (w : Spec (.of R)) (wL : Spec (.of (R ⊗[k] L)))
    (hu : ∀ v : Spec (.of (R ⊗[k] L)),
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L))) v = w → v = wL)
    (δ : D ⟶ A) (e₀ : Y ⟶ A)
    (τ : SmoothSite.etalePullback p
      (polynomialPunctureInclusion (k := k) (R := R)) ⟶ D)
    (hτ : τ ≫ δ = SmoothSite.etalePullbackFst p
      (polynomialPunctureInclusion (k := k) (R := R)) ≫ e₀)
    (s : sections P (Cor.mk D))
    (hpL : Etale ((SmoothSite.fieldBaseChange (algebraMap k L)).map p ≫
      (scalarLineIso k R L).hom).left)
    (hLift : letI := hpL
      HasAffinePolynomialTorusLifting (R ⊗[k] L)
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map p ≫ (scalarLineIso k R L).hom) wL
        (finiteSeparableExtension L P) ((SmoothSite.affineScalarIso k R L).inv ≫
          (SmoothSite.fieldBaseChange (algebraMap k L)).map z₀).left) :
    Nonempty (ProducedScalarCorrection P L w (p ≫ lineCylinderIso.hom) z₀ δ e₀ s) := by
  let F := SmoothSite.fieldBaseChange (algebraMap k L)
  let pL := F.map p ≫ (scalarLineIso k R L).hom
  let : Etale pL.left := hpL
  let V := SmoothSite.affineSite k R
  obtain ⟨B, v, _hB, hv, hwB, E, η, q, ζ, hE, hη, _hq, hbase, hζq, hζη,
      O, α, β, φ, H, hφ, hL⟩ := hLift
  let : IsOpenImmersion v.left := hv
  let : IsIso (SmoothSite.affineScalarIso k R L).inv.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme (Spec (.of L))).mapIso
      (SmoothSite.affineScalarIso k R L)).inv)
  let i := v ≫ (SmoothSite.affineScalarIso k R L).inv
  have hi : IsOpenImmersion i.left := inferInstanceAs
    (IsOpenImmersion (v.left ≫ (SmoothSite.affineScalarIso k R L).inv.left))
  have hfiber : (SmoothSite.finiteScalarProjection (E := L) V).left ⁻¹' {w} ⊆
      Set.range i.left := by
    intro y hy
    obtain ⟨b, hb⟩ := hwB
    have hy' : Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L)))
        ((SmoothSite.affineScalarIso k R L).hom.left y) = w := by
      have he := congrArg (fun f => f y) (SmoothSite.affineScalarIso_hom_original k R L)
      exact he.trans hy
    have he := hu _ hy'
    refine ⟨b, ?_⟩
    change (SmoothSite.affineScalarIso k R L).inv.left (v.left b) = y
    rw [hb, ← he]
    exact congrArg (fun f => f y)
      (((SmoothSite.forgetScheme (Spec (.of L))).mapIso
        (SmoothSite.affineScalarIso k R L)).hom_inv_id)
  let ζs : B ⟶ E := SmoothSite.homMk ζ (by
    rw [← MorphismProperty.Over.w q, ← Category.assoc, hζq]
    exact MorphismProperty.Over.w (SmoothSite.Contraction.nativeAffineSection (.of L) B 0))
  have hmark : ζs ≫ η = i ≫ F.map z₀ := by
    apply MorphismProperty.Over.Hom.ext
    exact hζη
  let : IsIso (SmoothSite.Contraction.affineLineCylinder.map (SmoothSite.affineScalarIso k R
    L).hom) :=
    inferInstanceAs (IsIso (cylinderIso (SmoothSite.affineScalarIso k R L)).hom)
  have hbase' : η ≫ F.map (p ≫ lineCylinderIso.hom) ≫
      (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom = q ≫
        SmoothSite.Contraction.affineLineCylinder.map i := by
    apply (cancel_mono (SmoothSite.Contraction.affineLineCylinder.map
      (SmoothSite.affineScalarIso k R L).hom)).mp
    calc
      _ = η ≫ pL ≫ (lineCylinderIso (k := L) (R := R ⊗[k] L)).hom := by
        simp only [pL, scalarLineIso, Iso.trans_hom, Iso.symm_hom,
          Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.inv_hom_id,
          Category.comp_id, cylinderIso, F, V]
      _ = q ≫ SmoothSite.Contraction.affineLineCylinder.map v := hbase
      _ = (q ≫ SmoothSite.Contraction.affineLineCylinder.map i) ≫
          SmoothSite.Contraction.affineLineCylinder.map (SmoothSite.affineScalarIso k R L).hom := by
        simp only [i, Functor.map_comp, Category.assoc]
        rw [← Functor.map_comp, Iso.inv_hom_id,
          (SmoothSite.Contraction.affineLineCylinder (S := Spec (.of L))).map_id, Category.comp_id]
  let τL := scalarPolynomialOverlapMap k R L p ≫ F.map τ
  let ψ := φ ≫ τL
  have hOverlap : scalarPolynomialOverlapMap k R L p ≫
      F.map (SmoothSite.etalePullbackFst p (polynomialPunctureInclusion (k := k) (R := R))) =
        SmoothSite.etalePullbackFst pL (polynomialPunctureInclusion (k := L) (R := R ⊗[k] L)) :=
    scalarPolynomialOverlapMap_fst k R L p
  have hψ : ψ ≫ F.map δ = α ≫ η ≫ F.map e₀ := by
    dsimp only [ψ, τL]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, hτ, Functor.map_comp,
      ← Category.assoc (scalarPolynomialOverlapMap k R L p), hOverlap,
      ← Category.assoc φ, hφ, Category.assoc]
  obtain ⟨a, c, hac⟩ := (HasRestrictionDifferenceLifting.restrict
    (finiteSeparableExtension L P) hL τL)
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)
  exact ⟨{
    B := B
    i := i
    open_i := hi
    fiber := hfiber
    E := E
    affine_E := hE
    η := η
    etale_η := hη
    q := q
    base_eq := hbase'
    ζ := ζs
    mark_eq := hmark
    O := O
    α := α
    β := β
    square := H
    φ := ψ
    ambient_eq := hψ
    a := a
    c := c
    relation := hac }⟩

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
