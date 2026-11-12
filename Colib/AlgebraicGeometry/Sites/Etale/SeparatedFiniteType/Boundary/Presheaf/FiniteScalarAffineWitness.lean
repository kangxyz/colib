/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarAffineCorrectionRestriction
public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange.FieldBaseChangeA1

/-!
# Scalar affine corrections on the original refinement

The correction over a finite separable scalar extension restricts to the
actual affine pullback. The lifted mark, torus section, ambient section,
and signed relation use the original coefficient maps.

Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/FinitePolynomialImage.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `ce22a1b5db4fcfe761f9e3150b18cc475d20f1bc`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.PresheafWithTransfers

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf

open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The actual affine scalar correction and its marked section equation. -/
structure ScalarAffineWitness
    (P : PresheafWithTransfers.{u + 1} k) (L : Type u) [Field L] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    {V Y D : SmoothSite (Spec (.of k))}
    (q : Y ⟶ SmoothSite.Contraction.affineLineCylinder.obj V) [Etale q.left] (z : V ⟶ Y)
    (φ : SmoothSite.etalePullback q (SmoothSite.Contraction.openInclusion.app V) ⟶ D)
    (s : sections P (Cor.mk D)) where
  E : SmoothSite (Spec (.of L))
  affine : IsAffine E.left
  f : E ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj Y
  etale : Etale f.left
  mark : (SmoothSite.fieldBaseChange (algebraMap k L)).obj V ⟶ E
  mark_eq : mark ≫ f = (SmoothSite.fieldBaseChange (algebraMap k L)).map z
  laurentSection : sections (finiteSeparableExtension L P)
    (Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k L)).obj
      (SmoothSite.Contraction.torusCylinder.obj V)))
  ambientSection : sections (finiteSeparableExtension L P) (Cor.mk E)
  relation :
    letI := etale
    let F := SmoothSite.fieldBaseChange (algebraMap k L)
    let α := SmoothSite.etalePullbackFst q (SmoothSite.Contraction.openInclusion.app V)
    let β := SmoothSite.etalePullbackSnd q (SmoothSite.Contraction.openInclusion.app V)
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (SmoothSite.etalePullbackSnd f (F.map α) ≫ F.map β)) laurentSection -
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (SmoothSite.etalePullbackFst f (F.map α))) ambientSection =
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (SmoothSite.etalePullbackSnd f (F.map α) ≫ F.map φ))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)

/-- Restrict the two scalar coefficient sections to the original affine refinement. -/
theorem restrictScalarAffineWitness
    (P : PresheafWithTransfers.{u + 1} k)
    {L : Type u} [Field L] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    {V U Y YU D A : SmoothSite (Spec (.of k))}
    [IsAffine Y.left] [IsAffine YU.left]
    (j : U ⟶ V) (q₀ : Y ⟶ SmoothSite.Contraction.affineLineCylinder.obj V)
    (qU : YU ⟶ SmoothSite.Contraction.affineLineCylinder.obj U) [Etale qU.left]
    (r : YU ⟶ Y) (hr : r ≫ q₀ = qU ≫ SmoothSite.Contraction.affineLineCylinder.map j)
    (z₀ : V ⟶ Y) (zU : U ⟶ YU) (hzr : zU ≫ r = j ≫ z₀)
    (e₀ : Y ⟶ A) (δ : D ⟶ A)
    [Mono ((SmoothSite.fieldBaseChange (algebraMap k L)).map δ)]
    (φU : SmoothSite.etalePullback qU (SmoothSite.Contraction.openInclusion.app U) ⟶ D)
    (hφU : φU ≫ δ = SmoothSite.etalePullbackFst qU
      (SmoothSite.Contraction.openInclusion.app U) ≫ r ≫ e₀)
    {B E O : SmoothSite (Spec (.of L))} [IsAffine E.left]
    (i : B ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj V)
    [Mono (SmoothSite.Contraction.affineLineCylinder.map i)]
    (bU : (SmoothSite.fieldBaseChange (algebraMap k L)).obj U ⟶ B)
    (hbU : bU ≫ i = (SmoothSite.fieldBaseChange (algebraMap k L)).map j)
    (η : E ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj Y) [Etale η.left]
    (q : E ⟶ SmoothSite.Contraction.affineLineCylinder.obj B)
    (hq : η ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map q₀ ≫
      (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom = q ≫
        SmoothSite.Contraction.affineLineCylinder.map i)
    (ζ : B ⟶ E)
    (hζη : ζ ≫ η = i ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map z₀)
    (α : O ⟶ E) (β : O ⟶ SmoothSite.Contraction.torusCylinder.obj B)
    (H : IsPullback β.left α.left (SmoothSite.Contraction.openInclusion.app B).left q.left)
    (φ : O ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj D)
    (hφ : φ ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map δ =
      α ≫ η ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map e₀)
    (s : sections P (Cor.mk D))
    (a : sections (finiteSeparableExtension L P) (Cor.mk
      (SmoothSite.Contraction.torusCylinder.obj B)))
    (c : sections (finiteSeparableExtension L P) (Cor.mk E))
    (h : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map β) a -
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map α) c =
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map φ)
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)) :
    Nonempty (ScalarAffineWitness P L qU zU φU s) := by
  let F := SmoothSite.fieldBaseChange (algebraMap k L)
  let : IsAffine ((𝟭 Scheme).obj Y.left) := inferInstanceAs (IsAffine Y.left)
  let : IsAffine ((𝟭 Scheme).obj YU.left) := inferInstanceAs (IsAffine YU.left)
  let : IsAffineHom Y.hom := isAffineHom_of_isAffine
    (show Y.left ⟶ Spec (.of k) from Y.hom)
  let : IsAffineHom YU.hom := isAffineHom_of_isAffine
    (show YU.left ⟶ Spec (.of k) from YU.hom)
  let : IsAffine (F.obj Y).left := inferInstanceAs
    (IsAffine (pullback Y.hom (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
  let : IsAffine (F.obj YU).left := inferInstanceAs
    (IsAffine (pullback YU.hom (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
  let E' := SmoothSite.etalePullback η (F.map r)
  let l := SmoothSite.etalePullbackFst η (F.map r)
  let f := SmoothSite.etalePullbackSnd η (F.map r)
  have hE' : IsAffine E'.left := inferInstanceAs
    (IsAffine (pullback η.left (F.map r).left))
  have hf : Etale f.left := inferInstanceAs (Etale (pullback.snd η.left (F.map r).left))
  let := hf
  have hlf : l ≫ η = f ≫ F.map r := (SmoothSite.etalePullbackCone η (F.map r)).condition
  have hm : (bU ≫ ζ) ≫ η = F.map zU ≫ F.map r := by
    rw [Category.assoc, hζη, ← Category.assoc, hbU, ← Functor.map_comp,
      ← hzr, Functor.map_comp]
  have HP : IsPullback l f η (F.map r) :=
    IsPullback.of_isLimit (SmoothSite.etalePullbackConeIsLimit η (F.map r))
  let mark := HP.lift (bU ≫ ζ) (F.map zU) hm
  let cU := (SmoothSite.fieldBaseChangeA1Iso (L := L) U).hom ≫
    SmoothSite.Contraction.affineLineCylinder.map bU
  let tU := (SmoothSite.fieldBaseChangeTorusCylinderIso (L := L) U).hom ≫
    SmoothSite.Contraction.torusCylinder.map bU
  have hlq : l ≫ q = f ≫ F.map qU ≫ cU := by
    apply (cancel_mono (SmoothSite.Contraction.affineLineCylinder.map i)).mp
    calc
      _ = l ≫ η ≫ F.map q₀ ≫ (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom := by
        rw [Category.assoc, ← hq]
      _ = f ≫ F.map (qU ≫ SmoothSite.Contraction.affineLineCylinder.map j) ≫
          (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom := by
        rw [← Category.assoc l, hlf, Category.assoc, ← Functor.map_comp_assoc, hr]
      _ = f ≫ F.map qU ≫ (SmoothSite.fieldBaseChangeA1Iso (L := L) U).hom ≫
          SmoothSite.Contraction.affineLineCylinder.map (bU ≫ i) := by
        rw [Functor.map_comp, Category.assoc, SmoothSite.fieldBaseChangeA1Iso_naturality, ← hbU]
      _ = (f ≫ F.map qU ≫ cU) ≫ SmoothSite.Contraction.affineLineCylinder.map i := by
        simp only [cU, Functor.map_comp, Category.assoc]
  have htj : tU ≫ SmoothSite.Contraction.openInclusion.app B =
      F.map (SmoothSite.Contraction.openInclusion.app U) ≫ cU := by
    dsimp only [tU, cU]
    rw [Category.assoc, SmoothSite.Contraction.openInclusion.naturality,
      ← Category.assoc, ← SmoothSite.fieldBaseChangeA1Iso_contractionOpen]
    simp only [Category.assoc, F]
  let αU := SmoothSite.etalePullbackFst qU (SmoothSite.Contraction.openInclusion.app U)
  let βU := SmoothSite.etalePullbackSnd qU (SmoothSite.Contraction.openInclusion.app U)
  have hU : βU ≫ SmoothSite.Contraction.openInclusion.app U = αU ≫ qU :=
    (SmoothSite.etalePullbackCone qU (SmoothSite.Contraction.openInclusion.app U)).condition.symm
  have hlη : l ≫ (η ≫ F.map e₀) = f ≫ F.map (r ≫ e₀) := by
    rw [← Category.assoc, hlf, Category.assoc, Functor.map_comp]
  refine ⟨{
    E := E'
    affine := hE'
    f := f
    etale := hf
    mark := mark
    mark_eq := HP.lift_snd _ _ _
    laurentSection := transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map tU) a
    ambientSection := transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map l) c
    relation := ?_ }⟩
  exact restriction_difference_on_scalar_etale_pullback P αU βU qU
    (SmoothSite.Contraction.openInclusion.app U) hU φU δ (r ≫ e₀) hφU
    f l q (SmoothSite.Contraction.openInclusion.app B) tU cU hlq htj α β H
    (η ≫ F.map e₀) hlη φ hφ _ a c h

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
