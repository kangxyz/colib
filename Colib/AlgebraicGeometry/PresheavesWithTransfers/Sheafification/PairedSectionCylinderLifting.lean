/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.PairedActionLift
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormChartMark
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormUnitDomain

/-!
# Lifting along the actual paired section data

This is the common result of the four actions on the original representatives.
It records the actual Cartesian cylinder, both marked section pairs, and the
literal restriction maps. The polynomial geometry produces these inputs.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample Stacks.Divisors Stacks.Morphisms
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

set_option maxHeartbeats 500000 in
-- The original section choices and the Cartesian cylinder use dependent scheme maps.
/-- The paired choices lift their original representatives to the whole restricted cylinder. -/
def PairedSectionCylinderLifting (k : Type u) [Field k] : Prop :=
  ∀ {S X Y P C A Z D₁ D₂ V : Scheme.{u}}
    [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine A] [IsIntegral A] [IsAffine V]
    (t : S ⟶ Spec (.of k)) [Smooth t]
    (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (π : P ⟶ S) [IsProper π] [SmoothOfRelativeDimension 1 π] (f : C ⟶ P) [IsFinite f]
    (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
    (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
    (p : Y ⟶ X) [Flat p] (hRet : j ≫ f = p ≫ jA)
    (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
    (a : A ⟶ X) [IsOpenImmersion a] [SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]
    (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
    (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
      SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
    (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
    (d₂ : D₂ ⟶ P) [IsClosedImmersion d₂] [IsClosedImmersion (z ≫ jA)]
    (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
    (ha : Disjoint (Set.range a) (Set.range z))
    (_c₁ : SectionData q (f ≫ π) j p hB a z s hs H e d₁ hd₁ ha)
    (_c₂ : SectionData q π jA (𝟙 X) hA a z z (Category.comp_id z) (IsPullback.of_id_snd)
      e d₂ hd₂ ha)
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ f ≫ π)]
    (u : V ⟶ Y) (hu : u ≫ j = v) (g : V ⟶ A) (hg : v ≫ f = g ≫ (a ≫ jA))
    (_hc₁ : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d₁ ∨ x ∈ Set.range (s ≫ j))
    (_hc₂ : ∀ x : P, x ∈ Set.range (a ≫ jA) ∨ x ∈ Set.range d₂ ∨
      x ∈ Set.range (z ≫ jA)),
    let zA := z ≫ jA
    let hmark := markedSection_original_equation f j zA s
      (pairedMark_isPullback f j jA p hRet z s H)
    ∀ [IsFiniteLocallyFree (graphProductMap π f j)]
      [IsFiniteLocallyFree (retainedProductInclusion (a ≫ q) π f)]
      [IsIntegral (pullback (a ≫ q) π)]
      [IsSeparated (terminal.from (pullback (j ≫ f ≫ π) π : Scheme.{u}))]
      (bI : pullback f d₂ ⟶ D₁) (_hbI : bI ≫ d₁ = pullback.fst f d₂)
      (bE : (residualMarkedFiberOpen f j zA s hmark).toScheme ⟶ D₁)
      (_hbE : bE ≫ d₁ = residualMarkedFiberMap f j zA s hmark)
      (_hResidual : ∀ (T : Scheme.{u}) (w : T ⟶ pullback (j ≫ f ≫ π) π),
        PairedNormChartResidualFactor π f j jA p hRet z s H w d₁),
      let b := j ≫ f ≫ π
      let bA := jA ≫ π
      let rB := v ≫ f ≫ π
      let rA := (a ≫ jA) ≫ π
      letI : Smooth q := SmoothOfRelativeDimension.smooth 1 q
      letI : Smooth b := SmoothOfRelativeDimension.smooth 1 b
      letI : Smooth bA := SmoothOfRelativeDimension.smooth 1 bA
      letI : Smooth rB := SmoothOfRelativeDimension.smooth 1 rB
      letI : Smooth rA := SmoothOfRelativeDimension.smooth 1 rA
      let Y₀ := SmoothSite.mk (b ≫ t)
      let X₀ := SmoothSite.mk (bA ≫ t)
      let V₀ := SmoothSite.mk (rB ≫ t)
      let A₀ := SmoothSite.mk ((a ≫ q) ≫ t)
      let A₁ := SmoothSite.mk (rA ≫ t)
      let hSourceBase : p ≫ bA = b := by
        rw [← Category.assoc p jA π, ← hRet, Category.assoc]
      let hTargetBase : g ≫ rA = rB := by
        rw [← Category.assoc g (a ≫ jA) π, ← hg, Category.assoc]
      let ha₀ : a ≫ bA = a ≫ q := congrArg (a ≫ ·) (hA.trans (Category.id_comp q))
      let u₀ : V₀ ⟶ Y₀ := SmoothSite.homMk u
        ((Category.assoc u b t).symm.trans
          (congrArg (fun w ↦ w ≫ t) ((Category.assoc u j (f ≫ π)).symm.trans
            (congrArg (fun w ↦ w ≫ f ≫ π) hu))))
      let p₀ : Y₀ ⟶ X₀ := SmoothSite.homMk p
        ((Category.assoc p bA t).symm.trans (congrArg (fun w ↦ w ≫ t) hSourceBase))
      let g₀ : V₀ ⟶ A₁ := SmoothSite.homMk g
        ((Category.assoc g rA t).symm.trans (congrArg (fun w ↦ w ≫ t) hTargetBase))
      let a₀ : A₀ ⟶ X₀ := SmoothSite.homMk a
        ((Category.assoc a bA t).symm.trans (congrArg (fun w ↦ w ≫ t) ha₀))
      let I₀ : A₀ ≅ A₁ := MorphismProperty.Over.isoMk (Iso.refl A) (by
        change 𝟙 A ≫ (rA ≫ t) = (a ≫ q) ≫ t
        exact (Category.id_comp _).trans
          (congrArg (· ≫ t) ((Category.assoc a jA π).trans ha₀)))
      ∀ (Pst : PresheafWithTransfers.{u + 1} k) (_hPst : Pst.IsA1Invariant)
        (_hSrc : SourceMarkedBoundaryGeneration π f j zA s d₁)
        (_hPuncture : Function.Surjective rA) (_hInfinity : Function.Surjective (d₂ ≫ π))
        (_hIntegral : ∀ (K : Scheme.{u}) [IsAffine K] [IsIntegral K] (bK : K ⟶ S),
          IsIntegral (pullback bK π))
        {Xo U U' T Ao Yo Bo : SmoothSite (Spec (.of k))}
        (jU : U ⟶ Xo) (l : U' ⟶ U) [IsOpenImmersion jU.left] [IsOpenImmersion l.left]
        (_hne : Nonempty U'.left) (eT : T ≅ affineLineCylinder.obj U)
        (h : affineLineCylinder.obj U' ⟶ T) (_he : h ≫ eT.hom = affineLineCylinder.map l)
        (E : X₀ ≅ affineLineCylinder.obj U')
        (i : Ao ⟶ T) (pT : Yo ⟶ T) (oA : Bo ⟶ Ao) (oY : Bo ⟶ Yo)
        (rAo : A₀ ⟶ Ao) (rYo : Y₀ ⟶ Yo) (rBo : V₀ ⟶ Bo)
        (_hAo : rAo ≫ i = (a₀ ≫ E.hom) ≫ h) (_hYo : rYo ≫ pT = (p₀ ≫ E.hom) ≫ h)
        (_hBoA : rBo ≫ oA = g₀ ≫ (I₀).inv ≫ rAo) (_hBoY : rBo ≫ oY = u₀ ≫ rYo)
        (_hCover : Sieve.ofTwoArrows (a₀ ≫ E.hom) (p₀ ≫ E.hom) ∈
          SmoothSite.nisnevichTopology (Spec (.of k)) (affineLineCylinder.obj U'))
        (σ : ((nisnevichSheafify k).obj Pst).obj.sections (Cor.mk (affineLineCylinder.obj Xo)))
        (sA : (nisnevichImage Pst).sections (Cor.mk Ao))
        (sY : (nisnevichImage Pst).sections (Cor.mk Yo))
        (_hm : (nisnevichImage Pst).transfer ((Cor.graphFunctor k).map oA) sA =
          (nisnevichImage Pst).transfer ((Cor.graphFunctor k).map oY) sY)
        (_hsA : (nisnevichImageι Pst).hom.app (op (Cor.mk Ao)) sA =
          ((nisnevichSheafify k).obj Pst).obj.transfer
            ((Cor.graphFunctor k).map (i ≫ eT.hom ≫ affineLineCylinder.map jU)) σ)
        (_hsY : (nisnevichImageι Pst).hom.app (op (Cor.mk Yo)) sY =
          ((nisnevichSheafify k).obj Pst).obj.transfer
            ((Cor.graphFunctor k).map (pT ≫ eT.hom ≫ affineLineCylinder.map jU)) σ),
        IsOpenImmersion (l ≫ jU).left ∧ Nonempty U'.left ∧
          ∃ z : (nisnevichImage Pst).sections (Cor.mk (affineLineCylinder.obj U')),
            (nisnevichImageι Pst).hom.app (op (Cor.mk (affineLineCylinder.obj U'))) z =
              ((nisnevichSheafify k).obj Pst).obj.transfer
                ((Cor.graphFunctor k).map (affineLineCylinder.map (l ≫ jU))) σ

end AlgebraicGeometry.PresheafWithTransfers
