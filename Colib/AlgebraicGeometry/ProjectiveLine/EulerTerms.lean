/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.EulerSequence
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-! # The three actual terms of the projective-line Euler sequence -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjKoszulOverBase
open Stacks.AlgebraicGeometry.ProjKoszulComplex
open Stacks.AlgebraicGeometry.ExampleGenerator
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "C" => koszulOver 1 X (-2)

attribute [local instance] Abelian.hasFiniteBiproducts MvPolynomial.gradedAlgebra

/-- Each Koszul term is the direct sum of twists indexed by its coordinate subsets. -/
def projectiveLineEulerTermIso (j : ℤ) :
    (C).X j ≅ ⨁ (fun _ : koszulIndex 2 j => twistOver 1 X (-2 + j)) :=
  let f : koszulIndex 2 j → (AlgebraicGeometry.Proj
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1)).Modules :=
    koszulFamily (ULift.{u} ℤ) 1 (-2) j
  Functor.mapBiproduct (Scheme.Modules.pullback (toProj 1 X)) f

/-- The first term is the twist by minus two. -/
def projectiveLineEulerFirstIso : (projectiveLineEulerSequence X).X₁ ≅ twistOver 1 X (-2) :=
  projectiveLineEulerTermIso X 0 ≪≫ biproductUniqueIso _

/-- The middle term is the sum of two copies of the twist by minus one. -/
def projectiveLineEulerMiddleIso :
    (projectiveLineEulerSequence X).X₂ ≅ ⨁ (fun _ : Fin 2 => twistOver 1 X (-1)) := by
  let e := Fintype.equivFinOfCardEq (show Fintype.card (koszulIndex 2 (1 : ℤ)) = 2 by
    simpa using (card_koszulIndex 2 1))
  let f : koszulIndex 2 (1 : ℤ) → (P).Modules := fun _ => twistOver 1 X (-1)
  let g : Fin 2 → (P).Modules := fun _ => twistOver 1 X (-1)
  exact projectiveLineEulerTermIso X 1 ≪≫
    biproduct.whiskerEquiv (f := f) (g := g) e (fun _ => Iso.refl _)

/-- The last term is the structure sheaf, by the canonical zero-twist identification. -/
def projectiveLineEulerLastIso : (projectiveLineEulerSequence X).X₃ ≅
    _root_.SheafOfModules.unit ((P).ringCatSheaf) := by
  let : Unique (koszulIndex 2 (2 : ℤ)) :=
    { default := ⟨Finset.univ, by simp⟩
      uniq a := Subtype.ext (Finset.eq_univ_of_card _ (by
        have := a.2
        simp only [Fintype.card_fin]
        omega)) }
  exact projectiveLineEulerTermIso X 2 ≪≫ biproductUniqueIso _ ≪≫ twistZeroIsoUnit 1 X

/-- A constant family on two indices computes the binary sum. -/
def projectiveLineEulerMiddleBiprodIso :
    (projectiveLineEulerSequence X).X₂ ≅ (twistOver 1 X (-1)) ⊞ (twistOver 1 X (-1)) := by
  let L := twistOver 1 X (-1)
  let e : Fin 2 ≃ WalkingPair :=
    (Fintype.equivFinOfCardEq (α := WalkingPair) (by decide)).symm
  let b := biproduct.bicone (pairFunction L L)
  have hb : b.toBinaryBicone.IsBilimit :=
    b.toBinaryBiconeIsBilimit.symm (biproduct.isBilimit _)
  exact projectiveLineEulerMiddleIso X ≪≫
    biproduct.whiskerEquiv e (fun i => by cases e i <;> exact Iso.refl _) ≪≫
      biprod.uniqueUpToIso L L hb

private theorem isFiniteLocallyFree_of_iso {M N : (P).Modules} (e : M ≅ N)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N := by
  obtain ⟨q, hq, hf⟩ := h.exists_isFiniteLocallyFreeData
  let q' : _root_.SheafOfModules.LocalGeneratorsData.{u} N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((_root_.SheafOfModules.overFunctor (P).ringCatSheaf (q.X i)).mapIso e).hom }
  refine ⟨q', ⟨fun i => ?_⟩, ?_⟩
  · let u := ((_root_.SheafOfModules.overFunctor (P).ringCatSheaf (q.X i)).mapIso e)
    have h₀ : IsIso (q.generators i).π := hq.isIso i
    have h₁ : IsIso ((q.generators i).π ≫ u.hom) := inferInstance
    exact Eq.mpr (congrArg IsIso (_root_.SheafOfModules.GeneratingSections.ofEpi_π
      (q.generators i) u.hom)) h₁
  · have hFinite := hf.isFiniteType
    exact ⟨fun i => ⟨(hFinite i).finite⟩⟩

private theorem twistFiniteLocallyFree (a : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (twistOver 1 X a) := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (twistOver 1 X a) 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme
        (projectiveSpaceOver 1 X) _
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

instance projectiveLineEulerFirst_finiteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (projectiveLineEulerSequence X).X₁ :=
  isFiniteLocallyFree_of_iso X (projectiveLineEulerFirstIso X).symm (twistFiniteLocallyFree X (-2))

instance projectiveLineEulerMiddle_finiteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (projectiveLineEulerSequence X).X₂ := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (twistOver 1 X (-1)) := twistFiniteLocallyFree X (-1)
  exact isFiniteLocallyFree_of_iso X (projectiveLineEulerMiddleBiprodIso X).symm
    (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_biprod _ _)

instance projectiveLineEulerLast_finiteLocallyFree :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (projectiveLineEulerSequence X).X₃ :=
  isFiniteLocallyFree_of_iso X
    (twistZeroIsoUnit 1 X ≪≫ (projectiveLineEulerLastIso X).symm) (twistFiniteLocallyFree X 0)

end AlgebraicGeometry.Scheme
