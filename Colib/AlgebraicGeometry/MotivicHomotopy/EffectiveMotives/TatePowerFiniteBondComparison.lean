/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TatePowerFiniteBond
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.TransferParameterProduct
import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.ShiftComparison

/-!
# Forgetting transfers on the original shifted finite bond

The two target comparisons commute on the signed cone coordinates.
Consequently the original finite Tate bond forgets to the existing
ordinary parameter map, including the positive Bockstein coordinate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace AlgebraicGeometry.MotivicHomotopy

section CochainComparison

open CochainComplex.finiteCoefficients

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  (F : C ⥤ D) (T : C ⥤ C) (U : D ⥤ D) [F.Additive] [T.Additive] [U.Additive]
  (φ : T ⋙ F ≅ F ⋙ U)

local notation "A" => T.mapHomologicalComplex (ComplexShape.up ℤ)
local notation "B" => Functor.mapHomologicalComplex F (ComplexShape.up ℤ)
local notation "D₁" => U.mapHomologicalComplex (ComplexShape.up ℤ)
local notation "θ" => NatIso.mapHomologicalComplex φ (ComplexShape.up ℤ)

private theorem parameterTarget_square (K : CochainComplex C ℤ) (n : ℕ) :
    let L := K⟦(1 : ℤ)⟧
    let M := finiteCoefficients K n
    let S := CategoryTheory.shiftFunctor (CochainComplex D ℤ) (1 : ℤ)
    let e := (B).commShiftIso (1 : ℤ)
    (B).map ((A).map (shiftOneIso K n).hom ≫ (mapIso T L n).hom) ≫
        (mapIso F ((A).obj L) n).hom ≫ map n ((θ).hom.app L) ≫
        map n ((D₁).map (e.hom.app K)) =
      (θ).hom.app (M⟦(1 : ℤ)⟧) ≫
        (D₁).map (e.hom.app M ≫ S.map (mapIso F K n).hom) ≫
        (D₁).map (shiftOneIso ((B).obj K) n).hom ≫
        (mapIso U ((B).obj K⟦(1 : ℤ)⟧) n).hom := by
  intro L M S e
  let s := (shiftOneIso K n).hom
  let t := (shiftOneIso ((B).obj K) n).hom
  let e₁ := (mapIso F K n).hom
  let e₂ := (mapIso F L n).hom
  let x := (mapIso T L n).hom
  let y := (mapIso F ((A).obj L) n).hom
  let z := (mapIso U ((B).obj L) n).hom
  let z' := (mapIso U ((B).obj K⟦(1 : ℤ)⟧) n).hom
  let v := (D₁).map (e.hom.app K)
  have h₁ : (B).map x ≫ y ≫ map n ((θ).hom.app L) =
      (θ).hom.app (finiteCoefficients L n) ≫ (D₁).map e₂ ≫ z := by
    have h := mapIso_natTrans φ.hom L n
    rw [mapIso_comp_hom T F, mapIso_comp_hom F U] at h
    exact (Category.assoc _ _ _).symm.trans h
  have h₂ : z ≫ map n v = (D₁).map (map n (e.hom.app K)) ≫ z' :=
    (mapIso_naturality U (e.hom.app K) n).symm
  have h₃ : (B).map ((A).map s) ≫ (θ).hom.app (finiteCoefficients L n) =
      (θ).hom.app (M⟦(1 : ℤ)⟧) ≫ (D₁).map ((B).map s) :=
    (θ).hom.naturality s
  have h₄ : (B).map s ≫ e₂ ≫ map n (e.hom.app K) = e.hom.app M ≫ S.map e₁ ≫ t :=
    mapIso_shiftOne F K n
  calc
    _ = (B).map ((A).map s) ≫ ((B).map x ≫ y ≫ map n ((θ).hom.app L)) ≫ map n v := by
      change (B).map ((A).map s ≫ x) ≫ y ≫ map n ((θ).hom.app L) ≫ map n v = _
      simp only [(B).map_comp, Category.assoc]
    _ = ((B).map ((A).map s) ≫ (θ).hom.app (finiteCoefficients L n)) ≫
        (D₁).map e₂ ≫ z ≫ map n v := by
      rw [h₁]
      simp only [Category.assoc]
    _ = (θ).hom.app (M⟦(1 : ℤ)⟧) ≫ (D₁).map ((B).map s) ≫ (D₁).map e₂ ≫
        (z ≫ map n v) := by rw [h₃]; simp only [Category.assoc]
    _ = (θ).hom.app (M⟦(1 : ℤ)⟧) ≫
        (D₁).map ((B).map s ≫ e₂ ≫ map n (e.hom.app K)) ≫ z' := by
      rw [h₂]
      simp only [(D₁).map_comp, Category.assoc]
    _ = _ := by
      change (θ).hom.app (M⟦(1 : ℤ)⟧) ≫
          (D₁).map ((B).map s ≫ e₂ ≫ map n (e.hom.app K)) ≫ z' =
        (θ).hom.app (M⟦(1 : ℤ)⟧) ≫
          (D₁).map (e.hom.app M ≫ S.map e₁) ≫ (D₁).map t ≫ z'
      rw [h₄, ← Category.assoc (e.hom.app M), (D₁).map_comp]
      simp only [Category.assoc]

end CochainComparison

open AlgebraicGeometry.Scheme PresheafWithTransfers SheafWithTransfers

universe u

variable (k : Type u) [Field k]

local notation "F" => SheafWithTransfers.toSheaf k
local notation "T" => SheafWithTransfers.torusSectionsFunctor k
local notation "U" => torusParameterSheafFunctor k
local notation "c" => ComplexShape.up ℤ
local notation "θ" => NatIso.mapHomologicalComplex (torusSectionsToSheafIso k) c

private theorem ordinaryTarget_hom (q n : ℕ) :
    let B := (U).mapHomologicalComplex c
    let K := motivicSheafComplex k (q + 1)
    (motivicFiniteParameterTargetIso k q n).hom =
      B.map (finiteCoefficients.shiftOneIso K n).hom ≫
        (finiteCoefficients.mapIso U (K⟦(1 : ℤ)⟧) n).hom := by
  intro B K
  let L := K⟦(1 : ℤ)⟧
  have h : ((n • 𝟙 K)⟦(1 : ℤ)⟧') = n • 𝟙 L := by simp [L]
  have hB : B.map (n • 𝟙 L) = n • 𝟙 (B.obj L) := by simp
  have hs : (finiteCoefficients.shiftOneIso K n).hom =
      (mappingCone.shiftIso (n • 𝟙 K) 1).hom ≫
        (eqToIso (congrArg (fun f : L ⟶ L => mappingCone f) h)).hom :=
    finiteCoefficients.shiftTriangleIso_hom₃ K n 1 h
  rw [hs, finiteCoefficients.mapIso_eq U L n hB]
  exact motivicFiniteParameterTargetIso_hom_eq k q n h hB

private theorem underlyingCone_hom (q n : ℕ) :
    (finiteCoefficients.mapIso F (motivicComplex k q) n).hom =
      (motivicFiniteComplexUnderlyingIso k q n).hom := by
  let K := motivicComplex k q
  let D := (F).mapHomologicalComplex c
  have h : D.map (n • 𝟙 K) = n • 𝟙 (D.obj K) := by simp
  rw [finiteCoefficients.mapIso_eq F K n h]
  unfold motivicFiniteComplexUnderlyingIso
  rfl

set_option maxHeartbeats 400000 in
-- Compare the two underlying shift and cone presentations of the same map.
/-- Forgetting transfers on the actual shifted finite bond gives the
original ordinary finite parameter product with its signed cone target. -/
theorem motivicFiniteTransferParameterProduct_underlying (q n : ℕ) :
    let D := (F).mapHomologicalComplex c
    let B := (U).mapHomologicalComplex c
    let M := motivicFiniteComplex k (q + 1) n
    let e := D.commShiftIso (1 : ℤ)
    let S := CategoryTheory.shiftFunctor (CochainComplex (Sheaf
      (SmoothSite.nisnevichTopology (Spec (.of k))) (LargeAb k)) ℤ) (1 : ℤ)
    D.map (motivicFiniteTransferParameterProduct k q n) ≫ (θ).hom.app (M⟦(1 : ℤ)⟧) ≫
        B.map (e.hom.app M ≫ S.map (motivicFiniteComplexUnderlyingIso k (q + 1) n).hom) =
      (motivicFiniteComplexUnderlyingIso k q n).hom ≫
        motivicFiniteSheafParameterProduct k q n := by
  intro D B M e S
  let K := motivicComplex k (q + 1)
  let A := (T).mapHomologicalComplex c
  let f := motivicFiniteTransferParameterProduct k q n
  let g := motivicFiniteTransferParameterProductToCone k q n
  let L := K⟦(1 : ℤ)⟧
  let a := (finiteCoefficients.shiftOneIso K n).hom
  let b := (finiteCoefficients.mapIso T L n).hom
  let d := (finiteCoefficients.mapIso F (A.obj L) n).hom
  let h := e.hom.app K
  let p := (motivicFiniteParameterTargetIso k q n).hom
  let v := (motivicFiniteComplexUnderlyingIso k q n).hom
  let z := motivicFiniteSheafParameterProduct k q n
  have hf : f ≫ A.map a ≫ b = g := motivicFiniteTransferParameterProduct_comp_target k q n
  have h₀ : D.map g ≫ d ≫ finiteCoefficients.map n ((θ).hom.app L) = v ≫ z ≫ p :=
    motivicFiniteTransferParameterProductToCone_underlying k q n
  have h₁ := parameterTarget_square F T U (torusSectionsToSheafIso k) K n
  change D.map (A.map a ≫ b) ≫ d ≫ finiteCoefficients.map n ((θ).hom.app L) ≫
      finiteCoefficients.map n (B.map h) =
    (θ).hom.app (M⟦(1 : ℤ)⟧) ≫
      B.map (e.hom.app M ≫ S.map (finiteCoefficients.mapIso F K n).hom) ≫
      B.map (finiteCoefficients.shiftOneIso (D.obj K) n).hom ≫
      (finiteCoefficients.mapIso U (D.obj K⟦(1 : ℤ)⟧) n).hom at h₁
  let t := (finiteCoefficients.mapIso F K n).hom
  let t' : D.obj M ⟶ motivicFiniteSheafComplex k (q + 1) n :=
    (motivicFiniteComplexUnderlyingIso k (q + 1) n).hom
  have ht : t = t' := underlyingCone_hom k (q + 1) n
  let u := B.map (finiteCoefficients.shiftOneIso (D.obj K) n).hom
  let v' := (finiteCoefficients.mapIso U (D.obj K⟦(1 : ℤ)⟧) n).hom
  have hp : u ≫ v' = p := (ordinaryTarget_hom k q n).symm
  have hh : h = 𝟙 (D.obj L) := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have hId : finiteCoefficients.map n (B.map h) =
      𝟙 (finiteCoefficients (B.obj (D.obj L)) n) := by
    have hB : B.map h = 𝟙 (B.obj (D.obj L)) :=
      (B.congr_map hh).trans (B.map_id _)
    exact (congrArg (finiteCoefficients.map n) hB).trans (finiteCoefficients.map_id n)
  let d' := B.map (e.hom.app M ≫ S.map t')
  have hTarget : D.map (A.map a ≫ b) ≫ d ≫ finiteCoefficients.map n ((θ).hom.app L) =
      (θ).hom.app (M⟦(1 : ℤ)⟧) ≫ d' ≫ p := by
    change D.map (A.map a ≫ b) ≫ d ≫ finiteCoefficients.map n ((θ).hom.app L) ≫
      finiteCoefficients.map n (B.map h) = (θ).hom.app (M⟦(1 : ℤ)⟧) ≫
      B.map (e.hom.app M ≫ S.map t) ≫ u ≫ v' at h₁
    rw [hId, ht, hp] at h₁
    have hcomp : finiteCoefficients.map n ((θ).hom.app L) ≫
        𝟙 (finiteCoefficients (B.obj (D.obj L)) n) = finiteCoefficients.map n ((θ).hom.app L) :=
      Category.comp_id _
    exact (congrArg (D.map (A.map a ≫ b) ≫ d ≫ ·) hcomp).symm.trans h₁
  change D.map f ≫ (θ).hom.app (M⟦(1 : ℤ)⟧) ≫ d' = v ≫ z
  apply (cancel_mono p).1
  calc
    _ = D.map f ≫ (D.map (A.map a ≫ b) ≫ d ≫
        finiteCoefficients.map n ((θ).hom.app L)) := by
      let r := (θ).hom.app (M⟦(1 : ℤ)⟧)
      exact ((Category.assoc (D.map f) (r ≫ d') p).trans
        (congrArg (D.map f ≫ ·) (Category.assoc r d' p))).trans
        (congrArg (D.map f ≫ ·) hTarget.symm)
    _ = D.map g ≫ d ≫ finiteCoefficients.map n ((θ).hom.app L) := by
      have hmap : D.map f ≫ D.map (A.map a ≫ b) = D.map g :=
        (D.map_comp _ _).symm.trans (D.congr_map hf)
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ d ≫ finiteCoefficients.map n ((θ).hom.app L)) hmap)
    _ = _ := h₀.trans (Category.assoc _ _ _).symm

end AlgebraicGeometry.MotivicHomotopy
