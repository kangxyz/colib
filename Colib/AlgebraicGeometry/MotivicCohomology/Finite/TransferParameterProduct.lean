/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Functoriality
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.ParameterProduct
public import Colib.AlgebraicGeometry.MotivicCohomology.TransferParameterUnderlying

/-!
# The finite parameter map with transfers

Apply the original multiplication-cone construction to the signed
integral transfer parameter map. The natural cone comparison
preserves the integral and positive Bockstein coordinates and
recovers the existing ordinary finite parameter map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CochainComplex AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "F" => SheafWithTransfers.toSheaf k
local notation "B" => SheafWithTransfers.torusSectionsFunctor k
local notation "c" => ComplexShape.up ℤ
local notation "φ" => SheafWithTransfers.torusSectionsToSheafIso k

/-- The actual finite map before comparing its target to the reindexed
shifted finite motivic complex. -/
def motivicFiniteTransferParameterProductToCone (q n : ℕ) :
    motivicFiniteComplex k q n ⟶ finiteCoefficients
      (((B).mapHomologicalComplex c).obj ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧)) n :=
  finiteCoefficients.map n (motivicTransferParameterProduct k q)

/-- The original finite parameter map is obtained by forgetting
transfers, using the actual target cone comparison. -/
theorem motivicFiniteTransferParameterProductToCone_underlying (q n : ℕ) :
    let D := (F).mapHomologicalComplex c
    let K := ((B).mapHomologicalComplex c).obj ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧)
    let θ := (NatIso.mapHomologicalComplex (φ) c).hom.app
      ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧)
    D.map (motivicFiniteTransferParameterProductToCone k q n) ≫
      (finiteCoefficients.mapIso F K n).hom ≫ finiteCoefficients.map n θ =
    (motivicFiniteComplexUnderlyingIso k q n).hom ≫
      motivicFiniteSheafParameterProduct k q n ≫ (motivicFiniteParameterTargetIso k q n).hom := by
  intro D K θ
  let A₀ := Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}
  let f := motivicTransferParameterProduct k q
  let u := (finiteCoefficients.mapIso F (motivicComplex k q) n).hom
  let t := (motivicFiniteParameterTargetIso k q n)
  let V : CochainComplex A₀ ℤ ⥤ CochainComplex A₀ ℤ := finiteCoefficients.functor n
  have h : D.map (motivicFiniteTransferParameterProductToCone k q n) ≫
      (finiteCoefficients.mapIso F K n).hom = u ≫ V.map (D.map f) :=
    finiteCoefficients.mapIso_naturality F f n
  have hu : u = (motivicFiniteComplexUnderlyingIso k q n).hom := by
    let M := motivicComplex k q
    have e : D.map (n • 𝟙 M) = n • 𝟙 (D.obj M) :=
      (D.map_nsmul (f := 𝟙 M) (n := n)).trans (congrArg (n • ·) (D.map_id M))
    change (finiteCoefficients.mapIso F M n).hom = _
    rw [finiteCoefficients.mapIso_eq F M n e]
    unfold motivicFiniteComplexUnderlyingIso
    rfl
  have hf : D.map f ≫ θ = motivicSheafParameterProduct k q :=
    motivicTransferParameterProduct_underlying k q
  have ht : motivicFiniteSheafParameterProduct k q n ≫ t.hom =
      V.map (motivicSheafParameterProduct k q) := by
    unfold motivicFiniteSheafParameterProduct
    change (V.map (motivicSheafParameterProduct k q) ≫ t.inv) ≫ t.hom = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (V.map (motivicSheafParameterProduct k q) ≫ ·) t.inv_hom_id).trans
        (Category.comp_id _))
  calc
    _ = (u ≫ V.map (D.map f)) ≫ V.map θ :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ V.map θ) h)
    _ = u ≫ V.map (D.map f ≫ θ) :=
      (Category.assoc _ _ _).trans (congrArg (u ≫ ·) (V.map_comp _ _).symm)
    _ = u ≫ V.map (motivicSheafParameterProduct k q) := congrArg (fun m => u ≫ V.map m) hf
    _ = _ := congrArg₂ (· ≫ ·) hu ht.symm

end AlgebraicGeometry.PresheafWithTransfers
