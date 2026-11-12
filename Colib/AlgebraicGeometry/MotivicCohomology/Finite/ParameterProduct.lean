/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Complex
public import Colib.AlgebraicGeometry.MotivicCohomology.ParameterProduct

/-!
# The multiplicative parameter map with finite motivic coefficients

Apply the actual multiplication-cone functor to the integral parameter map.
The native cone shift and additive reindexing comparisons identify the target
with the reindexed next-weight finite complex shifted by one. The comparison
uses the signed shift on the first cone coordinate and preserves the original
integral reduction map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace AlgebraicGeometry.PresheafWithTransfers

section ConeComparison

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C] [Preadditive D] [HasBinaryBiproducts D]

private theorem mappingCone_inr_eqToIso {K L : CochainComplex C ℤ} {φ ψ : K ⟶ L} (h : φ = ψ) :
    mappingCone.inr φ ≫ (eqToIso (congrArg (fun f : K ⟶ L ↦ mappingCone f) h)).hom =
      mappingCone.inr ψ := by
  subst ψ
  simp

private theorem mappingCone_shiftIso_inr {K L : CochainComplex C ℤ} (φ : K ⟶ L) (s : ℤ) :
    (mappingCone.inr φ)⟦s⟧' ≫ (mappingCone.shiftIso φ s).hom = mappingCone.inr (φ⟦s⟧') := by
  apply (cancel_mono (mappingCone.shiftIso φ s).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp [mappingCone.shiftIso]

variable (F : C ⥤ D) [F.Additive]

local notation "R" => Functor.mapHomologicalComplex F (ComplexShape.up ℤ)

private def coefficientMapShiftIso (K : CochainComplex C ℤ) (n : ℕ) (s : ℤ) :
    (R).obj ((finiteCoefficients K n)⟦s⟧) ≅ finiteCoefficients ((R).obj (K⟦s⟧)) n := by
  let L := K⟦s⟧
  have hs : ((n • 𝟙 K)⟦s⟧') = n • 𝟙 L := by simp [L]
  have hF : (R).map (n • 𝟙 L) = n • 𝟙 ((R).obj L) := by simp
  exact (R).mapIso (mappingCone.shiftIso (n • 𝟙 K) s ≪≫
      eqToIso (congrArg (fun f : L ⟶ L ↦ mappingCone f) hs)) ≪≫
    mappingCone.mapHomologicalComplexIso (n • 𝟙 L) F ≪≫
      eqToIso (congrArg (fun f : (R).obj L ⟶ (R).obj L ↦ mappingCone f) hF)

private theorem coefficientMapShiftIso_integral (K : CochainComplex C ℤ) (n : ℕ) (s : ℤ) :
    (R).map ((finiteCoefficients.integral K n)⟦s⟧') ≫ (coefficientMapShiftIso F K n s).hom =
      finiteCoefficients.integral ((R).obj (K⟦s⟧)) n := by
  have hs : ((n • 𝟙 K)⟦s⟧') = n • 𝟙 (K⟦s⟧) := by simp
  have hF : (R).map (n • 𝟙 (K⟦s⟧)) = n • 𝟙 ((R).obj (K⟦s⟧)) := by simp
  simp only [coefficientMapShiftIso, finiteCoefficients.integral, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← (R).map_comp_assoc, mappingCone_shiftIso_inr (n • 𝟙 K) s, ← (R).map_comp_assoc,
    mappingCone_inr_eqToIso hs, ← Category.assoc, mappingCone.map_inr (n • 𝟙 (K⟦s⟧)) F,
    mappingCone_inr_eqToIso hF]

end ConeComparison

open _root_.AlgebraicGeometry.Scheme

universe u

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

local notation "R" =>
  Functor.mapHomologicalComplex (torusParameterSheafFunctor k) (ComplexShape.up ℤ)

/-- The reindexed shifted finite target is the multiplication cone on the
actual integral target. -/
@[no_expose]
def motivicFiniteParameterTargetIso (q n : ℕ) :
    (R).obj ((motivicFiniteSheafComplex k (q + 1) n)⟦(1 : ℤ)⟧) ≅
      finiteCoefficients ((R).obj ((motivicSheafComplex k (q + 1))⟦(1 : ℤ)⟧)) n :=
  coefficientMapShiftIso (torusParameterSheafFunctor k) (motivicSheafComplex k (q + 1)) n 1

/-- The target comparison identifies the original shifted integral reduction
with integral reduction on the reindexed integral target. -/
@[reassoc]
theorem motivicFiniteParameterTargetIso_integral (q n : ℕ) :
    (R).map ((finiteCoefficients.integral (motivicSheafComplex k (q + 1)) n)⟦(1 : ℤ)⟧') ≫
        (motivicFiniteParameterTargetIso k q n).hom =
      finiteCoefficients.integral ((R).obj ((motivicSheafComplex k (q + 1))⟦(1 : ℤ)⟧)) n :=
  coefficientMapShiftIso_integral (torusParameterSheafFunctor k) (motivicSheafComplex k (q + 1)) n 1

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))
  AddCommGrpCat.{u + 1}]

/-- The native finite-coefficient map induced by the integral motivic parameter map. -/
def motivicFiniteSheafParameterProduct (q n : ℕ) :
    motivicFiniteSheafComplex k q n ⟶
      (R).obj ((motivicFiniteSheafComplex k (q + 1) n)⟦(1 : ℤ)⟧) :=
  finiteCoefficients.map n (motivicSheafParameterProduct k q) ≫
    (motivicFiniteParameterTargetIso k q n).inv

/-- Integral reduction commutes with the actual finite-coefficient parameter map. -/
@[reassoc]
theorem integral_motivicFiniteSheafParameterProduct (q n : ℕ) :
    finiteCoefficients.integral (motivicSheafComplex k q) n ≫
        motivicFiniteSheafParameterProduct k q n =
      motivicSheafParameterProduct k q ≫
        (R).map ((finiteCoefficients.integral (motivicSheafComplex k (q + 1)) n)⟦(1 : ℤ)⟧') := by
  rw [motivicFiniteSheafParameterProduct, ← Category.assoc, finiteCoefficients.integral_naturality,
    Category.assoc, ← motivicFiniteParameterTargetIso_integral k q n, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.PresheafWithTransfers
