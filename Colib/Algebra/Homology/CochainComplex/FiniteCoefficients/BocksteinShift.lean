/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.ModBockstein
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.ShiftComparison

/-!
# The coefficient Bockstein under additive functors and shift

The cone comparison for an additive functor preserves the actual Bockstein.
The signed cone comparison for a one-degree shift negates it.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex.finiteCoefficients

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

/-- The signed cone shift preserves integral reduction. -/
@[reassoc]
theorem shiftOneIso_hom_integral (K : CochainComplex C ℤ) (n : ℕ) :
    (integral K n)⟦(1 : ℤ)⟧' ≫ (shiftOneIso K n).hom = integral (K⟦(1 : ℤ)⟧) n := by
  let e := shiftTriangleIso K n 1
  have h := e.hom.comm₂
  change (((1 : ℤ).negOnePow • (integral K n)⟦(1 : ℤ)⟧') ≫ (shiftOneIso K n).hom) =
    e.hom.hom₂ ≫ integral (K⟦(1 : ℤ)⟧) n at h
  rw [show e.hom.hom₂ = -(𝟙 (K⟦(1 : ℤ)⟧)) by
    dsimp only [e]
    rw [shiftTriangleIso_hom₂, Int.negOnePow_one, Units.neg_smul, one_smul]] at h
  have h' : -((integral K n)⟦(1 : ℤ)⟧' ≫ (shiftOneIso K n).hom) =
      -(integral (K⟦(1 : ℤ)⟧) n) := by
    simp only [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.neg_comp] at h
    exact h.trans (congrArg Neg.neg (Category.id_comp (integral (K⟦(1 : ℤ)⟧) n)))
  exact neg_injective h'

/-- The actual degree-one Bockstein anticommutes with the signed cone shift. -/
@[reassoc]
theorem shiftOneIso_hom_modBockstein (K : CochainComplex C ℤ) (n : ℕ) :
    (shiftOneIso K n).hom ≫ modBockstein (K⟦(1 : ℤ)⟧) n =
      -((modBockstein K n)⟦(1 : ℤ)⟧' ≫ (shiftOneIso K n).hom⟦(1 : ℤ)⟧') := by
  let e := shiftTriangleIso K n 1
  have h : (shiftOneIso K n).hom ≫ bockstein (K⟦(1 : ℤ)⟧) n =
      -((bockstein K n)⟦(1 : ℤ)⟧') := by
    have h₃ := e.hom.comm₃.symm
    let T := CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)
    change e.hom.hom₃ ≫ bockstein (T.obj K) n =
      ((Triangle.shiftFunctor (CochainComplex C ℤ) 1).obj (triangle K n)).mor₃ ≫
        T.map e.hom.hom₁ at h₃
    dsimp only [Triangle.shiftFunctor] at h₃
    change e.hom.hom₃ ≫ bockstein (T.obj K) n =
      ((1 : ℤ).negOnePow • (T.map (bockstein K n) ≫
        (shiftFunctorComm (CochainComplex C ℤ) (1 : ℤ) 1).hom.app K)) ≫
          T.map e.hom.hom₁ at h₃
    have h₁ : e.hom.hom₁ = 𝟙 (T.obj K) := shiftTriangleIso_hom₁ K n 1
    rw [h₁, T.map_id] at h₃
    have hc : (shiftFunctorComm (CochainComplex C ℤ) (1 : ℤ) 1).hom.app K =
        𝟙 (T.obj (T.obj K)) := by rw [shiftFunctorComm_eq_refl]; rfl
    rw [hc] at h₃
    have hh : ((1 : ℤ).negOnePow • (T.map (bockstein K n) ≫ 𝟙 _)) ≫ 𝟙 _ =
        -(T.map (bockstein K n)) := by
      calc
        _ = (1 : ℤ).negOnePow • (T.map (bockstein K n) ≫ 𝟙 _) := Category.comp_id _
        _ = (1 : ℤ).negOnePow • T.map (bockstein K n) :=
          congrArg ((1 : ℤ).negOnePow • ·) (Category.comp_id _)
        _ = _ := by simp
    exact h₃.trans hh
  unfold modBockstein
  rw [← Category.assoc, h, Preadditive.neg_comp, ← shiftOneIso_hom_integral,
    Functor.map_comp, Functor.map_comp, Category.assoc]

variable (F : C ⥤ D) [F.Additive]

local notation "R" => (F.mapHomologicalComplex (ComplexShape.up ℤ))

/-- Applying an additive functor preserves the actual mod-`n` Bockstein
through its multiplication cone and shift comparisons. -/
@[reassoc]
theorem mapIso_hom_modBockstein (K : CochainComplex C ℤ) (n : ℕ) :
    (mapIso F K n).hom ≫ modBockstein ((R).obj K) n =
      (R).map (modBockstein K n) ≫ ((R).commShiftIso (1 : ℤ)).hom.app _ ≫
        (mapIso F K n).hom⟦(1 : ℤ)⟧' := by
  let e := mapTriangleIso F K n
  let T := CategoryTheory.shiftFunctor (CochainComplex D ℤ) (1 : ℤ)
  let c := ((R).commShiftIso (1 : ℤ)).hom
  have hi := e.hom.comm₂
  change (R).map (integral K n) ≫ (mapTriangleIso F K n).hom.hom₃ =
    (mapTriangleIso F K n).hom.hom₂ ≫ integral ((R).obj K) n at hi
  rw [mapTriangleIso_hom₂, Category.id_comp, mapTriangleIso_hom₃] at hi
  have h₁ : e.hom.hom₁ = 𝟙 ((R).obj K) := mapTriangleIso_hom₁ F K n
  have hb : (mapIso F K n).hom ≫ bockstein ((R).obj K) n =
      (R).map (bockstein K n) ≫ c.app K := by
    have h₃ := e.hom.comm₃.symm
    change e.hom.hom₃ ≫ bockstein ((R).obj K) n =
      ((R).map (bockstein K n) ≫ c.app K) ≫ T.map e.hom.hom₁ at h₃
    rw [h₁, T.map_id] at h₃
    have he : e.hom.hom₃ = (mapIso F K n).hom := mapTriangleIso_hom₃ F K n
    exact (congrArg (· ≫ bockstein ((R).obj K) n) he.symm).trans
      (h₃.trans (Category.comp_id _))
  unfold modBockstein
  change _ = (R).map _ ≫ c.app _ ≫ T.map _
  rw [← Category.assoc, hb, ← hi, T.map_comp, (R).map_comp]
  simp only [Category.assoc]
  have hc : (R).map ((integral K n)⟦(1 : ℤ)⟧') ≫ c.app (finiteCoefficients K n) =
      c.app K ≫ T.map ((R).map (integral K n)) := c.naturality (integral K n)
  have ha := congrArg (fun f ↦ f ≫ T.map (mapIso F K n).hom) hc.symm
  simp only [Category.assoc] at ha
  exact congrArg ((R).map (bockstein K n) ≫ ·) ha

end CochainComplex.finiteCoefficients
