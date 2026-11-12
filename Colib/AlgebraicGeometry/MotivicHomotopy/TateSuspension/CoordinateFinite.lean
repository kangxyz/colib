/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Complex
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.CoordinateTate

/-!
# Finite-coefficient Tate coordinate classes

Reduce the integral torus and Tate coordinate classes by the inclusion into
the actual multiplication cone. The Tate quotient boundary commutes with
these reductions by naturality of the native shift-addition isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]
  [HasDerivedCategory.{d}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Rₖ" => CommRingCat.of k
local notation "Sₖ" => Spec Rₖ
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ

/-- Reduce the forward torus coordinate to the original finite coefficient complex. -/
def torusCoordinateFiniteClass (n : ℕ) :
    (reducedHypercohomology.{d, u + 1} Cₖ Jₖ (motivicFiniteSheafComplex k 1 n) 1).obj
      (op (liftedPointedTorus k)) :=
  (reducedHypercohomologyCoefficientMap.{d, u + 1} Cₖ Jₖ 1
    (CochainComplex.finiteCoefficients.integral (motivicSheafComplex k 1) n)).app
      (op (liftedPointedTorus k)) (torusCoordinateReducedMotivicClass.{d} k)

/-- Reduce the integral Tate class by the actual inclusion into the multiplication cone. -/
def tateCoordinateFiniteClass (n : ℕ) :
    (reducedHypercohomology.{d, u + 1} Cₖ Jₖ (motivicFiniteSheafComplex k 1 n) 2).obj
      (op (liftedTateSphere Rₖ)) :=
  (reducedHypercohomologyCoefficientMap.{d, u + 1} Cₖ Jₖ 2
    (CochainComplex.finiteCoefficients.integral (motivicSheafComplex k 1) n)).app
      (op (liftedTateSphere Rₖ)) (tateCoordinateClass.{d} k)

/-- The original Tate quotient boundary carries the finite torus coordinate
to the finite Tate class with its native shift convention. -/
theorem tateCoordinateFiniteClass_eq_connecting (n : ℕ) :
    tateCoordinateFiniteClass.{d} k n =
      tateSphereConnecting.{d} Rₖ ≫ (torusCoordinateFiniteClass.{d} k n)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}))
          (1 : ℤ) 1).inv.app (DerivedCategory.Q.{d}.obj (motivicFiniteSheafComplex k 1 n)) := by
  let D := DerivedCategory.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1})
  let K := DerivedCategory.Q.{d}.obj (motivicSheafComplex k 1)
  let L := DerivedCategory.Q.{d}.obj (motivicFiniteSheafComplex k 1 n)
  let ρ := DerivedCategory.Q.{d}.map
    (CochainComplex.finiteCoefficients.integral (motivicSheafComplex k 1) n)
  let δ := tateSphereConnecting.{d} Rₖ
  let x : (reducedDerivedChains.{d, u + 1} Cₖ Jₖ).obj (liftedPointedTorus k) ⟶
      K⟦(1 : ℤ)⟧ := torusCoordinateReducedMotivicClass.{d} k
  let S := shiftFunctor D (1 : ℤ)
  let e := shiftFunctorAdd D (1 : ℤ) 1
  have h : tateCoordinateClass.{d} k = δ ≫ S.map x ≫ e.inv.app K := by
    let ν := (weightOneDerivedUnitsIso.{d} k).hom
    let ν₂ := (weightOneTateDerivedUnitsIso.{d} k).hom
    apply (cancel_mono ν₂).1
    change tateCoordinateClass.{d} k ≫ ν₂ =
      (δ ≫ S.map x ≫ e.inv.app K) ≫ (e.hom.app K ≫ S.map ν)
    calc
      _ = δ ≫ S.map (x ≫ ν) :=
        (tateCoordinateClass_comp_weightOneTateDerivedUnitsIso.{d} k).trans
          (congrArg (fun f => δ ≫ S.map f)
            (torusCoordinateReducedMotivicClass_comp_weightOneDerivedUnitsIso.{d} k).symm)
      _ = δ ≫ S.map x ≫ S.map ν := congrArg (δ ≫ ·) (S.map_comp x ν)
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [tateCoordinateFiniteClass, torusCoordinateFiniteClass,
    reducedHypercohomologyCoefficientMap_app_apply]
  let v : (reducedDerivedChains.{d, u + 1} Cₖ Jₖ).obj (liftedTateSphere Rₖ) ⟶
      K⟦(2 : ℤ)⟧ := tateCoordinateClass.{d} k
  have hv : v = δ ≫ S.map x ≫ e.inv.app K := h
  have hn : e.inv.app K ≫ (shiftFunctor D (2 : ℤ)).map ρ =
      S.map (S.map ρ) ≫ e.inv.app L := (e.inv.naturality ρ).symm
  change v ≫ (shiftFunctor D (2 : ℤ)).map ρ =
    δ ≫ S.map (x ≫ S.map ρ) ≫ e.inv.app L
  rw [hv]
  simp only [Category.assoc, hn, Functor.map_comp]
  exact congrArg (δ ≫ ·) (Category.assoc (S.map x) (S.map (S.map ρ)) (e.inv.app L)).symm

end AlgebraicGeometry.MotivicHomotopy
