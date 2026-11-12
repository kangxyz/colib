/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Basic
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalInvariance
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalComparison
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import StacksCore.Algebra.Homology.TotalComplexHomotopy

/-!
# Bounded-above singular representatives with transfers

Apply the original singular total complex and exact Nisnevich sheafification
to a bounded-above cochain complex. The construction retains the original
bound, has A¹-invariant cohomology, and respects both homotopies and
quasi-isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "c" => ComplexShape.up ℤ

/-- Apply the actual total singular functor and termwise transfer sheafification. -/
abbrev singularSheafTotalFunctor :
    CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ ⥤
      CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  singularTotalFunctor k ⋙ (nisnevichSheafify k).mapHomologicalComplex c

/-- The total construction retains an upper bound on the original coefficients. -/
theorem singularSheafTotalFunctor_obj_isStrictlyLE
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    ((singularSheafTotalFunctor k).obj K).IsStrictlyLE b := by
  let L := (singularTotalFunctor k).obj K
  let : L.IsStrictlyLE b := singularTotalFunctor_obj_isStrictlyLE k K b
  apply (CochainComplex.isStrictlyLE_iff _ b).2
  intro i hi
  exact (nisnevichSheafify k).map_isZero (L.isZero_of_isStrictlyLE b i hi)

/-- On bounded-above complexes, the original sheafified singular construction
preserves the given quasi-isomorphism. -/
theorem singularSheafTotalFunctor_quasiIso
    {K L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ} (f : K ⟶ L)
    (b : ℤ) [K.IsStrictlyLE b] [L.IsStrictlyLE b] [QuasiIso f] :
    QuasiIso ((singularSheafTotalFunctor k).map f) := by
  let : QuasiIso ((singularTotalFunctor k).map f) := singularTotalFunctor_quasiIso f b
  change QuasiIso (((nisnevichSheafify k).mapHomologicalComplex c).map
    ((singularTotalFunctor k).map f))
  infer_instance

/-- Homotopies of the actual coefficient maps induce homotopies of their
sheafified total maps. -/
def singularSheafTotalHomotopy
    {K L : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ} {f g : K ⟶ L}
    (h : Homotopy f g) :
    Homotopy ((singularSheafTotalFunctor k).map f) ((singularSheafTotalFunctor k).map g) :=
  (nisnevichSheafify k).mapHomotopy
    (HomologicalComplex₂.totalMapHomotopy₁ ((singularCochainFunctor 0).mapHomotopy h) c)

/-- The original coefficient sheaf complex maps to its singular representative. -/
abbrev singularSheafTotalUnit :
    (nisnevichSheafify k).mapHomologicalComplex c ⟶ singularSheafTotalFunctor k :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (singularTotalUnit k) ((nisnevichSheafify k).mapHomologicalComplex c)

variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- Cohomology sheaves of the singular total representative are A¹-invariant. -/
theorem singularSheafTotalDerivedCohomology_isA1Invariant
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) i).obj
      (DerivedCategory.Q.obj ((singularSheafTotalFunctor k).obj K))).obj.IsA1Invariant := by
  let L := (singularTotalFunctor k).obj K
  let N := (singularSheafTotalFunctor k).obj K
  let a := nisnevichSheafify k
  let e₀ := (DerivedCategory.homologyFunctorFactors (SheafWithTransfers.{u + 1} k) i).app N
  let e₁ : N.homology i ≅ a.obj (L.homology i) := (L.sc i).mapHomologyIso a
  let e := (SheafWithTransfers.forget k).mapIso (e₀ ≪≫ e₁)
  exact (nisnevichSheafify_isA1Invariant _
    (singularTotalFunctor_homology_isA1Invariant K b i)).of_iso e.symm

end AlgebraicGeometry.MotivicHomotopy
