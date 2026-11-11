/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.PicardRoot
public import Colib.Util.References
public import Colib.AlgebraicGeometry.GroupScheme.AbelianVariety.SeparablyClosedPoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPointGroup
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardFunctorRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories

/-!
# Tensor roots of degree-zero invertible modules on a closed curve

For a smooth proper curve over a separably closed field, native Jacobian and point-lifting
theorems supply an actual invertible module and a tensor-power isomorphism.
The native degree and Kummer constructions use two Picard models. We transport through
`Stacks.GluePicard.picardModelAddEquiv`, which preserves the class of the original module,
rather than identifying those models definitionally.

The degree-zero hypothesis concerns the specified module. This result does not yet identify
that module with a difference of section divisors.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- Degree-zero Picard classes on a smooth proper curve over a separably closed field are
divisible by every natural number invertible in the field. All Jacobian and representability
inputs are supplied by the native curve theorems. -/
theorem exists_nsmul_eq_of_mem_picardDegreeZero_of_isSepClosed
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [IsCurve k q] [Smooth q] [IsProper q]
    (hdim : topologicalKrullDim X ≤ 1) {n : ℕ} (hn : IsUnit (n : k))
    (x : picardDegreeZero k q hdim) :
    ∃ y : picardDegreeZero k q hdim, n • y = x := by
  let S₀ : Set Scheme.{u} := {X, Spec (.of k)}
  have : Small.{u} S₀ := by dsimp [S₀]; infer_instance
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  have hX : B.Contains X := hB X (by simp [S₀])
  have hk : B.Contains (Spec (.of k)) := hB _ (by simp [S₀])
  let f : B.obj hX ⟶ B.obj hk := ObjectProperty.homMk q
  have : IsCurve k (B.inclusion.map f) := ‹IsCurve k q›
  have : Smooth (B.inclusion.map f) := ‹Smooth q›
  have : IsProper (B.inclusion.map f) := ‹IsProper q›
  have : GeometricallyIrreducible (B.inclusion.map f) :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X q
  have hproj : IsProjectiveMorphism (B.inclusion.map f) :=
    isProjectiveMorphism_of_isProper_of_isCurve k q
  have : IsProjectiveVariety k (B.inclusion.map f) :=
    (isProjectiveVariety_iff_isProjectiveMorphism k q).2 hproj
  obtain ⟨σ, hσ⟩ := Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed k q
  have := Stacks.RigidifiedPicard.isRepresentable_picardFunctor_of_isSepClosed k B hX hk f hproj
  have := Stacks.PicardFunctor.isAbelianVariety_jacobian B hX hk f σ hσ
  let J := (Stacks.PicardFunctor.jacobianGrp B hX hk f σ hσ).X
  let E := Stacks.PicardFunctor.jacobianPointsAddEquiv B hX hk f σ hσ hdim
  obtain ⟨b, hb⟩ := Stacks.Groupoids.exists_nsmul_eq_of_isUnit_of_isSepClosed J n hn (E.symm x)
  exact ⟨E b, by rw [← map_nsmul, hb, AddEquiv.apply_symm_apply]⟩

end AlgebraicGeometry

namespace Stacks.Kummer

/-- On a smooth proper curve over a separably closed field, every degree-zero invertible
module has an ordinary tensor root for every natural exponent invertible in the field. -/
@[colib_tag "COL-1034", stacks 03RP
  "Degree-zero Picard divisibility on a smooth proper curve, transported to an actual tensor root",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/PicardScheme/CurvePicard/JacobianPointGroup.lean:375-381"
    "ingredient" "Native additive identification of Jacobian points with degree-zero Picard classes",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/PicardScheme/Jacobian/PicardFunctorRepresentable.lean:211-234"
    "ingredient" "Unconditional Picard representability over a separably closed field",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/GroupScheme/AbelianVariety/SeparablyClosedDivisiblePoints.lean:113-129"
    "ingredient" "Lifting rational points along multiplication over a separably closed field",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/GroupScheme/AbelianVariety/ZPowEtaleOfIsUnit.lean:197-199"
    "ingredient" "The native etaleness theorem discharges the point-lifting criterion",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Curves/GlueingSquishing/GlueingPicardSequence.lean:165-190"
    "ingredient" "Additive model equivalence preserving the class of the same invertible module"]
theorem exists_schemeTensorPower_iso_of_picardDegree_eq_zero
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [IsCurve k q] [Smooth q] [IsProper q]
    {n : ℕ} (hn : IsUnit (n : k))
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hdeg : picardDegree k q (IsCurve.topologicalKrullDim_eq_one (k := k) (f := q)).le
      (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace (X.picardClass L hL)) = 0) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅ L) := by
  let e := Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
  let hdim := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := q)).le
  have hx : e (X.picardClass L hL) ∈ picardDegreeZero k q hdim := hdeg
  obtain ⟨y, hy⟩ :=
    AlgebraicGeometry.exists_nsmul_eq_of_mem_picardDegreeZero_of_isSepClosed q hdim hn
    ⟨e (X.picardClass L hL), hx⟩
  apply exists_schemeTensorPower_iso_of_picard_nsmul X n L hL
  refine ⟨e.symm (y : schemePicard X), ?_⟩
  apply e.injective
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  exact congrArg (fun z : picardDegreeZero k q hdim => (z : schemePicard X)) hy

end Stacks.Kummer
