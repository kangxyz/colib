/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.TorusHigherImage
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.HasRightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleCollapseViaPlus
import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction
import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison

/-!
# Acyclic coefficients for the actual derived torus functor

The torus sections functor is left exact on transfer sheaves. The positive
right-derived vanishing therefore identifies the genuine total right-derived
functor on each A¹-invariant sheaf placed in one degree. Bounded truncation
triangles retain the upper bound on a finite interval of such cohomology.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

instance torusSectionsFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (torusSectionsFunctor k :
      SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k) := by
  let U : SheafWithTransfers.{u + 1} k ⥤ ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    SheafWithTransfers.forget k ⋙ PresheafWithTransfers.forget
  let e : U.FullyFaithful :=
    (ObjectProperty.fullyFaithfulι (PresheafWithTransfers.IsNisnevichSheaf k)).comp
      (ObjectProperty.fullyFaithfulι (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1}))
  let : U.Full := e.full
  let : U.Faithful := e.faithful
  let hU : ReflectsLimitsOfSize.{0, 0} U := fullyFaithful_reflectsLimits U
  let : ReflectsFiniteLimits U := { reflects J _ _ := hU.reflectsLimitsOfShape (J := J) }
  have : PreservesFiniteLimits (torusSectionsFunctor k ⋙ U) := by
    change PreservesFiniteLimits (U ⋙ (Functor.whiskeringLeft _ _ _).obj
      (Cor.parameterProduct (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (torusSectionsFunctor k) U

variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- The actual total-derived unit identifies a right-acyclic coefficient in
one cochain degree with the original underived torus sections. -/
def torusSectionsDerivedSingleIso (F : SheafWithTransfers.{u + 1} k)
    (hF : (torusSectionsFunctor k).rightAcyclic F) (n : ℤ) :
    (torusSectionsDerivedFunctor k).obj ((DerivedCategory.singleFunctor _ n).obj F) ≅
      (DerivedCategory.singleFunctor _ n).obj ((torusSectionsFunctor k).obj F) := by
  let b : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k := torusSectionsFunctor k
  let R := torusSectionsDerivedFunctor k
  let α := Stacks.Injectives.homotopyUnitOfComplexUnit b R (torusSectionsDerivedUnit k)
  let e := (DerivedCategory.singleFunctors (SheafWithTransfers.{u + 1} k)).shiftIso
    (-n) n 0 (by omega)
  let e₀ := b.singleCollapseIso R α
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _) F hF
  exact R.mapIso (e.app F).symm ≪≫
    (R.commShiftIso (-n)).app ((DerivedCategory.singleFunctor _ 0).obj F) ≪≫
    (shiftFunctor _ (-n)).mapIso e₀ ≪≫ e.app (b.obj F)

/-- The genuine total derived functor keeps the lower bound, by the
comparison with its bounded-below restriction. -/
theorem torusSectionsDerived_isGE (K : DerivedCategory (SheafWithTransfers.{u + 1} k))
    (a : ℤ) [K.IsGE a] : ((torusSectionsDerivedFunctor k).obj K).IsGE a := by
  let b : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k := torusSectionsFunctor k
  let R := torusSectionsDerivedFunctor k
  let α := Stacks.Injectives.homotopyUnitOfComplexUnit b R (torusSectionsDerivedUnit k)
  let L : DerivedCategory.Plus (SheafWithTransfers.{u + 1} k) := ⟨K, a, inferInstance⟩
  let : L.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff L a).1
    (inferInstanceAs (K.IsGE a))
  let D := DerivedCategory.Plus.ι.obj (b.rightDerivedFunctorPlus.obj L)
  let e : D ≅ R.obj K := (b.boundedDerivedIso R α
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _)).app L
  let : D.IsGE a :=
    (DerivedCategory.Plus.isGE_ι_obj_iff _ a).2 (b.isGE_rightDerivedFunctorPlus_obj L a)
  exact DerivedCategory.TStructure.t.isGE_of_iso e a

/-- A bounded-below complex of torus-acyclic coefficients computes the
actual total derived functor, by its original comparison unit. -/
theorem isIso_torusSectionsDerivedUnit_app_of_rightAcyclic
    (K : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ)
    (hK : CochainComplex.plus _ K)
    (h : ∀ n, (torusSectionsFunctor k).rightAcyclic (K.X n)) :
    IsIso ((torusSectionsDerivedUnit k).app K) := by
  let b : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k := torusSectionsFunctor k
  let R := torusSectionsDerivedFunctor k
  let α := Stacks.Injectives.homotopyUnitOfComplexUnit b R (torusSectionsDerivedUnit k)
  let e₁ := (DerivedCategory.quotientCompQhIso (SheafWithTransfers.{u + 1} k)).hom.app
    ((b.mapHomologicalComplex (.up ℤ)).obj K)
  let e₂ := R.map
    ((DerivedCategory.quotientCompQhIso (SheafWithTransfers.{u + 1} k)).inv.app K)
  have hu := Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic b R α K hK h
  let : IsIso (e₁ ≫ (torusSectionsDerivedUnit k).app K ≫ e₂) := by
    simpa only [α, Stacks.Injectives.homotopyUnitOfComplexUnit_app_quotient, e₁, e₂] using hu
  let : IsIso ((torusSectionsDerivedUnit k).app K ≫ e₂) :=
    IsIso.of_isIso_comp_left e₁ _
  exact IsIso.of_isIso_comp_right _ e₂

variable [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- An A¹-invariant transfer sheaf over a perfect field is right acyclic for
the genuine torus sections functor. -/
theorem torusSectionsFunctor_rightAcyclic_of_perfect (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) : (torusSectionsFunctor k).rightAcyclic F := by
  apply (CategoryTheory.rightAcyclic_iff_isZero_rightDerived (torusSectionsFunctor k) F).2
  intro p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  exact torusSectionsRightDerived_isZero_succ_of_perfect k F hF n

/-- On a finite cohomological interval with A¹-invariant cohomology sheaves,
the actual derived torus functor retains the original upper bound. -/
theorem torusSectionsDerived_isLE_of_isGE_of_isLE (K :
    DerivedCategory (SheafWithTransfers.{u + 1} k)) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor _ n).obj K).obj.IsA1Invariant) :
    ((torusSectionsDerivedFunctor k).obj K).IsLE b := by
  let B : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k := torusSectionsFunctor k
  let P := B.rightAcyclic
  let : P.ContainsZero := ⟨by
    refine ⟨0, isZero_zero _, (CategoryTheory.rightAcyclic_iff_isZero_rightDerived B 0).2 ?_⟩
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact B.isZero_rightDerived_obj_injective_succ m 0⟩
  have hSingle (F : SheafWithTransfers.{u + 1} k) (hF : P F) (n : ℤ) :
      ((torusSectionsDerivedFunctor k).obj ((DerivedCategory.singleFunctor _ n).obj F)).IsLE
        (n + 0) := by
    rw [add_zero]
    exact DerivedCategory.TStructure.t.isLE_of_iso
      (torusSectionsDerivedSingleIso k F hF n).symm n
  simpa only [add_zero] using Stacks.SmallDerivedCategory.isLE_obj_of_isGE_of_isLE P
    (torusSectionsDerivedFunctor k) 0 hSingle K
    (fun n => torusSectionsFunctor_rightAcyclic_of_perfect k _ (hK n)) a b

end AlgebraicGeometry.SheafWithTransfers
