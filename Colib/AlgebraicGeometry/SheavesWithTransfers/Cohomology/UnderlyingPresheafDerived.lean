/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.UnderlyingComplexAcyclic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedForgetComparison
public import StacksFrontier.Homology.DerivedCategory.RightDerivedExactChange

/-!
# Derived forget and ordinary Nisnevich presheaves

Restrict the original transfer presheaf along the graph functor. The
comparison of the two derived forget functors comes from the original
underlying-presheaf isomorphism and its acyclicity on transfer-injective
resolutions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open Stacks.DerivedSquare
open Stacks.Injectives.KInjectiveResolution

universe u w₁ w₂ w₃ w₄

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "J" => SmoothSite.nisnevichTopology S
local notation "A" => LargeAb k
local notation "V" => PresheafWithTransfers.toPresheaf k
local notation "F" => toSheaf k
local notation "U" => sheafToPresheaf J A
local notation "c" => ComplexShape.up ℤ

variable [HasDerivedCategory.{w₃}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]

/-- Apply ordinary underlying presheaves to the original complex and localize. -/
abbrev ordinaryPresheafComplexToDerived :
    CochainComplex (Sheaf J A) ℤ ⥤ DerivedCategory ((SmoothSite S)ᵒᵖ ⥤ A) :=
  (U).mapHomologicalComplex c ⋙ DerivedCategory.Q

instance : (ordinaryPresheafComplexToDerived k).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf J A) c) :=
  hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (U)

/-- Derived ordinary presheaves of a complex of ordinary Nisnevich sheaves. -/
@[no_expose]
def ordinaryPresheafDerivedFunctor :
    DerivedCategory (Sheaf J A) ⥤ DerivedCategory ((SmoothSite S)ᵒᵖ ⥤ A) :=
  (ordinaryPresheafComplexToDerived k).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf J A) c)

/-- The original cochain comparison for derived ordinary presheaves. -/
@[no_expose]
def ordinaryPresheafDerivedUnit :
    ordinaryPresheafComplexToDerived k ⟶ DerivedCategory.Q ⋙ ordinaryPresheafDerivedFunctor k :=
  (ordinaryPresheafComplexToDerived k).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf J A) c)

instance : (ordinaryPresheafDerivedFunctor k).IsRightDerivedFunctor
    (ordinaryPresheafDerivedUnit k) (HomologicalComplex.quasiIso (Sheaf J A) c) := by
  dsimp only [ordinaryPresheafDerivedFunctor, ordinaryPresheafDerivedUnit]
  infer_instance

private theorem isIso_ordinaryPresheafDerivedUnit_app_of_injectiveTerms
    (I : CochainComplex (LargeSheaves k) ℤ) (hI : ∀ i, Injective (I.X i)) :
    IsIso ((ordinaryPresheafDerivedUnit k).app (((F).mapHomologicalComplex c).obj I)) := by
  let K := ((F).mapHomologicalComplex c).obj I
  obtain ⟨L, a, hL, ha⟩ :=
    Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian (Sheaf J A) K
  let : QuasiIso a := ha
  apply isIso_app_of_quasiIso_resolution DerivedCategory.Q (ordinaryPresheafDerivedFunctor k)
    (ordinaryPresheafDerivedUnit k) (invertsQuasiIso_mapHomologicalComplex_comp_Q (U)) a hL ha
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_underlyingPresheaf_of_injectiveTerms k I hI a hL)

variable [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]

instance toPresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafWithTransfers.toPresheaf.{u + 1} k) :=
  ⟨fun _ _ _ => inferInstance⟩

instance toPresheaf_preservesFiniteColimits :
    PreservesFiniteColimits (PresheafWithTransfers.toPresheaf.{u + 1} k) :=
  ⟨fun _ _ _ => inferInstance⟩

omit [HasDerivedCategory (LargePresheaves k)] [HasDerivedCategory (LargeSheaves k)] in
private theorem isIso_ordinaryPresheafDerivedUnit_app_of_isKInjective
    (I : CochainComplex (LargeSheaves k) ℤ) (hI : I.IsKInjective) :
    IsIso ((ordinaryPresheafDerivedUnit k).app (((F).mapHomologicalComplex c).obj I)) := by
  let L := (Stacks.Injectives.kInjectiveResolutionFunctor (LargeSheaves k)).obj I
  let a := (Stacks.Injectives.kInjectiveResolutionInclusion (LargeSheaves k)).app I
  have ha : QuasiIso a := inferInstanceAs
    (QuasiIso ((Stacks.Injectives.kInjectiveResolutionInclusion (LargeSheaves k)).app I))
  let f := ((F).mapHomologicalComplex c).map a
  have hf : QuasiIso f := quasiIso_mapHomologicalComplex_map_of_isKInjective (F) a hI
    (inferInstanceAs
      (((Stacks.Injectives.kInjectiveResolutionFunctor (LargeSheaves k)).obj I).IsKInjective)) ha
  let : QuasiIso f := hf
  let : IsIso ((ordinaryPresheafComplexToDerived k).map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_mapHomologicalComplex_map_of_isKInjective ((F) ⋙ U) a hI
        (inferInstanceAs
          (((Stacks.Injectives.kInjectiveResolutionFunctor (LargeSheaves k)).obj I).IsKInjective))
        ha)
  let : IsIso ((ordinaryPresheafDerivedUnit k).app (((F).mapHomologicalComplex c).obj L)) :=
    isIso_ordinaryPresheafDerivedUnit_app_of_injectiveTerms k L
      (fun i => inferInstanceAs
        (Injective (((Stacks.Injectives.kInjectiveResolutionFunctor (LargeSheaves k)).obj I).X i)))
  let α := ordinaryPresheafDerivedUnit k
  let b := (DerivedCategory.Q ⋙ ordinaryPresheafDerivedFunctor k).map f
  let : IsIso b := inferInstanceAs
    (IsIso ((ordinaryPresheafDerivedFunctor k).map (DerivedCategory.Q.map f)))
  let : IsIso (α.app (((F).mapHomologicalComplex c).obj I) ≫ b) :=
    α.naturality f ▸ inferInstance
  exact IsIso.of_isIso_comp_right _ b

/-- Forgetting the derived transfer presheaf along graphs recovers derived
ordinary presheaves of the actual underlying Nisnevich sheaf. -/
@[no_expose]
def forgetDerivedOrdinaryPresheafIso :
    forgetDerivedFunctor k ⋙ (V).mapDerivedCategory ≅
      (F).mapDerivedCategory ⋙ ordinaryPresheafDerivedFunctor k :=
  rightDerivedExactChangeIso (forget k) (U) (F) (V)
    (forgetDerivedFunctor k) (forgetDerivedUnit k)
    (ordinaryPresheafDerivedFunctor k) (ordinaryPresheafDerivedUnit k)
    (toSheafCompSheafToPresheafIso k).symm
    (isIso_ordinaryPresheafDerivedUnit_app_of_isKInjective k)

/-- On complexes the ordinary-presheaf comparison uses the original
underlying-presheaf identification and both genuine derived units. -/
theorem forgetDerivedOrdinaryPresheafIso_hom_fac
    (K : CochainComplex (LargeSheaves k) ℤ) :
    (exactChangeUnitDerivedFirst (forget k) (V) (forgetDerivedFunctor k)
      (forgetDerivedUnit k)).app K ≫
        (forgetDerivedOrdinaryPresheafIso k).hom.app (DerivedCategory.Q.obj K) =
      (exactChangeUnitChangeFirst (forget k) (U) (F) (V) (ordinaryPresheafDerivedFunctor k)
        (ordinaryPresheafDerivedUnit k) (toSheafCompSheafToPresheafIso k).symm).app K := by
  unfold forgetDerivedOrdinaryPresheafIso
  exact rightDerivedExactChangeIso_hom_fac (forget k) (U) (F) (V)
    (forgetDerivedFunctor k) (forgetDerivedUnit k)
    (ordinaryPresheafDerivedFunctor k) (ordinaryPresheafDerivedUnit k)
    (toSheafCompSheafToPresheafIso k).symm
    (isIso_ordinaryPresheafDerivedUnit_app_of_isKInjective k) K

end AlgebraicGeometry.SheafWithTransfers
