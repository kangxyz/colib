/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TatePowerFiniteBond
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.IntegralCoefficientSuspension

/-!
# Tate suspension with finite motivic coefficients

The integral Tate suspension calculation applies to the original signed
map of multiplication cones and the underlying ordinary coefficient complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe u w₁ w₂ w₃ w₄ w₅

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]
  [HasDerivedCategory.{w₃}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Rₖ" => CommRingCat.of k
local notation "Sₖ" => Spec Rₖ
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ

local notation "E" => motivicReducedDerivedChains k
local notation "N" => reducedTorusSectionsDerivedFunctor k
local notation "F" =>
  (Functor.mapDerivedCategory (toSheaf k) :
    DerivedCategory (LargeSheaves k) ⥤ DerivedCategory (Sheaf Jₖ (LargeAb k)))
local notation "Qₜ" =>
  (DerivedCategory.Q : CochainComplex (LargeSheaves k) ℤ ⥤ DerivedCategory (LargeSheaves k))

omit [HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})] in
/-- The finite coefficient isomorphism is induced by the actual
map of the original multiplication cones. -/
def finiteTorusBondIso (q n : ℕ) :
    (Qₜ).obj (motivicFiniteComplex k q n) ≅
      (N).obj ((Qₜ).obj ((motivicFiniteComplex k (q + 1) n)⟦(1 : ℤ)⟧)) :=
  @asIso _ _ _ _ (motivicDerivedReducedFiniteTransferParameterProduct k q n)
    (isIso_motivicDerivedReducedFiniteTransferParameterProduct k q n
      (isIso_motivicDerivedReducedTransferParameterProduct k q))

/-- The same Tate suspension uses the original finite coefficient cone and its signed map. -/
@[no_expose]
def finiteTateSuspensionHomEquiv (X : PointedSimplicialPresheaf.{u + 1} Cₖ)
    (m : ℤ) (q n : ℕ) :
    ((E).obj X ⟶ (DerivedCategory.Q.obj (motivicFiniteSheafComplex k q n))⟦m⟧) ≃
      ((E).obj (Under.smash X (liftedTateSphere Rₖ)) ⟶
        (DerivedCategory.Q.obj (motivicFiniteSheafComplex k (q + 1) n))⟦m + 2⟧) := by
  let K := motivicFiniteComplex k q n
  let L := motivicFiniteComplex k (q + 1) n
  let D := DerivedCategory (Sheaf Jₖ (LargeAb k))
  let Q₀ : CochainComplex (Sheaf Jₖ (LargeAb k)) ℤ ⥤ D := DerivedCategory.Q
  let s := shiftFunctor D m
  let t := shiftFunctor D (m + 1)
  let L₀ := Q₀.obj (motivicFiniteSheafComplex k (q + 1) n)
  let e₁ := s.mapIso (ordinaryCoefficientDerivedIso k K ≪≫
    Q₀.mapIso (motivicFiniteComplexUnderlyingIso k q n))
  let F₀ := (toSheaf k).mapHomologicalComplex (.up ℤ)
  let e₂ := ordinaryCoefficientDerivedIso k (L⟦(1 : ℤ)⟧) ≪≫
    Q₀.mapIso ((F₀.commShiftIso (1 : ℤ)).app L) ≪≫
    (Q₀.commShiftIso (1 : ℤ)).app (F₀.obj L) ≪≫
    (shiftFunctor D (1 : ℤ)).mapIso (Q₀.mapIso (motivicFiniteComplexUnderlyingIso k (q + 1) n))
  let e₃ := t.mapIso e₂ ≪≫
    ((shiftFunctorAdd' D 1 (m + 1) (m + 2) (by omega)).app L₀).symm
  have h (i : ℤ) := subsingleton_derivedHom_smashPointedAffineLine k
    (motivicFiniteSheafComplex k (q + 1) n) i (motivicFiniteAffineLineRepresentative k i (q + 1) n)
    (motivicFiniteAffineLineRepresentativeHomEquiv k i (q + 1) n) X
  let Y := (E).obj (Under.smash X (liftedPointedAffineLine Rₖ))
  let b := e₃.homToEquiv (Z := Y)
  let b' := e₃.homToEquiv (Z := Y⟦(1 : ℤ)⟧)
  let : Subsingleton (Y ⟶ L₀⟦m + 2⟧) := h (m + 2)
  let : Subsingleton (Y⟦(1 : ℤ)⟧ ⟶ L₀⟦m + 2⟧) :=
    subsingleton_shiftedHom_of_subsingleton _ _ (m + 2) (h (m + 2 - 1))
  exact e₁.symm.homToEquiv.trans
    ((tateSuspensionDerivedHomEquiv k X m (finiteTorusBondIso k q n)
      b.injective.subsingleton b'.injective.subsingleton).trans
        e₃.homToEquiv)

/-- Finite suspension commutes with the same original pointed restriction. -/
theorem finiteTateSuspensionHomEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y) (m : ℤ) (q n : ℕ)
    (g : (E).obj Y ⟶ (DerivedCategory.Q.obj (motivicFiniteSheafComplex k q n))⟦m⟧) :
    finiteTateSuspensionHomEquiv k X m q n ((E).map f ≫ g) =
      (E).map (Under.smashMap f (𝟙 (liftedTateSphere Rₖ))) ≫
        finiteTateSuspensionHomEquiv k Y m q n g := by
  unfold finiteTateSuspensionHomEquiv
  simp only [Equiv.trans_apply, Iso.homToEquiv_apply]
  exact tateSuspensionDerivedHomEquiv_congr_precomp k f m (finiteTorusBondIso k q n)
    _ _ _ _ _ _ g

end AlgebraicGeometry.MotivicHomotopy
