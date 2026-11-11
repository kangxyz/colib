/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseCochainRepresentative
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Stalkwise representatives from functorial K-injective resolutions

Use the chosen Stacks functorial resolution and its natural inclusion.
Under the pointed simplicial-set chain hypothesis, the resulting pointed
cochain representative computes the reduced hypercohomology of the
original coefficient complex.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]
  [IsGrothendieckAbelian.{w} (Sheaf J AddCommGrpCat.{w})]

/-- Apply the pointed cochain representative to the chosen functorial
K-injective resolution of the coefficient complex. -/
abbrev pointedKInjectiveCochainRepresentative (p : ℤ) :
    CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ ⥤ PointedSimplicialPresheaf.{w} C :=
  Stacks.Injectives.kInjectiveResolutionFunctor (Sheaf J AddCommGrpCat.{w}) ⋙
    pointedCochainRepresentative C J p

variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{w})]

private def shiftedKInjectiveResolutionIso (p : ℤ)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) :
    (DerivedCategory.Q.obj K)⟦p⟧ ≅
      (DerivedCategory.Q.obj
        ((Stacks.Injectives.kInjectiveResolutionFunctor
          (Sheaf J AddCommGrpCat.{w})).obj K))⟦p⟧ := by
  let i := (Stacks.Injectives.kInjectiveResolutionInclusion (Sheaf J AddCommGrpCat.{w})).app K
  have : IsIso (DerivedCategory.Q.map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ i).2
      (Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso _ K)
  exact (shiftFunctor _ p).mapIso (asIso (DerivedCategory.Q.map i))

variable [LocallySmall.{w} C] [J.HasEnoughPoints.{w}]

/-- Under the pointed simplicial-set chain hypothesis, the chosen resolution
represents reduced hypercohomology with the original coefficient complex.
Transport in the coefficient is by the inverse of the shifted resolution
inclusion in the derived category. -/
@[no_expose]
def stalkwiseKInjectiveReplacementHomEquiv
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w})
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (X : PointedSimplicialPresheaf.{w} C) :
    ((toStalkwiseHomotopyCategory C J).obj X ⟶
      (toStalkwiseHomotopyCategory C J).obj
        ((pointedKInjectiveCochainRepresentative C J p).obj K)) ≃
      (reducedHypercohomology C J K p).obj (op X) := by
  let R := Stacks.Injectives.kInjectiveResolutionFunctor (Sheaf J AddCommGrpCat.{w})
  exact (stalkwiseCochainRepresentativeHomEquiv C J h p (R.obj K) X).trans
    ((Iso.refl ((reducedDerivedChains C J).obj X)).homCongr
      (shiftedKInjectiveResolutionIso C J p K).symm)

/-- Precomposition with the original pointed map gives the reduced cohomology restriction. -/
theorem stalkwiseKInjectiveReplacementHomEquiv_naturality
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w})
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (a : (toStalkwiseHomotopyCategory C J).obj Y ⟶
      (toStalkwiseHomotopyCategory C J).obj
        ((pointedKInjectiveCochainRepresentative C J p).obj K)) :
    stalkwiseKInjectiveReplacementHomEquiv C J h p K X
        ((toStalkwiseHomotopyCategory C J).map f ≫ a) =
      (reducedHypercohomology C J K p).map f.op
        (stalkwiseKInjectiveReplacementHomEquiv C J h p K Y a) := by
  let R := Stacks.Injectives.kInjectiveResolutionFunctor (Sheaf J AddCommGrpCat.{w})
  let e := shiftedKInjectiveResolutionIso C J p K
  let Q := toStalkwiseHomotopyCategory C J
  let D := reducedDerivedChains C J
  rw [reducedHypercohomology_map_apply]
  change 𝟙 _ ≫ stalkwiseCochainRepresentativeHomEquiv C J h p (R.obj K) X
      (Q.map f ≫ a) ≫ e.inv =
    D.map f ≫ 𝟙 _ ≫ stalkwiseCochainRepresentativeHomEquiv C J h p (R.obj K) Y a ≫ e.inv
  rw [stalkwiseCochainRepresentativeHomEquiv_naturality]
  simp only [Category.id_comp, reducedHypercohomology_map_apply]
  exact Category.assoc _ _ _

/-- The original resolution inclusion carries the represented class to the
class computed directly with the chosen K-injective coefficient. -/
theorem stalkwiseKInjectiveReplacementHomEquiv_comp_inclusion
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w})
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (X : PointedSimplicialPresheaf.{w} C)
    (f : (toStalkwiseHomotopyCategory C J).obj X ⟶
      (toStalkwiseHomotopyCategory C J).obj
        ((pointedKInjectiveCochainRepresentative C J p).obj K)) :
    ((reducedHypercohomologyCoefficientMap C J p
      ((Stacks.Injectives.kInjectiveResolutionInclusion (Sheaf J AddCommGrpCat.{w})).app K)).app
        (op X)) (stalkwiseKInjectiveReplacementHomEquiv C J h p K X f) =
      stalkwiseCochainRepresentativeHomEquiv C J h p
        ((Stacks.Injectives.kInjectiveResolutionFunctor
          (Sheaf J AddCommGrpCat.{w})).obj K) X f := by
  let R := Stacks.Injectives.kInjectiveResolutionFunctor (Sheaf J AddCommGrpCat.{w})
  let e := shiftedKInjectiveResolutionIso C J p K
  let a : (reducedDerivedChains C J).obj X ⟶ (DerivedCategory.Q.obj (R.obj K))⟦p⟧ :=
    stalkwiseCochainRepresentativeHomEquiv C J h p (R.obj K) X f
  rw [reducedHypercohomologyCoefficientMap_app_apply]
  change (𝟙 _ ≫ a ≫ e.inv) ≫ e.hom = a
  simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.PointedSimplicialPresheaf
