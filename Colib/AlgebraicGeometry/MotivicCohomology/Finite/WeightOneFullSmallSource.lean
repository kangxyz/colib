/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallCanonicalSource
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.DerivedRestrictionAtBase

/-! # Full-small transport at the identity neighborhood preserves the original unit -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE Stacks.Cohomology.Corepresented
universe u wN wE wS
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{wE}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : SmoothSite (Spec (.of k)))
variable [HasDerivedCategory.{wS} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Original full-small derived transport at the identity neighborhood retains the unit section. -/
lemma fullSmallUnits_source
    (h : (freeYoneda.{u + 1} (SmoothSite.etaleTopology (Spec (.of k)))).obj X ⟶
      largeUnitsEtaleSheaf (Spec (.of k))) :
    fullSmallDerivedHomMapAtBase X (weightOneEtaleUnitsComplex k) 1
        ((DerivedCategory.singleFunctor _ 0).map h ≫
          (derivedSingleNegOneCancelIso (largeUnitsEtaleSheaf (Spec (.of k)))).inv) ≫
      (DerivedCategory.Q.map (fullSmallEtaleUnitsComplexIso k X).hom)⟦(1 : ℤ)⟧' ≫
      (derivedSingleNegOneCancelIso (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)).hom =
    (DerivedCategory.singleFunctor _ 0).map
      ((sectionsEquiv.{u + 1} (Scheme.Etale.mk (𝟙 X.left))
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)).symm
        (ULift.up (sectionsEquiv.{u + 1} X (largeUnitsEtaleSheaf (Spec (.of k))) h).down)) := by
  let V : EtaleSeparatedFiniteType X.left :=
    MorphismProperty.Over.mk ⊤ (𝟙 X.left) (etaleSeparatedFiniteType.id_mem X.left)
  let g : (toSmoothSite X).obj V ⟶ X := SmoothSite.homMk (𝟙 X.left) (by rfl)
  let a := (freeYoneda.{u + 1} X.left.smallEtaleTopology).map
    (toSmallEtaleIdentityIso X.left).inv
  let b := (freeYoneda.{u + 1} (SmoothSite.etaleTopology (Spec (.of k)))).map g
  have h₂ := (Equiv.eq_symm_apply (sectionsEquiv.{u + 1} (Scheme.Etale.mk (𝟙 X.left))
    (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left))).2 (fullSmallSourceMapAtBase_units X h)
  let DE := DerivedCategory.singleFunctor
    (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) 0
  let DS := DerivedCategory.singleFunctor
    (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  have hb : DE.map b ≫ (DE.map h ≫
      (derivedSingleNegOneCancelIso (largeUnitsEtaleSheaf (Spec (.of k)))).inv) =
      DE.map (b ≫ h) ≫
        (derivedSingleNegOneCancelIso (largeUnitsEtaleSheaf (Spec (.of k)))).inv := by
    rw [Functor.map_comp, Category.assoc]
  change (DS.map a ≫ fullSmallDerivedHomMap X V (weightOneEtaleUnitsComplex k) 1
    (DE.map b ≫ (DE.map h ≫
      (derivedSingleNegOneCancelIso (largeUnitsEtaleSheaf (Spec (.of k)))).inv))) ≫
      (DerivedCategory.Q.map (fullSmallEtaleUnitsComplexIso k X).hom)⟦(1 : ℤ)⟧' ≫
      (derivedSingleNegOneCancelIso (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)).hom = _
  rw [hb, Category.assoc, fullSmallUnits_sourceMap, ← Functor.map_comp]
  exact congrArg DS.map h₂

end AlgebraicGeometry.MotivicCohomology.WeightOne
