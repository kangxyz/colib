/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.PerfectFlatBaseChangePlus
public import Colib.AlgebraicGeometry.ProjectiveLine.PerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.QuasiCompactBounded
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasquePushforwardVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors

/-! # Perfect complexes and projective-line direct image

For a quasi-compact scheme, localization of the full subcategory of perfect complexes
factors through the bounded-below derived category. In this category the flat and self
base-change comparisons are the canonical mates. A termwise flasque bounded-below
perfect complex computes its own derived direct image along the line projection.

* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 09T0](https://stacks.math.columbia.edu/tag/09T0)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.FlasquePushforward

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard

/-- Perfection of a complex means perfection of its localization in the derived category. -/
abbrev perfectComplexes (X : Scheme.{u}) : ObjectProperty (CochainComplex X.Modules ℤ) :=
  RingedSpace.IsPerfectComplex (X := X.toRingedSpace)

/-- The actual localization of perfect complexes on a quasi-compact scheme takes values in
the bounded-below derived category; no bound on the terms of the complex is required. -/
@[expose] def perfectComplexToDerivedPlus (X : Scheme.{u}) [CompactSpace X] :
    (perfectComplexes X).FullSubcategory ⥤ DerivedCategory.Plus X.Modules :=
  ObjectProperty.lift _ ((perfectComplexes X).ι ⋙ DerivedCategory.Q) (fun K ↦ by
    obtain ⟨a, _, ha, _⟩ :=
      Stacks.AlgebraicGeometry.PerfectCohomology.exists_isGE_isLE_of_isPerfect
        X (DerivedCategory.Q.obj K.obj) (K.property.isPerfect)
    exact ⟨a, ha⟩)

/-- After inclusion in the derived category, the lift is the ordinary localization. -/
def perfectComplexToDerivedPlusFactors (X : Scheme.{u}) [CompactSpace X] :
    perfectComplexToDerivedPlus X ⋙ DerivedCategory.Plus.ι ≅
      (perfectComplexes X).ι ⋙ DerivedCategory.Q :=
  ObjectProperty.liftCompιIso ..

instance (S : Scheme.{u}) [CompactSpace S] : CompactSpace (projectiveSpaceOver 1 S) :=
  QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOver 1 S ↘ S)

/-- Flat base change on the original complexes, without changing their representatives. -/
@[expose] def projectiveLinePerfectComplexFlatBaseChangeIso {S T : Scheme.{u}} [CompactSpace S]
    (g : T ⟶ S) [Flat g] :=
  let L := perfectComplexToDerivedPlus (projectiveSpaceOver 1 S)
  let τ := Functor.whiskerLeft L (projectiveLineFlatBaseChangePlus g)
  @asIso _ _ _ _ τ ((NatTrans.isIso_iff_isIso_app τ).mpr fun K ↦ by
    change IsIso ((projectiveLineFlatBaseChangePlus g).app (L.obj K))
    exact isIso_projectiveLineFlatBaseChangePlus g (L.obj K) K.property.isPerfect)

/-- The comparison on perfect complexes is the actual flat base-change mate. -/
theorem projectiveLinePerfectComplexFlatBaseChangeIso_hom_app {S T : Scheme.{u}}
    [CompactSpace S] (g : T ⟶ S) [Flat g]
    (K : (perfectComplexes (projectiveSpaceOver 1 S)).FullSubcategory) :
    (projectiveLinePerfectComplexFlatBaseChangeIso g).hom.app K =
      (projectiveLineFlatBaseChangePlus g).app
        ((perfectComplexToDerivedPlus (projectiveSpaceOver 1 S)).obj K) := rfl

/-- The self-base-change comparison on the original perfect complexes. -/
@[expose] def linePerfectComplexSelfBaseChangeIso (R : CommRingCat.{u}) :=
  let L := perfectComplexToDerivedPlus (projectiveSpaceOver 1 (Spec R))
  let τ := Functor.whiskerLeft L (lineSelfBaseChangePlus R)
  @asIso _ _ _ _ τ ((NatTrans.isIso_iff_isIso_app τ).mpr fun K ↦ by
    change IsIso ((lineSelfBaseChangePlus R).app (L.obj K))
    exact isIso_lineSelfBaseChangePlus R (L.obj K) K.property.isPerfect)

/-- The self-comparison retains the actual self-base-change mate. -/
theorem linePerfectComplexSelfBaseChangeIso_hom_app (R : CommRingCat.{u})
    (K : (perfectComplexes (projectiveSpaceOver 1 (Spec R))).FullSubcategory) :
    (linePerfectComplexSelfBaseChangeIso R).hom.app K =
      (lineSelfBaseChangePlus R).app
        ((perfectComplexToDerivedPlus (projectiveSpaceOver 1 (Spec R))).obj K) := rfl

/-- The ordinary degreewise direct image of a bounded-below termwise flasque perfect complex
along the line projection is perfect. -/
theorem isPerfect_projectiveLinePushforward_of_termwiseFlasque (S : Scheme.{u})
    (K : CochainComplex.Plus (projectiveSpaceOver 1 S).Modules)
    (hK : perfectComplexes (projectiveSpaceOver 1 S) K.obj)
    (hfl : ∀ n, TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf _).obj (K.obj.X n))) :
    perfectComplexes S
      (((Scheme.Modules.pushforward (projectiveSpaceOver 1 S ↘ S)).mapHomologicalComplex
        (.up ℤ)).obj K.obj) := by
  let f := projectiveSpaceOver 1 S ↘ S
  let F := Scheme.Modules.pushforward f
  have hacyc (n : ℤ) : F.rightAcyclic (K.obj.X n) := by
    apply ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F _).2
      inferInstance).2
    intro i hi
    exact @isZero_rightDerivedPlus_modulePushforward_of_isFlasque _ _ f.toLRSHom.toShHom
        (K.obj.X n) (hfl n) i hi
  let J := (HomotopyCategory.Plus.quotient _).obj K
  have hunit : IsIso (F.rightDerivedFunctorPlusUnith.app J) :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic F J hacyc
  let e := (DerivedCategory.Plus.quotientCompQhIso _).symm.app
      (F.mapCochainComplexPlus.obj K) ≪≫
    DerivedCategory.Plus.Qh.mapIso (F.quotientCompMapHomotopyCategoryPlusIso.symm.app K) ≪≫
    asIso (F.rightDerivedFunctorPlusUnith.app J) ≪≫
    F.rightDerivedFunctorPlus.mapIso ((DerivedCategory.Plus.quotientCompQhIso _).app K)
  have hd := isPerfect_projectiveLineDerivedPushforwardPlus S (DerivedCategory.Plus.Q.obj K)
    hK.isPerfect
  exact RingedSpace.isPerfectComplex_of_isPerfect_representation hd
    ⟨DerivedCategory.Plus.ι.mapIso e⟩

end AlgebraicGeometry.projectiveSpaceOver
