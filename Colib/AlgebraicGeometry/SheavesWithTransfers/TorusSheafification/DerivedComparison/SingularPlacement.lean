/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedWindow
import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# The original singular torus map and the natural derived comparison

Extension by zero retains the signed permutation of the raw singular
complex and the termwise sheafification map. The corresponding derived
comparison uses the same total right-derived unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers
open Stacks.DerivedIndexing

variable (k : Type u) [Field k]

private theorem mapExtendIso_hom_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [HasZeroObject A] [HasZeroObject B] [HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex A c) :
    (mapExtendIso (F ⋙ G) e K).hom =
      (mapExtendIso G e ((F.mapHomologicalComplex c).obj K)).hom ≫
        (G.mapHomologicalComplex c').map (mapExtendIso F e K).hom := by
  ext i' : 1
  change (mapExtendXIso (F ⋙ G) K (e.r i')).hom =
    (mapExtendXIso G ((F.mapHomologicalComplex c).obj K) (e.r i')).hom ≫
      G.map ((mapExtendXIso F K (e.r i')).hom)
  generalize e.r i' = j
  cases j with
  | none => exact (HomologicalComplex.extend.isZero_X _ rfl).eq_of_src _ _
  | some j =>
    simp only [mapExtendXIso, Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

/-- The original signed parameter permutation in the actual weight-zero
cochain placement. -/
def singularCochainTorusParameterIso (P : PresheafWithTransfers.{u + 1} k) :
    singularCochainComplex (torusSections P) 0 ≅
      ((torusSectionsPresheafFunctor k).mapHomologicalComplex (.up ℤ)).obj
        (singularCochainComplex P 0) :=
  let e := ComplexShape.embeddingUpIntLE 0
  let G := SmoothSite.multiplicativeGroupObject (Spec (.of k))
  (e.extendFunctor _).mapIso (withParameterSingularComplexIso P G).symm ≪≫
    mapExtendIso (torusSectionsPresheafFunctor k) e (singularComplex P)

/-- The original sheafified singular cochain comparison first sheafifies
the placed signed permutation, then applies the actual termwise map. -/
theorem singularSheafCochainTorusSectionsMap_eq_placed
    (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafCochainTorusSectionsMap k P =
      ((nisnevichSheafify k).mapHomologicalComplex (.up ℤ)).map
          (singularCochainTorusParameterIso k P).hom ≫
        torusSectionsSheafificationComplexMap k (.up ℤ) (singularCochainComplex P 0) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let T := torusSectionsPresheafFunctor k
  let A := nisnevichSheafify k
  let B := torusSectionsFunctor k
  let K := singularComplex P
  let L := singularComplex (torusSections P)
  let A₀ := A.mapHomologicalComplex (.down ℕ)
  let A₁ := A.mapHomologicalComplex (.up ℤ)
  let B₁ := B.mapHomologicalComplex (.up ℤ)
  let D := e.extendFunctor (PresheafWithTransfers.{u + 1} k)
  let E := e.extendFunctor (SheafWithTransfers.{u + 1} k)
  let G := SmoothSite.multiplicativeGroupObject (Spec (.of k))
  let σ : L ⟶ (T.mapHomologicalComplex (.down ℕ)).obj K :=
    (withParameterSingularComplexIso P G).inv
  let aL := mapExtendIso A e L
  let aK := mapExtendIso A e K
  let aT := mapExtendIso A e ((T.mapHomologicalComplex (.down ℕ)).obj K)
  let bA := mapExtendIso B e (A₀.obj K)
  let tK := mapExtendIso T e K
  let τ₀ := torusSectionsSheafificationComplexMap k (.down ℕ) K
  let τ₁ := torusSectionsSheafificationComplexMap k (.up ℤ) (D.obj K)
  have hσ : aL.inv ≫ E.map (A₀.map σ) = A₁.map (D.map σ) ≫ aT.inv :=
    ((mapExtendNatIso A e).inv.naturality σ).symm
  have hτ : E.map τ₀ ≫ bA.hom ≫ B₁.map aK.hom =
      aT.hom ≫ A₁.map tK.hom ≫ τ₁ := by
    have hh := mapExtendIso_hom_natTrans (torusSectionsSheafificationNatTrans k) e K
    simp only [mapExtendIso_hom_comp, Category.assoc] at hh
    exact hh
  change aL.inv ≫ E.map (A₀.map σ ≫ τ₀) ≫ bA.hom ≫ B₁.map aK.hom =
    A₁.map (D.map σ ≫ tK.hom) ≫ τ₁
  calc
    _ = (aL.inv ≫ E.map (A₀.map σ)) ≫ (E.map τ₀ ≫ bA.hom ≫ B₁.map aK.hom) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [hσ, hτ]
      simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

/-- The source of the original singular comparison is the source of the
natural derived comparison via the actual signed permutation. -/
def singularDerivedTorusComparisonSourceIso (P : PresheafWithTransfers.{u + 1} k) :
    DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0) ≅
      ((torusSectionsPresheafFunctor k).mapDerivedCategory ⋙
        (nisnevichSheafify k).mapDerivedCategory).obj
          (DerivedCategory.Q.obj (singularCochainComplex P 0)) :=
  let T := torusSectionsPresheafFunctor k
  let A := nisnevichSheafify k
  let K := singularCochainComplex P 0
  let T₁ := T.mapHomologicalComplex (.up ℤ)
  let e := A.mapDerivedCategory.mapIso (T.mapDerivedCategoryFactors.app K) ≪≫
    A.mapDerivedCategoryFactors.app (T₁.obj K)
  DerivedCategory.Q.mapIso ((A.mapHomologicalComplex (.up ℤ)).mapIso
    (singularCochainTorusParameterIso k P)) ≪≫ e.symm

/-- The natural derived comparison is the original singular torus map
under the actual source and target identifications. -/
theorem singularSheafDerivedTorusSectionsMap_eq_comparison
    (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafDerivedTorusSectionsMap k P =
      (singularDerivedTorusComparisonSourceIso k P).hom ≫
        (torusSectionsDerivedSheafificationComparison k).app
          (DerivedCategory.Q.obj (singularCochainComplex P 0)) ≫
        (torusSectionsDerivedFunctor k).map
          ((nisnevichSheafify k).mapDerivedCategoryFactors.hom.app
            (singularCochainComplex P 0)) := by
  let T := torusSectionsPresheafFunctor k
  let A := nisnevichSheafify k
  let R := torusSectionsDerivedFunctor k
  let K := singularCochainComplex P 0
  let e := A.mapDerivedCategory.mapIso (T.mapDerivedCategoryFactors.app K) ≪≫
    A.mapDerivedCategoryFactors.app ((T.mapHomologicalComplex (.up ℤ)).obj K)
  let Q : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ ⥤
      DerivedCategory (SheafWithTransfers.{u + 1} k) := DerivedCategory.Q
  let eA := A.mapDerivedCategoryFactors.app K
  let σ := ((A.mapHomologicalComplex (.up ℤ)).mapIso (singularCochainTorusParameterIso k P)).hom
  let τ := torusSectionsSheafificationComplexMap k (.up ℤ) K
  let v := (torusSectionsDerivedUnit k).app (((A.mapHomologicalComplex (.up ℤ)).obj K))
  have hη :
      (torusSectionsDerivedSheafificationComparison k).app (DerivedCategory.Q.obj K) =
        e.hom ≫ Q.map τ ≫ v ≫ R.map eA.inv := by
    exact (torusSectionsDerivedSheafificationComparison_app_Q_obj k K).trans
      (by simp only [e, eA, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]; rfl)
  rw [hη, singularSheafDerivedTorusSectionsMap, singularSheafCochainTorusSectionsMap_eq_placed]
  change Q.map (σ ≫ τ) ≫ v = (Q.map σ ≫ e.inv) ≫
    (e.hom ≫ Q.map τ ≫ v ≫ R.map eA.inv) ≫ R.map eA.hom
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  have hId : R.map eA.inv ≫ R.map eA.hom = 𝟙 _ :=
    (R.map_comp eA.inv eA.hom).symm.trans
      ((congrArg R.map eA.inv_hom_id).trans (R.map_id _))
  let p₀ := Q.map σ ≫ Q.map τ ≫ v
  calc
    _ = p₀ := rfl
    _ = p₀ ≫ 𝟙 (R.obj (Q.obj ((A.mapHomologicalComplex (.up ℤ)).obj K))) :=
      (Category.comp_id p₀).symm
    _ = p₀ ≫ (R.map eA.inv ≫ R.map eA.hom) := congrArg (p₀ ≫ ·) hId.symm
    _ = _ := by simp only [p₀, Category.assoc]

end AlgebraicGeometry.SheafWithTransfers
