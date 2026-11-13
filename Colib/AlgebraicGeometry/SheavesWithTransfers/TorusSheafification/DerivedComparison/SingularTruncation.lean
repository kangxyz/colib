/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.DerivedCategory.ExactFunctorTruncGE
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedTruncation
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.Bounded
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularPlacement
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.HomotopyInvariance

/-!
# The actual derived singular comparison on the finite window

The exact truncation projections and the signed placement identify the
original factorization with the natural derived comparison on the raw
truncated singular complex. Its cohomology coefficients are A¹-invariant.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

/-- Both exact functors commute with the actual lower truncation on the
source of the comparison. -/
def torusSectionsDerivedSheafificationSourceTruncGEIso
    (E : DerivedCategory (PresheafWithTransfers.{u + 1} k)) (a : ℤ) :
    let F := (torusSectionsPresheafFunctor k).mapDerivedCategory ⋙
      (nisnevichSheafify k).mapDerivedCategory
    (DerivedCategory.TStructure.t.truncGE a).obj (F.obj E) ≅
      F.obj ((DerivedCategory.TStructure.t.truncGE a).obj E) :=
  let T := torusSectionsPresheafFunctor k
  let A := nisnevichSheafify k
  A.mapDerivedCategoryTruncGEIso (T.mapDerivedCategory.obj E) a ≪≫
    A.mapDerivedCategory.mapIso (T.mapDerivedCategoryTruncGEIso E a)

/-- The source comparison commutes with the literal lower truncation
projection. -/
@[reassoc]
theorem torusSectionsDerivedSheafificationSourceTruncGEIso_comp
    (E : DerivedCategory (PresheafWithTransfers.{u + 1} k)) (a : ℤ) :
    let F := (torusSectionsPresheafFunctor k).mapDerivedCategory ⋙
      (nisnevichSheafify k).mapDerivedCategory
    (DerivedCategory.TStructure.t.truncGEπ a).app (F.obj E) ≫
        (torusSectionsDerivedSheafificationSourceTruncGEIso k E a).hom =
      F.map ((DerivedCategory.TStructure.t.truncGEπ a).app E) := by
  let T := torusSectionsPresheafFunctor k
  let A := nisnevichSheafify k
  let π := (DerivedCategory.TStructure.t.truncGEπ a).app E
  let X := T.mapDerivedCategory.obj E
  let eA := A.mapDerivedCategoryTruncGEIso X a
  let eT := T.mapDerivedCategoryTruncGEIso E a
  let p := (DerivedCategory.TStructure.t.truncGEπ a).app (A.mapDerivedCategory.obj X)
  change p ≫ (eA.hom ≫ A.mapDerivedCategory.map eT.hom) =
    A.mapDerivedCategory.map (T.mapDerivedCategory.map π)
  calc
    _ = (p ≫ eA.hom) ≫ A.mapDerivedCategory.map eT.hom := (Category.assoc _ _ _).symm
    _ = A.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ a).app X) ≫
        A.mapDerivedCategory.map eT.hom :=
      congrArg (· ≫ A.mapDerivedCategory.map eT.hom)
        (A.truncGEπ_app_comp_mapDerivedCategoryTruncGEIso_hom X a)
    _ = _ := (A.mapDerivedCategory.map_comp _ _).symm.trans
      (congrArg A.mapDerivedCategory.map
        (T.truncGEπ_app_comp_mapDerivedCategoryTruncGEIso_hom E a))

/-- The original singular truncation map agrees with the actual derived
sheafification comparison on the raw singular truncation. -/
theorem singularSheafDerivedTorusSectionsTruncationMap_eq_comparison
    (P : PresheafWithTransfers.{u + 1} k) (a : ℤ) :
    let K := singularCochainComplex P 0
    let E := DerivedCategory.Q.obj K
    let t : Triangulated.TStructure (DerivedCategory (SheafWithTransfers.{u + 1} k)) :=
      DerivedCategory.TStructure.t
    let A := nisnevichSheafify k
    let R := torusSectionsDerivedFunctor k
    let source := (t.truncGE a).mapIso (singularDerivedTorusComparisonSourceIso k P) ≪≫
      torusSectionsDerivedSheafificationSourceTruncGEIso k E a
    let target := R.mapIso ((A.mapDerivedCategoryTruncGEIso E a).symm ≪≫
      (t.truncGE a).mapIso (A.mapDerivedCategoryFactors.app K))
    singularSheafDerivedTorusSectionsTruncationMap k P a =
      source.hom ≫ (torusSectionsDerivedSheafificationComparison k).app
        ((DerivedCategory.TStructure.t.truncGE a).obj E) ≫ target.hom := by
  let K := singularCochainComplex P 0
  let E := DerivedCategory.Q.obj K
  let t : Triangulated.TStructure (DerivedCategory (SheafWithTransfers.{u + 1} k)) :=
    DerivedCategory.TStructure.t
  let T := torusSectionsPresheafFunctor k
  let A := nisnevichSheafify k
  let R := torusSectionsDerivedFunctor k
  let F₁ := T.mapDerivedCategory ⋙ A.mapDerivedCategory
  let F₂ := A.mapDerivedCategory ⋙ R
  let η := torusSectionsDerivedSheafificationComparison k
  let L := (DerivedCategory.TStructure.t.truncGE a).obj E
  let π : E ⟶ L := (DerivedCategory.TStructure.t.truncGEπ a).app E
  let e₀ := singularDerivedTorusComparisonSourceIso k P
  let e₁ := A.mapDerivedCategoryFactors.app K
  let eA := A.mapDerivedCategoryTruncGEIso E a
  let eF := torusSectionsDerivedSheafificationSourceTruncGEIso k E a
  let source := (t.truncGE a).mapIso e₀ ≪≫ eF
  let target := R.mapIso (eA.symm ≪≫ (t.truncGE a).mapIso e₁)
  let E₀ := DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0)
  let E₁ := DerivedCategory.Q.obj (singularSheafCochainComplex k P 0)
  let p₀ := (t.truncGEπ a).app E₀
  let p₁ := (t.truncGEπ a).app E₁
  let : ((t.truncGE a).obj E₁).IsGE a := inferInstance
  let : (R.obj ((t.truncGE a).obj E₁)).IsGE a := torusSectionsDerived_isGE k _ a
  have hSource : p₀ ≫ source.hom = e₀.hom ≫ F₁.map π := by
    change p₀ ≫ ((t.truncGE a).map e₀.hom ≫ eF.hom) = _
    rw [← Category.assoc, t.truncGEπ_naturality, Category.assoc,
      torusSectionsDerivedSheafificationSourceTruncGEIso_comp]
  have hTarget : F₂.map π ≫ target.hom = R.map e₁.hom ≫ R.map p₁ := by
    change R.map (A.mapDerivedCategory.map π) ≫
      R.map (eA.inv ≫ (t.truncGE a).map e₁.hom) = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg R.map
    let q := (t.truncGEπ a).app (A.mapDerivedCategory.obj E)
    let m := (t.truncGE a).map e₁.hom
    change A.mapDerivedCategory.map π ≫ (eA.inv ≫ m) = e₁.hom ≫ p₁
    calc
      _ = (q ≫ eA.hom) ≫ (eA.inv ≫ m) :=
        congrArg (· ≫ (eA.inv ≫ m))
          (A.truncGEπ_app_comp_mapDerivedCategoryTruncGEIso_hom E a).symm
      _ = q ≫ m := by rw [Category.assoc, Iso.hom_inv_id_assoc]
      _ = _ := t.truncGEπ_naturality a e₁.hom
  change singularSheafDerivedTorusSectionsTruncationMap k P a =
    source.hom ≫ η.app L ≫ target.hom
  apply t.from_truncGE_obj_ext
  rw [singularSheafDerivedTorusSectionsTruncationMap_comp]
  symm
  calc
    p₀ ≫ source.hom ≫ η.app L ≫ target.hom =
        (p₀ ≫ source.hom) ≫ η.app L ≫ target.hom :=
      (Category.assoc _ _ _).symm
    _ = e₀.hom ≫ η.app E ≫ (F₂.map π ≫ target.hom) := by
      rw [hSource, Category.assoc, η.naturality_assoc]
    _ = _ := by
      rw [hTarget, singularSheafDerivedTorusSectionsMap_eq_comparison]
      simp only [Category.assoc]
      rfl

omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] in
private theorem singularRawDerivedCohomology_isA1Invariant
    (P : PresheafWithTransfers.{u + 1} k) (i : ℤ) :
    ((DerivedCategory.homologyFunctor _ i).obj
      (DerivedCategory.Q.obj (singularCochainComplex P 0))).IsA1Invariant := by
  let K := singularCochainComplex P 0
  let e := (DerivedCategory.homologyFunctorFactors (PresheafWithTransfers.{u + 1} k) i).app K
  apply IsA1Invariant.of_iso _ e.symm
  by_cases hi : 0 < i
  · exact isA1Invariant_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ (K.sc i)
      (isZero_singularCochainComplex_X P 0 i hi))
  · let r := (-i).toNat
    have hr : (0 : ℤ) - r = i := by omega
    let e' : K.homology i ≅ (singularComplex P).homology r :=
      (singularComplex P).extendHomologyIso (ComplexShape.embeddingUpIntLE 0) hr
    exact (singularComplex_homology_isA1Invariant P r).of_iso e'.symm

variable [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The original singular torus comparison on the lower truncation is
invertible over a perfect field. -/
theorem isIso_singularSheafDerivedTorusSectionsTruncationMap
    (P : PresheafWithTransfers.{u + 1} k) (a : ℤ) :
    IsIso (singularSheafDerivedTorusSectionsTruncationMap k P a) := by
  let E := DerivedCategory.Q.obj (singularCochainComplex P 0)
  let L := (DerivedCategory.TStructure.t.truncGE a).obj E
  let : L.IsGE a := inferInstanceAs (((DerivedCategory.TStructure.t.truncGE a).obj E).IsGE a)
  let : IsIso ((torusSectionsDerivedSheafificationComparison k).app L) :=
    isIso_torusSectionsDerivedSheafificationComparison_app_of_isGE k L
      (isA1Invariant_derivedHomology_truncGE k E
        (singularRawDerivedCohomology_isA1Invariant k P) a) a
  rw [singularSheafDerivedTorusSectionsTruncationMap_eq_comparison]
  infer_instance

/-- At the finite projective-dimension cutoff, the original singular map
followed by the actual derived target projection induces a bijection. -/
theorem singularSheafDerivedTorusSectionsMap_comp_cutoff_bijective
    (P : PresheafWithTransfers.{u + 1} k) (W : SheafWithTransfers.{u + 1} k)
    (d : ℕ) [HasProjectiveDimensionLE W d] (p : ℤ) :
    let a : ℤ := p - (d : ℤ)
    let E := DerivedCategory.Q.obj (singularSheafCochainComplex k (torusSections P) 0)
    let L := DerivedCategory.Q.obj (singularSheafCochainComplex k P 0)
    let R := torusSectionsDerivedFunctor k
    let f := singularSheafDerivedTorusSectionsMap k P ≫
      R.map ((DerivedCategory.TStructure.t.truncGEπ a).app L)
    Function.Bijective (fun x : (DerivedCategory.singleFunctor _ 0).obj W ⟶ E⟦p⟧ =>
      x ≫ f⟦p⟧') := by
  apply (singularSheafDerivedTorusSectionsTruncationMap_bijective_iff k P W d p).2
  let a : ℤ := p - (d : ℤ)
  let f := singularSheafDerivedTorusSectionsTruncationMap k P a
  let : IsIso f := isIso_singularSheafDerivedTorusSectionsTruncationMap k P a
  exact (asIso (f⟦p⟧')).homToEquiv.bijective

end AlgebraicGeometry.SheafWithTransfers
