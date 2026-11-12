/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.Basic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsFunctor
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.FieldTheory.Perfect
import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerivedSourceNaturality
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.PerfectField
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.TransferInvariance
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.TorusLocalZero
import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CohomologyComparison

/-!
# Higher images of the transfer torus reindexing

Evaluation of the actual reindexed injective resolution at a correspondence
object is represented by the transfer representable of its torus product.
The comparison respects every signed correspondence restriction. Exact
transfer sheafification then gives the genuine right-derived functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "T" => Cor.parameterProduct Gₘ
local notation "R" => T ⋙ transferRepresentable k
private abbrev torusDiagramFunctor :
    SheafWithTransfers.{u + 1} k ⥤ ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  torusSectionsFunctor k ⋙ SheafWithTransfers.forget k ⋙ PresheafWithTransfers.forget

local notation "B" => torusSectionsFunctor k
local notation "D" => torusDiagramFunctor k

local instance : HasExt.{u + 1} (SheafWithTransfers.{u + 1} k) := hasExt_of_enoughInjectives _

private abbrev torusSectionsAt (X : (Cor k)ᵒᵖ) :
    SheafWithTransfers.{u + 1} k ⥤ AddCommGrpCat.{u + 1} :=
  D ⋙ (CategoryTheory.evaluation _ _).obj X

private abbrev torusSectionsAtMap {X Y : (Cor k)ᵒᵖ} (f : X ⟶ Y) :
    torusSectionsAt k X ⟶ torusSectionsAt k Y :=
  Functor.whiskerLeft D ((CategoryTheory.evaluation (Cor k)ᵒᵖ AddCommGrpCat.{u + 1}).map f)

private def torusSectionsAtRepresented (X : (Cor k)ᵒᵖ) :
    preadditiveCoyoneda.obj (op ((R).obj X.unop)) ≅ torusSectionsAt k X :=
  NatIso.ofComponents (fun F => (transferSectionsEquiv k ((T).obj X.unop) F).toAddCommGrpIso)
    (by
      intro F G f
      ext x
      exact transferSectionsEquiv_comp k ((T).obj X.unop) x f)

private theorem torusSectionsAtRepresented_naturality {X Y : (Cor k)ᵒᵖ} (f : X ⟶ Y) :
    preadditiveCoyoneda.map ((R).map f.unop).op ≫ (torusSectionsAtRepresented k Y).hom =
      (torusSectionsAtRepresented k X).hom ≫ torusSectionsAtMap k f := by
  ext F x
  exact transferSectionsEquiv_naturality_left k F ((T).map f.unop) x

private def torusSectionsAtDerivedRepresented (X : (Cor k)ᵒᵖ) (n : ℕ) :
    (preadditiveCoyoneda.obj (op ((R).obj X.unop))).rightDerived n ≅
      (torusSectionsAt k X).rightDerived n where
  hom := NatTrans.rightDerived (torusSectionsAtRepresented k X).hom n
  inv := NatTrans.rightDerived (torusSectionsAtRepresented k X).inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]

private theorem torusSectionsAtDerivedRepresented_naturality {X Y : (Cor k)ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    NatTrans.rightDerived (preadditiveCoyoneda.map ((R).map f.unop).op) n ≫
        (torusSectionsAtDerivedRepresented k Y n).hom =
      (torusSectionsAtDerivedRepresented k X n).hom ≫
        NatTrans.rightDerived (torusSectionsAtMap k f) n := by
  dsimp only [torusSectionsAtDerivedRepresented]
  rw [← NatTrans.rightDerived_comp, torusSectionsAtRepresented_naturality,
    NatTrans.rightDerived_comp]

variable {F : SheafWithTransfers.{u + 1} k} (I : InjectiveResolution F)

private def torusResolutionStep (n : ℕ) :
    ShortComplex ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  (I.cocomplex.sc n).map D

private def torusSectionsAtDerivedIso (n : ℕ) (X : (Cor k)ᵒᵖ) :
    (((torusSectionsAt k X).rightDerived n).obj F) ≅
      (torusResolutionStep k I n).homology.obj X :=
  I.isoRightDerivedObj (torusSectionsAt k X) n ≪≫
    (torusResolutionStep k I n).mapHomologyIso ((CategoryTheory.evaluation _ _).obj X)

private theorem torusSectionsAtDerivedIso_naturality (n : ℕ)
    {X Y : (Cor k)ᵒᵖ} (f : X ⟶ Y) :
    (NatTrans.rightDerived (torusSectionsAtMap k f) n).app F ≫
        (torusSectionsAtDerivedIso k I n Y).hom =
      (torusSectionsAtDerivedIso k I n X).hom ≫ (torusResolutionStep k I n).homology.map f := by
  rw [I.rightDerived_app_eq]
  dsimp only [torusSectionsAtDerivedIso, Iso.trans_hom]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  apply (cancel_epi (I.isoRightDerivedObj (torusSectionsAt k X) n).hom).2
  change ShortComplex.homologyMap
      ((torusResolutionStep k I n).mapNatTrans ((CategoryTheory.evaluation _ _).map f)) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp

private def torusExtResolutionIso (n : ℕ) :
    (T).op ⋙ transferExtPresheaf k F n ≅ (torusResolutionStep k I n).homology :=
  NatIso.ofComponents (fun X =>
    (I.extRightDerivedAddEquiv ((R).obj X.unop) n).toAddCommGrpIso ≪≫
      (torusSectionsAtDerivedRepresented k X n).app F ≪≫
      torusSectionsAtDerivedIso k I n X) (by
    intro X Y f
    ext x
    let a := I.extRightDerivedAddEquiv ((R).obj X.unop) n x
    change (torusSectionsAtDerivedIso k I n Y).hom
        (((torusSectionsAtDerivedRepresented k Y n).app F).hom
          (I.extRightDerivedAddEquiv ((R).obj Y.unop) n
            ((Ext.mk₀ ((R).map f.unop)).comp x (zero_add n)))) =
      (torusResolutionStep k I n).homology.map f
        ((torusSectionsAtDerivedIso k I n X).hom
          (((torusSectionsAtDerivedRepresented k X n).app F).hom a))
    erw [InjectiveResolution.extRightDerivedAddEquiv_naturality_left
      (I := I) (X := (R).obj X.unop) (n := n) ((R).map f.unop) x]
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (torusSectionsAtDerivedRepresented_naturality k f n) F) a
    change ((torusSectionsAtDerivedRepresented k Y n).app F).hom
        ((NatTrans.rightDerived (preadditiveCoyoneda.map ((R).map f.unop).op) n).app F a) =
      (NatTrans.rightDerived (torusSectionsAtMap k f) n).app F
        (((torusSectionsAtDerivedRepresented k X n).app F).hom a) at h
    rw [h]
    exact ConcreteCategory.congr_hom (torusSectionsAtDerivedIso_naturality k I n f) _)

variable [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

private def torusExtCohomologyIso (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    (T).op ⋙ transferExtPresheaf k F n ≅
      (torusSections (SheafCohomology.withTransfers k F n)).obj :=
  NatIso.ofComponents (fun X =>
    (transferExtEquiv k ((T).obj X.unop).toSmoothSite F n).toAddCommGrpIso) (by
    intro X Y f
    ext x
    exact (ordinaryCohomologyTransfers_apply k F n ((T).map f.unop) x).symm)

/-- The actual higher image is the transfer sheafification of ordinary cohomology
on the torus products, with the original action of every signed correspondence. -/
@[no_expose]
def torusSectionsRightDerivedIso (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    ((B).rightDerived n).obj F ≅
      (nisnevichSheafify k).obj (torusSections (SheafCohomology.withTransfers k F n)) := by
  let I := injectiveResolution F
  let K := (I.cocomplex.sc n).map B
  let S := K.map (SheafWithTransfers.forget k)
  let e : torusSections (SheafCohomology.withTransfers k F n) ≅ S.homology :=
    ObjectProperty.isoMk _ ((torusExtCohomologyIso k F n).symm ≪≫
      torusExtResolutionIso k I n ≪≫ S.mapHomologyIso PresheafWithTransfers.forget)
  let ε := asIso (nisnevichSheafificationAdjunction k).counit
  exact I.isoRightDerivedObj B n ≪≫
    ((ShortComplex.homologyFunctor _).mapIso (K.mapNatIso ε)).symm ≪≫
    S.mapHomologyIso (nisnevichSheafify k) ≪≫ (nisnevichSheafify k).mapIso e.symm

/-- The actual positive right-derived torus reindexing vanishes when the
ordinary cohomology in that degree is A¹-invariant. -/
theorem torusSectionsRightDerived_isZero_succ (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant) :
    IsZero (((B).rightDerived (n + 1)).obj F) := by
  apply (torusSectionsRightDerivedIso k F (n + 1)).isZero_iff.mpr
  let P := torusSections (SheafCohomology.withTransfers k F (n + 1))
  let G := (nisnevichSheafify k).obj P
  let A := (toSheaf k).obj G
  let U := toSheaf k ⋙ sheafToPresheaf _ AddCommGrpCat.{u + 1}
  have hA : IsZero (U.obj G) := (Functor.isZero_iff _).mpr (by
    intro V
    let X := V.unop
    let r := EtaleSeparatedFiniteType.restrict X AddCommGrpCat.{u + 1}
    let e := r.mapIso (((nisnevichSheafificationUnderlyingIso k).app P).symm)
    let q := EtaleSeparatedFiniteType.toSmoothSite X
    let e' := (q.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
        (EtaleSeparatedFiniteType.nisnevichTopology X.left)
        (SmoothSite.nisnevichTopology (Spec (.of k)))).symm.app ((toPresheaf k).obj P)
    have hz : IsZero (r.obj A) :=
      (SheafCohomology.isZero_smallSheafify_torus_succ F n hP X).of_iso (e ≪≫ e')
    let W := EtaleSeparatedFiniteType.identityObject X
    let E := sheafToPresheaf (EtaleSeparatedFiniteType.nisnevichTopology X.left)
      AddCommGrpCat.{u + 1} ⋙ (CategoryTheory.evaluation _ _).obj (op W)
    have hW : IsZero (A.obj.obj (op (q.obj W))) := E.map_isZero hz
    exact hW.of_iso (A.obj.mapIso (EtaleSeparatedFiniteType.identityImageIso X).op))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply U.map_injective
  change U.map (𝟙 G) = U.map (0 : G ⟶ G)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp hA

/-- Over a perfect field, an A¹-invariant transfer sheaf is acyclic for the
actual torus reindexing functor. -/
theorem torusSectionsRightDerived_isZero_succ_of_perfect [PerfectField k]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n : ℕ) :
    IsZero (((B).rightDerived (n + 1)).obj F) :=
  torusSectionsRightDerived_isZero_succ k F n
    ((SheafCohomology.withTransfers_isA1Invariant_iff k F (n + 1)).mpr
      (isStrictA1Invariant_of_perfect F hF (n + 1)))

end AlgebraicGeometry.SheafWithTransfers
