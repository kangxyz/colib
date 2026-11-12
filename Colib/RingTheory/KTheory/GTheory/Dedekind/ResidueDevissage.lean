/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.PrimarySmallModel
public import Colib.Algebra.Category.FGModuleCat.IdealPowerFiltration
public import Colib.CategoryTheory.ExactCategory.Filtration.Subcategory
public import Colib.CategoryTheory.ExactCategory.Filtration.Functor
public import Colib.CategoryTheory.ExactCategory.Filtration.Iso
public import Colib.Algebra.Category.FGModuleCat.ScalarFiltration
public import Colib.KTheory.Quillen.Devissage.Theorem
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization
public import Colib.KTheory.Quillen.Map.Functoriality
public import Colib.KTheory.Quillen.Map.NaturalIso

/-!
# Quotient-ring dévissage for actual point-primary modules

The source is the native small-model G-theory of `R / p`. The target is the
same lower-universe small model of actual ideal-power-primary modules used
in native primary assembly. Actual ideal powers give the finite filtration;
the killed-by-p subcategory is the image of original quotient restriction.
The resulting all-degree K-equivalence retains that restriction's original,
zero-normalized K-map. No categorical equivalence with the whole primary
category or identification with a separately chosen residue field is used.

## Implementation provenance

Adapted from `Quillen/GTheory/Dedekind/ResidueDevissage.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native finite modules, actual
localization kernel, canonical scalar restrictions and original normalized K-maps are retained.
The standard exact structures use Colib's native abelian structures directly.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Abelian CategoryTheory.Abelian.Devissage
open FGModuleCat.PrimaryDecomposition
open FGModuleCat.IdealSupport
open scoped ZeroObject

namespace FGModuleCat.DedekindResidue

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)

/-- The actual quotient ring, which is distinct from a separately chosen residue field. -/
abbrev ResidueQuotient := R ⧸ p.asIdeal

/-- The original lower-universe primary model used by the native assembly. -/
abbrev PrimaryCategory : Type u := SmallModel.{u} (PrimaryModule R p.asIdeal)

/-- Realization of the primary small model as actual finite R-modules. -/
abbrev primaryRepresentation : PrimaryCategory R p ⥤ FGModuleCat.{u} R :=
  (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse ⋙
    (primaryObjectProperty R p.asIdeal).ι

/-- Multiplication by an actual scalar on the fully faithful primary representation. -/
abbrev primaryScalar (r : R) : 𝟭 (PrimaryCategory R p) ⟶ 𝟭 (PrimaryCategory R p) :=
  CentralEndomorphism.scalar (primaryRepresentation R p) r

/-- Primary objects annihilated by p itself, as opposed to a power of p. -/
def primaryKilled : ObjectProperty (PrimaryCategory R p) :=
  fun X => ∀ r : p.asIdeal, CentralEndomorphism.killed (primaryScalar R p r.val) X

/-- The small categorical predicate is actual annihilation by every element of p. -/
theorem primaryKilled_iff (X : PrimaryCategory R p) :
    primaryKilled R p X ↔ killedBy p.asIdeal ((primaryRepresentation R p).obj X) := by
  simp only [primaryKilled, CentralEndomorphism.scalar_killed_iff, killedBy]
  exact ⟨fun h r hr => h ⟨r, hr⟩, fun h r => h r.val r.property⟩

instance primaryKilled_containsZero : (primaryKilled R p).ContainsZero :=
  ⟨⟨0, isZero_zero _, fun r =>
    (CentralEndomorphism.killed (primaryScalar R p r.val)).prop_of_isZero
      (isZero_zero _)⟩⟩

instance primaryKilled_subobjects : (primaryKilled R p).IsClosedUnderSubobjects where
  prop_of_mono i _ h r :=
    (CentralEndomorphism.killed (primaryScalar R p r.val)).prop_of_mono i (h r)

instance primaryKilled_quotients : (primaryKilled R p).IsClosedUnderQuotients where
  prop_of_epi f _ h r :=
    (CentralEndomorphism.killed (primaryScalar R p r.val)).prop_of_epi f (h r)

instance primaryKilled_finiteProducts : (primaryKilled R p).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := {
    limitsOfShape_le := by
      rintro X ⟨q⟩ r
      change (primaryScalar R p r.val).app X = 0
      apply q.isLimit.hom_ext
      intro j
      have h : (primaryScalar R p r.val).app (q.diag.obj j) = 0 := q.prop_diag_obj j r
      have hn := (primaryScalar R p r.val).naturality (q.cone.π.app j)
      change q.cone.π.app j ≫ (primaryScalar R p r.val).app (q.diag.obj j) =
        (primaryScalar R p r.val).app X ≫ q.cone.π.app j at hn
      rw [h, comp_zero] at hn
      simpa only [zero_comp] using hn.symm }

/-- Ideal powers give genuine finite filtrations inside the actual primary small category. -/
theorem primaryFiltrationHypothesis : Devissage.FiltrationHypothesis (primaryKilled R p) := by
  intro X
  let M := (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse.obj X
  obtain ⟨n, hn⟩ := M.property
  obtain ⟨F⟩ := FGModuleCat.IdealSupport.idealPowerFiltration
    p.asIdeal M.obj n ((killedBy_iff_le_annihilator _ _).1 hn)
  let G := F.toFullSubcategory (primaryObjectProperty R p.asIdeal) M.property
  let H := (nativePrimaryModelExactFunctor R p).mapFiltration (Q := primaryKilled R p)
    (fun Y hY => (primaryKilled_iff R p _).2
      ((killedBy p.asIdeal).prop_of_iso
        ((primaryObjectProperty R p.asIdeal).ι.mapIso
          ((equivSmallModel.{u} (PrimaryModule R p.asIdeal)).unitIso.app Y)) hY)) G
  exact ⟨H.ofIso ((equivSmallModel.{u} (PrimaryModule R p.asIdeal)).counitIso.app X)⟩

/-- Actual quotient restriction, with codomain in the actual primary category. -/
def quotientToPrimary : FGModuleCat.{u} (ResidueQuotient R p) ⥤ PrimaryModule R p.asIdeal :=
  (primaryObjectProperty R p.asIdeal).lift (closedRestriction p.asIdeal) (fun M =>
    ⟨1, by simpa only [pow_one, killedBy] using closedRestriction_killed p.asIdeal M⟩)

omit [IsDedekindDomain R] in
/-- The factorization retains the original restriction of scalars along the quotient map. -/
theorem quotientToPrimary_comp_inclusion :
    quotientToPrimary R p ⋙ (primaryObjectProperty R p.asIdeal).ι =
      closedRestriction p.asIdeal := rfl

instance quotientToPrimary_additive : (quotientToPrimary R p).Additive := by
  dsimp [quotientToPrimary]
  infer_instance

instance quotientToPrimary_full : (quotientToPrimary R p).Full := by
  dsimp [quotientToPrimary]
  infer_instance

instance quotientToPrimary_faithful : (quotientToPrimary R p).Faithful := by
  dsimp [quotientToPrimary]
  infer_instance

/-- The quotient restriction is exact on the original large categories. -/
def quotientToPrimaryExact : ExactFunctor
    (abelianExactStructure (FGModuleCat.{u} (ResidueQuotient R p)))
    (abelianExactStructure (primaryObjectProperty R p.asIdeal).FullSubcategory) where
  toFunctor := quotientToPrimary R p
  map_conflation S hS := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (primaryObjectProperty R p.asIdeal).ι
    exact hS.map_of_exact (closedRestriction p.asIdeal)

/-- The original quotient restriction transported directly between matching native small models. -/
def smallQuotientToPrimaryExact : ExactFunctor
    (abelianExactStructure (FGModuleCat.{u} (ResidueQuotient R p))).smallModel
    (abelianExactStructure (PrimaryCategory R p)) :=
  (((abelianExactStructure (FGModuleCat.{u} (ResidueQuotient R p))).smallModelToOriginal).comp
    (quotientToPrimaryExact R p)).comp (nativePrimaryModelExactFunctor R p)

theorem smallQuotientToPrimary_killed
    (M : SmallModel.{u} (FGModuleCat.{u} (ResidueQuotient R p))) :
    primaryKilled R p ((smallQuotientToPrimaryExact R p).toFunctor.obj M) := by
  apply (primaryKilled_iff R p _).2
  apply (killedBy p.asIdeal).prop_of_iso
    ((primaryObjectProperty R p.asIdeal).ι.mapIso
      ((equivSmallModel.{u} (PrimaryModule R p.asIdeal)).unitIso.app
        ((quotientToPrimary R p).obj
          ((equivSmallModel.{u} (FGModuleCat.{u} (ResidueQuotient R p))).inverse.obj M))))
  exact closedRestriction_killed p.asIdeal _

/-- Factor the original small quotient restriction through exactly the p-annihilated objects. -/
def quotientToKilled : SmallModel.{u} (FGModuleCat.{u} (ResidueQuotient R p)) ⥤
    (primaryKilled R p).FullSubcategory :=
  (primaryKilled R p).lift (smallQuotientToPrimaryExact R p).toFunctor
    (smallQuotientToPrimary_killed R p)

instance quotientToKilled_additive : (quotientToKilled R p).Additive := by
  dsimp [quotientToKilled]
  infer_instance

instance quotientToKilled_full : (quotientToKilled R p).Full := by
  change ((primaryKilled R p).lift
    (((equivSmallModel.{u} (FGModuleCat.{u} (ResidueQuotient R p))).inverse ⋙
      quotientToPrimary R p) ⋙
      (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).functor) _).Full
  infer_instance

instance quotientToKilled_faithful : (quotientToKilled R p).Faithful := by
  change ((primaryKilled R p).lift
    (((equivSmallModel.{u} (FGModuleCat.{u} (ResidueQuotient R p))).inverse ⋙
      quotientToPrimary R p) ⋙
      (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).functor) _).Faithful
  infer_instance

/-- Every annihilated primary object carries its actual finite quotient-ring module structure. -/
instance quotientToKilled_essSurj : (quotientToKilled R p).EssSurj where
  mem_essImage X := by
    let e := equivSmallModel.{u} (PrimaryModule R p.asIdeal)
    let Q := equivSmallModel.{u} (FGModuleCat.{u} (ResidueQuotient R p))
    let M := e.inverse.obj X.obj
    let N : (killedBy p.asIdeal).FullSubcategory :=
      ⟨M.obj, (primaryKilled_iff R p X.obj).1 X.property⟩
    let L := (closedEquivalence p.asIdeal).inverse.obj N
    let f : (quotientToPrimary R p).obj L ≅ M := ObjectProperty.isoMk _
      ((killedBy p.asIdeal).ι.mapIso ((closedEquivalence p.asIdeal).counitIso.app N))
    refine ⟨Q.functor.obj L, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _
      (e.functor.mapIso ((quotientToPrimary R p).mapIso (Q.unitIso.app L).symm ≪≫ f) ≪≫
        e.counitIso.app X.obj)

instance quotientToKilled_isEquivalence : (quotientToKilled R p).IsEquivalence := {}

/-- The actual quotient equivalence onto killed objects, at matching native small endpoints. -/
def quotientToKilledExact : ExactFunctor
    (abelianExactStructure (FGModuleCat.{u} (ResidueQuotient R p))).smallModel
    (abelianExactStructure (primaryKilled R p).FullSubcategory) where
  toFunctor := quotientToKilled R p
  map_conflation S hS := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (primaryKilled R p).ι
    exact (smallQuotientToPrimaryExact R p).map_conflation S hS

instance quotientToKilledExact_isEquivalence :
    (quotientToKilledExact R p).toFunctor.IsEquivalence := quotientToKilled_isEquivalence R p

instance quotientToKilledExact_mapQ_isEquivalence :
    (quotientToKilledExact R p).mapQ.IsEquivalence := by
  apply (quotientToKilledExact R p).mapQ_isEquivalence_of_equivalence
  · intro X Y f hf
    rw [abelianExactStructure_smallModel]
    exact (abelianExactStructure_inflation_iff _ f).2
      ((quotientToKilledExact R p).toFunctor.mono_of_mono_map
        ((abelianExactStructure (primaryKilled R p).FullSubcategory).mono_of_inflation hf))
  · intro X Y f hf
    rw [abelianExactStructure_smallModel]
    exact (abelianExactStructure_deflation_iff _ f).2
      ((quotientToKilledExact R p).toFunctor.epi_of_epi_map
        ((abelianExactStructure (primaryKilled R p).FullSubcategory).epi_of_deflation hf))

/-- Original small quotient restriction followed by the actual primary inclusion. -/
def residueToPrimaryExact : ExactFunctor
    (abelianExactStructure (FGModuleCat.{u} (ResidueQuotient R p))).smallModel
    (abelianExactStructure (PrimaryCategory R p)) :=
  (quotientToKilledExact R p).comp (ObjectProperty.exactInclusion (primaryKilled R p))

/-- The dévissage factorization is literally the original transported restriction functor. -/
theorem residueToPrimaryExact_eq_original :
    residueToPrimaryExact R p = smallQuotientToPrimaryExact R p := rfl

/-- Quotient-ring G-theory is equivalent to the actual point-primary K-group in all degrees. -/
def residuePrimaryKEquiv (n : ℕ) :
    FGModuleCat.FractionLocalization.G (ResidueQuotient R p) n ≃*
      (abelianExactStructure (PrimaryCategory R p)).K n :=
  ((quotientToKilledExact R p).KEquivOfMapQIsEquivalence n).trans
    (Devissage.KEquiv (primaryKilled R p) (primaryFiltrationHypothesis R p) n)

/-- The forward equivalence is the original restriction-induced K-map, including rebasing. -/
@[simp]
theorem residuePrimaryKEquiv_toMonoidHom (n : ℕ) :
    ((residuePrimaryKEquiv R p n).toMonoidHom :
      FGModuleCat.FractionLocalization.G (ResidueQuotient R p) n →*
        (abelianExactStructure (PrimaryCategory R p)).K n) =
      (residueToPrimaryExact R p).KMap n := by
  change (Devissage.KMap (primaryKilled R p) n).comp
      ((quotientToKilledExact R p).KMap n) = _
  exact (ExactFunctor.KMap_comp _ _ n).symm

/-- The ambient square cancels only the canonical primary-model unit isomorphism. -/
def residueAmbientComparisonIso :
    ((residueToPrimaryExact R p).comp
      (((nativePrimaryRealizationExactFunctor R p).comp
        (ObjectProperty.exactInclusion (primaryObjectProperty R p.asIdeal))).comp
          (finiteModuleToNativeSmallExactFunctor R))).toFunctor ≅
      (((closedRestrictionExact p.asIdeal).smallModel).comp
        (CategoryTheory.SmallModel.abelianExactComparison (FGModuleCat.{u} R))).toFunctor := by
  let Q := equivSmallModel.{u} (FGModuleCat.{u} (ResidueQuotient R p))
  let e := equivSmallModel.{u} (PrimaryModule R p.asIdeal)
  let F := Q.inverse ⋙ quotientToPrimary R p
  let G := (primaryObjectProperty R p.asIdeal).ι ⋙
    (equivSmallModel.{u} (FGModuleCat.{u} R)).functor
  change F ⋙ e.functor ⋙ e.inverse ⋙ G ≅ F ⋙ G
  exact Functor.isoWhiskerLeft F (Functor.isoWhiskerRight e.unitIso.symm G) ≪≫
    Functor.isoWhiskerLeft F (Functor.leftUnitor G)

/-- Passing to ambient G-theory retains the original quotient pushforward K-map. -/
theorem residuePrimaryKEquiv_comp_ambient (n : ℕ) :
    ((SmallModelLocalization.standardKEquiv (FGModuleCat.{u} R) n).symm.toMonoidHom.comp
      ((((nativePrimaryRealizationExactFunctor R p).comp
        (ObjectProperty.exactInclusion (primaryObjectProperty R p.asIdeal))).comp
          (finiteModuleToNativeSmallExactFunctor R)).KMap n)).comp
        (residuePrimaryKEquiv R p n).toMonoidHom =
      (closedRestrictionExact p.asIdeal).smallKMap n := by
  let A := ((nativePrimaryRealizationExactFunctor R p).comp
    (ObjectProperty.exactInclusion (primaryObjectProperty R p.asIdeal))).comp
      (finiteModuleToNativeSmallExactFunctor R)
  have h := ExactFunctor.KMap_eq_of_natIso (residueAmbientComparisonIso R p) n
  rw [ExactFunctor.KMap_comp (residueToPrimaryExact R p) _ n,
    ExactFunctor.KMap_comp (closedRestrictionExact p.asIdeal).smallModel
      (CategoryTheory.SmallModel.abelianExactComparison (FGModuleCat.{u} R)) n] at h
  ext a
  change (SmallModelLocalization.standardKEquiv (FGModuleCat.{u} R) n).symm
    (((((nativePrimaryRealizationExactFunctor R p).comp
      (ObjectProperty.exactInclusion (primaryObjectProperty R p.asIdeal))).comp
        (finiteModuleToNativeSmallExactFunctor R)).KMap n)
          (residuePrimaryKEquiv R p n a)) = _
  apply (SmallModelLocalization.standardKEquiv (FGModuleCat.{u} R) n).injective
  rw [MulEquiv.apply_symm_apply]
  exact (congrArg (fun x => A.KMap n x)
    (DFunLike.congr_fun (residuePrimaryKEquiv_toMonoidHom R p n) a)).trans
      (DFunLike.congr_fun h a)

end FGModuleCat.DedekindResidue
