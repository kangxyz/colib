/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.FGModuleCat.RestrictScalars
public import Colib.Algebra.Category.FGModuleCat.IdealClosedSupport
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization
public import Colib.KTheory.Quillen.SmallModel.Functoriality
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Canonical comparison with the residue field of a Dedekind prime

For a height-one prime of a Dedekind domain, the original algebra map from the
quotient ring to `Ideal.ResidueField` is bijective. The resulting canonical
R-algebra equivalence identifies finite modules by actual scalar restriction.
Its composite with quotient pushforward is naturally isomorphic to restriction
along the original R-map into the residue field; the component maps are the
identity on the underlying additive groups.

All small-model and K-theory endpoints use the native common universe `u`.
The forward K-equivalence is the original scalar-restriction `smallKMap`, and
its pushforward square retains the original zero-normalized maps. These results
allow quotient-residue assembly to be expressed using `Ideal.ResidueField`.
No identification with a scheme's residue field is asserted here.

## Implementation provenance

Adapted from `Quillen/GTheory/Dedekind/ResidueField.lean` at Quillen commit
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
attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat.DedekindResidue

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)

/-- The canonical R-algebra equivalence is the original quotient-to-residue-field map. -/
def quotientResidueFieldAlgEquiv : (R ⧸ p.asIdeal) ≃ₐ[R] p.asIdeal.ResidueField :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ p.asIdeal) p.asIdeal.ResidueField)
    p.asIdeal.bijective_algebraMap_quotient_residueField

/-- The equivalence has precisely the canonical algebra map as its underlying function. -/
@[simp] theorem quotientResidueFieldAlgEquiv_apply (x : R ⧸ p.asIdeal) :
    quotientResidueFieldAlgEquiv R p x =
      algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField x := rfl

/-- The original R-map commutes with the canonical quotient comparison. -/
@[simp] theorem quotientResidueFieldAlgEquiv_algebraMap (r : R) :
    quotientResidueFieldAlgEquiv R p (Ideal.Quotient.mk p.asIdeal r) =
      algebraMap R p.asIdeal.ResidueField r := rfl

/-- Equality of the original ring homomorphisms, before passing to module categories. -/
theorem quotientResidueFieldAlgEquiv_comp_quotient :
    (quotientResidueFieldAlgEquiv R p).toRingHom.comp (Ideal.Quotient.mk p.asIdeal) =
      algebraMap R p.asIdeal.ResidueField := rfl

/-- The inverse comparison also preserves the original R-map. -/
theorem quotientResidueFieldAlgEquiv_symm_algebraMap (r : R) :
    (quotientResidueFieldAlgEquiv R p).symm (algebraMap R p.asIdeal.ResidueField r) =
      Ideal.Quotient.mk p.asIdeal r :=
  (quotientResidueFieldAlgEquiv R p).symm.commutes r

private theorem finite_restriction_iff (M : ModuleCat.{u} p.asIdeal.ResidueField) :
    Module.Finite (R ⧸ p.asIdeal)
      ((ModuleCat.restrictScalars (quotientResidueFieldAlgEquiv R p).toRingHom).obj M) ↔
        Module.Finite p.asIdeal.ResidueField M := by
  let N := (ModuleCat.restrictScalars (quotientResidueFieldAlgEquiv R p).toRingHom).obj M
  have : IsScalarTower (R ⧸ p.asIdeal) p.asIdeal.ResidueField N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  constructor
  · intro h
    have : Module.Finite (R ⧸ p.asIdeal) N := h
    exact Module.Finite.of_restrictScalars_finite (R ⧸ p.asIdeal) p.asIdeal.ResidueField N
  · intro h
    have : Module.Finite p.asIdeal.ResidueField N := h
    have : Module.Finite (R ⧸ p.asIdeal) p.asIdeal.ResidueField :=
      RingHom.Finite.of_surjective _ (quotientResidueFieldAlgEquiv R p).surjective
    exact Module.Finite.trans p.asIdeal.ResidueField N

/-- Restrict the original ring-equivalence module functor to actual finite modules. -/
def residueFieldFiniteEquivalence :
    FGModuleCat.{u} p.asIdeal.ResidueField ≌ FGModuleCat.{u} (R ⧸ p.asIdeal) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (quotientResidueFieldAlgEquiv R p).toRingEquiv).congrFullSubcategory (by
      ext M
      exact finite_restriction_iff R p M)

/-- Actual scalar restriction along the canonical quotient-to-residue-field map. -/
def residueFieldRestriction : FGModuleCat.{u} p.asIdeal.ResidueField ⥤
    FGModuleCat.{u} (R ⧸ p.asIdeal) :=
  FGModuleCat.finiteRestriction (quotientResidueFieldAlgEquiv R p).toRingHom
    (RingHom.Finite.of_surjective _ (quotientResidueFieldAlgEquiv R p).surjective)

/-- The equivalence's forward functor is the original finite scalar restriction. -/
theorem residueFieldFiniteEquivalence_functor :
    (residueFieldFiniteEquivalence R p).functor = residueFieldRestriction R p := rfl

/-- Canonical scalar restriction is an actual equivalence of finite-module categories. -/
instance residueFieldRestriction_isEquivalence : (residueFieldRestriction R p).IsEquivalence :=
  (residueFieldFiniteEquivalence R p).isEquivalence_functor

/-- The same original finite scalar restriction, with its standard exact structures. -/
def residueFieldRestrictionExact :
    ExactFunctor (abelianExactStructure (FGModuleCat.{u} p.asIdeal.ResidueField))
      (abelianExactStructure (FGModuleCat.{u} (R ⧸ p.asIdeal))) :=
  FGModuleCat.finiteRestrictionExact (quotientResidueFieldAlgEquiv R p).toRingHom
    (RingHom.Finite.of_surjective _ (quotientResidueFieldAlgEquiv R p).surjective)

/-- Actual restriction along the original R-map into `Ideal.ResidueField`. -/
def residueFieldPushforward :
    FGModuleCat.{u} p.asIdeal.ResidueField ⥤ FGModuleCat.{u} R :=
  FGModuleCat.finiteRestriction (algebraMap R p.asIdeal.ResidueField)
    (RingHom.Finite.of_surjective _ p.asIdeal.algebraMap_residueField_surjective)

/-- The original residue-field pushforward is exact on finite modules. -/
def residueFieldPushforwardExact :
    ExactFunctor (abelianExactStructure (FGModuleCat.{u} p.asIdeal.ResidueField))
      (abelianExactStructure (FGModuleCat.{u} R)) :=
  FGModuleCat.finiteRestrictionExact (algebraMap R p.asIdeal.ResidueField)
    (RingHom.Finite.of_surjective _ p.asIdeal.algebraMap_residueField_surjective)

/-- Restriction through the quotient agrees with the original R-restriction. -/
def residueFieldRestrictionPushforwardIso :
    residueFieldRestriction R p ⋙
        FGModuleCat.IdealSupport.closedRestriction p.asIdeal ≅
      residueFieldPushforward R p :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    (ModuleCat.restrictScalarsComp'App (Ideal.Quotient.mk p.asIdeal)
      (quotientResidueFieldAlgEquiv R p).toRingHom (algebraMap R p.asIdeal.ResidueField)
      rfl M.obj).symm) (by
    intro M N f
    apply FGModuleCat.hom_ext
    rfl)

/-- The pushforward comparison uses the identity function on every underlying module. -/
theorem residueFieldRestrictionPushforwardIso_hom_apply
    (M : FGModuleCat.{u} p.asIdeal.ResidueField) (m : M) :
    ((residueFieldRestrictionPushforwardIso R p).hom.app M).hom.hom m = m := rfl

/-- The inverse pushforward comparison also uses the identity function. -/
theorem residueFieldRestrictionPushforwardIso_inv_apply
    (M : FGModuleCat.{u} p.asIdeal.ResidueField) (m : M) :
    ((residueFieldRestrictionPushforwardIso R p).inv.app M).hom.hom m = m := rfl

/-- The canonical equivalence between the two native lower-universe finite-module models. -/
def residueFieldSmallEquivalence :
    SmallModel.{u} (FGModuleCat.{u} p.asIdeal.ResidueField) ≌
      SmallModel.{u} (FGModuleCat.{u} (R ⧸ p.asIdeal)) :=
  (equivSmallModel.{u} (FGModuleCat.{u} p.asIdeal.ResidueField)).symm.trans
    ((residueFieldFiniteEquivalence R p).trans
      (equivSmallModel.{u} (FGModuleCat.{u} (R ⧸ p.asIdeal))))

/-- The chosen small equivalence retains the original exact scalar-restriction functor. -/
theorem residueFieldSmallEquivalence_functor :
    (residueFieldSmallEquivalence R p).functor =
      (residueFieldRestrictionExact R p).smallModel.toFunctor := rfl

/-- The original scalar restriction remains an equivalence at the small endpoints. -/
instance residueFieldSmallRestriction_isEquivalence :
    (residueFieldRestrictionExact R p).smallModel.toFunctor.IsEquivalence :=
  (residueFieldSmallEquivalence R p).isEquivalence_functor

/-- Reflection of actual monomorphisms and epimorphisms gives the original Q-equivalence. -/
instance residueFieldSmallRestriction_mapQ_isEquivalence :
    (residueFieldRestrictionExact R p).smallModel.mapQ.IsEquivalence := by
  apply (residueFieldRestrictionExact R p).smallModel.mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    rw [abelianExactStructure_smallModel]
    exact (abelianExactStructure_inflation_iff _ i).2
      ((residueFieldRestrictionExact R p).smallModel.toFunctor.mono_of_mono_map
        ((abelianExactStructure (FGModuleCat.{u} (R ⧸ p.asIdeal))).smallModel.mono_of_inflation hi))
  · intro X Y i hi
    rw [abelianExactStructure_smallModel]
    exact (abelianExactStructure_deflation_iff _ i).2
      ((residueFieldRestrictionExact R p).smallModel.toFunctor.epi_of_epi_map
        ((abelianExactStructure (FGModuleCat.{u} (R ⧸ p.asIdeal))).smallModel.epi_of_deflation hi))

/-- Canonical native G-theory comparison, in every degree and with original map forward. -/
def residueFieldKEquiv (n : ℕ) :
    FGModuleCat.FractionLocalization.G p.asIdeal.ResidueField n ≃*
      FGModuleCat.FractionLocalization.G (R ⧸ p.asIdeal) n :=
  (residueFieldRestrictionExact R p).smallModel.KEquivOfMapQIsEquivalence n

/-- The forward comparison is exactly the original finite scalar-restriction K-map. -/
@[simp] theorem residueFieldKEquiv_toMonoidHom (n : ℕ) :
    ((residueFieldKEquiv R p n).toMonoidHom : FGModuleCat.FractionLocalization.G
      p.asIdeal.ResidueField n →*
      FGModuleCat.FractionLocalization.G (R ⧸ p.asIdeal) n) =
      (residueFieldRestrictionExact R p).smallKMap n := rfl

/-- The original pushforward square at matching native small exact endpoints. -/
def residueFieldSmallRestrictionPushforwardIso :
    ((residueFieldRestrictionExact R p).smallModel.comp
      (FGModuleCat.IdealSupport.closedRestrictionExact
        p.asIdeal).smallModel).toFunctor ≅
      (residueFieldPushforwardExact R p).smallModel.toFunctor :=
  (ExactFunctor.smallModelCompIso (residueFieldRestrictionExact R p)
    (FGModuleCat.IdealSupport.closedRestrictionExact p.asIdeal)).symm ≪≫
      ExactFunctor.smallModelNatIso (residueFieldRestrictionPushforwardIso R p)

/-- The canonical K-comparison preserves the original R-pushforward, including normalization. -/
theorem residueFieldKEquiv_comp_pushforward (n : ℕ) :
    ((FGModuleCat.IdealSupport.closedRestrictionExact
      p.asIdeal).smallKMap n).comp (residueFieldKEquiv R p n).toMonoidHom =
      (residueFieldPushforwardExact R p).smallKMap n := by
  rw [residueFieldKEquiv_toMonoidHom,
    ← ExactFunctor.smallKMap_comp]
  exact ExactFunctor.smallKMap_eq_of_natIso (residueFieldRestrictionPushforwardIso R p) n

end FGModuleCat.DedekindResidue
