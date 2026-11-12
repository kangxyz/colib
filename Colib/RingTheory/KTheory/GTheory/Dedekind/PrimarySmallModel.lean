/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.FGModuleCat.PrimaryDecomposition
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization
public import Colib.CategoryTheory.Pi.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Primary decomposition on the native supported small category

Adapted from `Quillen/Aglib/Algebra/Category/FGModuleCat/PrimarySmallModel.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native finite-module categories, primary components and canonical maps are retained.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe t u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped nonZeroDivisors ZeroObject

namespace FGModuleCat.PrimaryDecomposition

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : Type u) [CommRing R]

section Noetherian

variable [IsNoetherianRing R]

/-- The original native supported small-model category, with no change of its predicate. -/
abbrev NativeSmallTorsion : Type u :=
  (Localization.supported.{u, u} (nonZeroDivisors R)).FullSubcategory

/-- The original support predicate is the inverse image under canonical small-model realization. -/
theorem smallTorsion_inverseImage :
    (localizationTorsionProperty (nonZeroDivisors R)).inverseImage
      (equivSmallModel.{u} (FGModuleCat.{u} R)).inverse =
      Localization.supported.{u, u} (nonZeroDivisors R) := by
  funext M
  exact propext (Localization.supported_iff (nonZeroDivisors R) M).symm

/-- Restrict the original canonical small-model equivalence to the actual torsion kernels. -/
def smallTorsionEquivalence : NativeSmallTorsion R ≌ TorsionModule R :=
  (equivSmallModel.{u} (FGModuleCat.{u} R)).symm.congrFullSubcategory (smallTorsion_inverseImage R)

instance smallTorsionEquivalence_functor_additive :
    (smallTorsionEquivalence R).functor.Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact (equivSmallModel.{u} (FGModuleCat.{u} R)).inverse.map_add

/-- Realization of the actual supported small category is exact. -/
def smallTorsionToOriginalExactFunctor : ExactCategory.ExactFunctor
    (abelianExactStructure (Localization.supported.{u, u} (nonZeroDivisors R)).FullSubcategory)
    (abelianExactStructure (localizationTorsionProperty (nonZeroDivisors R)).FullSubcategory) where
  toFunctor := (smallTorsionEquivalence R).functor
  map_conflation _ hS := hS.map_of_exact _

/-- The original-to-small supported comparison is exact for the same standard structures. -/
def originalToSmallTorsionExactFunctor : ExactCategory.ExactFunctor
    (abelianExactStructure (localizationTorsionProperty (nonZeroDivisors R)).FullSubcategory)
    (abelianExactStructure
      (Localization.supported.{u, u} (nonZeroDivisors R)).FullSubcategory) where
  toFunctor := (smallTorsionEquivalence R).inverse
  additive := (smallTorsionEquivalence R).inverse_additive
  map_conflation _ hS := hS.map_of_exact _

/-- The realized support inclusion is literally the original ambient realization functor. -/
theorem smallTorsionEquivalence_comp_inclusion :
    (smallTorsionEquivalence R).functor ⋙ (localizationTorsionProperty (nonZeroDivisors R)).ι =
      (Localization.supported.{u, u} (nonZeroDivisors R)).ι ⋙
        (equivSmallModel.{u} (FGModuleCat.{u} R)).inverse := rfl

/-- The inverse comparison also retains the original inclusion and small-model functor. -/
theorem smallTorsionEquivalence_inverse_comp_inclusion :
    (smallTorsionEquivalence R).inverse ⋙
        (Localization.supported.{u, u} (nonZeroDivisors R)).ι =
      (localizationTorsionProperty (nonZeroDivisors R)).ι ⋙
      (equivSmallModel.{u} (FGModuleCat.{u} R)).functor := rfl

/-- The original native support inclusion square uses the canonical ambient counit. -/
def smallTorsionInclusionIso :
    (smallTorsionEquivalence R).functor ⋙ (localizationTorsionProperty (nonZeroDivisors R)).ι ⋙
        (equivSmallModel.{u} (FGModuleCat.{u} R)).functor ≅
      (Localization.supported.{u, u} (nonZeroDivisors R)).ι :=
  NatIso.ofComponents
    (fun M => (equivSmallModel.{u} (FGModuleCat.{u} R)).counitIso.app M.obj) (by
      intro M N f
      exact (equivSmallModel.{u} (FGModuleCat.{u} R)).counitIso.hom.naturality f.hom)

/-- The original finite-module chosen-model functor with standard abelian exact structures. -/
def finiteModuleToNativeSmallExactFunctor : ExactCategory.ExactFunctor
    (abelianExactStructure (FGModuleCat.{u} R))
    (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} R))) where
  toFunctor := (equivSmallModel.{u} (FGModuleCat.{u} R)).functor
  map_conflation _ hS := hS.map_of_exact _

/-- The original support inclusion square, explicitly on the same small exact endpoints. -/
def smallTorsionInclusionExactIso :
    (((smallTorsionToOriginalExactFunctor R).comp
      (ObjectProperty.exactInclusion (localizationTorsionProperty (nonZeroDivisors R)))).comp
      (finiteModuleToNativeSmallExactFunctor R)).toFunctor ≅
      (ObjectProperty.exactInclusion
        (Localization.supported.{u, u} (nonZeroDivisors R))).toFunctor :=
  smallTorsionInclusionIso R

end Noetherian

/-- The original torsion category admits lower-universe models through its original inclusion. -/
instance torsionModule_essentiallySmall : EssentiallySmall.{u} (TorsionModule R) :=
  essentiallySmall_of_fully_faithful (localizationTorsionProperty (nonZeroDivisors R)).ι

/-- Ideal-power primary modules admit lower-universe models through their original inclusion. -/
instance primaryModule_essentiallySmall (I : Ideal R) : EssentiallySmall.{u} (PrimaryModule R I) :=
  essentiallySmall_of_fully_faithful (primaryObjectProperty R I).ι

section Dedekind

variable [IsDedekindDomain R]

section ChosenModels

variable [EssentiallySmall.{t} (TorsionModule R)]
  [∀ p : IsDedekindDomain.HeightOneSpectrum R, EssentiallySmall.{t} (PrimaryModule R p.asIdeal)]

/-- Chosen models at one explicit common universe give the same primary-family equivalence. -/
def chosenPrimaryEquivalence : SmallModel.{t} (TorsionModule R) ≌
    Pi.FiniteCategoryFamily (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{t} (PrimaryModule R p.asIdeal)) :=
  (equivSmallModel.{t} (TorsionModule R)).symm.trans
    ((finitePrimaryEquivalence R).trans (Pi.finiteFamilySmallModelEquivalence _))

/-- Realization from the explicitly chosen torsion model is exact. -/
def chosenTorsionRealizationExactFunctor : ExactCategory.ExactFunctor
    (abelianExactStructure (SmallModel.{t} (TorsionModule R)))
    (abelianExactStructure (localizationTorsionProperty (nonZeroDivisors R)).FullSubcategory) where
  toFunctor := (equivSmallModel.{t} (TorsionModule R)).inverse
  map_conflation _ hS := hS.map_of_exact _

/-- The chosen-model primary comparison uses the original exact functors throughout. -/
def chosenPrimaryExactFunctor : ExactCategory.ExactFunctor
    (abelianExactStructure (SmallModel.{t} (TorsionModule R)))
    (Pi.finiteCategoryExactStructure (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{t} (PrimaryModule R p.asIdeal))) :=
  ((chosenTorsionRealizationExactFunctor R).comp (finitePrimaryExactFunctor R)).comp
    (Pi.finiteFamilyToSmallModelExactFunctor _)

@[simp]
theorem chosenPrimaryExactFunctor_toFunctor :
    (chosenPrimaryExactFunctor R).toFunctor = (chosenPrimaryEquivalence R).functor := rfl

instance chosenPrimaryEquivalence_functor_additive :
    (chosenPrimaryEquivalence R).functor.Additive := by
  change (chosenPrimaryExactFunctor R).toFunctor.Additive
  infer_instance

/-- The same chosen-model inverse equivalence is exact. -/
def chosenPrimaryInverseExactFunctor : ExactCategory.ExactFunctor
    (Pi.finiteCategoryExactStructure (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{t} (PrimaryModule R p.asIdeal)))
    (abelianExactStructure (SmallModel.{t} (TorsionModule R))) where
  toFunctor := (chosenPrimaryEquivalence R).inverse
  additive := (chosenPrimaryEquivalence R).inverse_additive
  map_conflation _ hS := hS.map_of_exact _

/-- Chosen-model evaluation retains the original primary coordinate and its chosen model map. -/
theorem chosenPrimaryEquivalence_comp_evaluation (p : IsDedekindDomain.HeightOneSpectrum R) :
    (chosenPrimaryEquivalence R).functor ⋙ (Pi.finiteCategoryEvaluation
      (fun q : IsDedekindDomain.HeightOneSpectrum R => SmallModel.{t} (PrimaryModule R q.asIdeal))
      p).toFunctor =
      (equivSmallModel.{t} (TorsionModule R)).inverse ⋙ torsionPrimaryFunctor R p.asIdeal ⋙
        (equivSmallModel.{t} (PrimaryModule R p.asIdeal)).functor := rfl

/-- The original primary-to-chosen-model functor is exact at the declared model universe. -/
def chosenPrimaryModelExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor
      (abelianExactStructure (primaryObjectProperty R p.asIdeal).FullSubcategory)
      (abelianExactStructure (SmallModel.{t} (PrimaryModule R p.asIdeal))) where
  toFunctor := (equivSmallModel.{t} (PrimaryModule R p.asIdeal)).functor
  map_conflation _ hS := hS.map_of_exact _

/-- Chosen-model exact evaluation is the original coordinate chain on the same endpoints. -/
theorem chosenPrimaryExactFunctor_comp_evaluation (p : IsDedekindDomain.HeightOneSpectrum R) :
    (chosenPrimaryExactFunctor R).comp (Pi.finiteCategoryEvaluation
      (fun q : IsDedekindDomain.HeightOneSpectrum R =>
        SmallModel.{t} (PrimaryModule R q.asIdeal)) p) =
      ((chosenTorsionRealizationExactFunctor R).comp (torsionPrimaryExactFunctor R p)).comp
        (chosenPrimaryModelExactFunctor R p) := rfl

end ChosenModels

/-- The lower-universe primary family used by the original native number-ring support model. -/
abbrev NativePrimaryFamily : Type u := Pi.FiniteCategoryFamily
  (fun p : IsDedekindDomain.HeightOneSpectrum R => SmallModel.{u} (PrimaryModule R p.asIdeal))

/-- The actual native support category splits into its lower-universe actual primary models. -/
def nativePrimaryEquivalence : NativeSmallTorsion R ≌ NativePrimaryFamily R :=
  (smallTorsionEquivalence R).trans
    ((finitePrimaryEquivalence R).trans (Pi.finiteFamilySmallModelEquivalence _))

/-- The native comparison retains the original support realization and exact primary functors. -/
def nativePrimaryExactFunctor : ExactCategory.ExactFunctor
    (abelianExactStructure (Localization.supported.{u, u} (nonZeroDivisors R)).FullSubcategory)
    (Pi.finiteCategoryExactStructure (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{u} (PrimaryModule R p.asIdeal))) :=
  ((smallTorsionToOriginalExactFunctor R).comp (finitePrimaryExactFunctor R)).comp
    (Pi.finiteFamilyToSmallModelExactFunctor _)

@[simp]
theorem nativePrimaryExactFunctor_toFunctor :
    (nativePrimaryExactFunctor R).toFunctor = (nativePrimaryEquivalence R).functor := rfl

instance nativePrimaryEquivalence_functor_additive :
    (nativePrimaryEquivalence R).functor.Additive := by
  change (nativePrimaryExactFunctor R).toFunctor.Additive
  infer_instance

/-- The native inverse primary equivalence is exact in the same lower universe. -/
def nativePrimaryInverseExactFunctor : ExactCategory.ExactFunctor
    (Pi.finiteCategoryExactStructure (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      SmallModel.{u} (PrimaryModule R p.asIdeal)))
    (abelianExactStructure
      (Localization.supported.{u, u} (nonZeroDivisors R)).FullSubcategory) where
  toFunctor := (nativePrimaryEquivalence R).inverse
  additive := (nativePrimaryEquivalence R).inverse_additive
  map_conflation _ hS := hS.map_of_exact _

/-- Native evaluation retains the actual support realization and original primary coordinate. -/
theorem nativePrimaryEquivalence_comp_evaluation (p : IsDedekindDomain.HeightOneSpectrum R) :
    (nativePrimaryEquivalence R).functor ⋙ (Pi.finiteCategoryEvaluation
      (fun q : IsDedekindDomain.HeightOneSpectrum R => SmallModel.{u} (PrimaryModule R q.asIdeal))
      p).toFunctor =
      (smallTorsionEquivalence R).functor ⋙ torsionPrimaryFunctor R p.asIdeal ⋙
        (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).functor := rfl

/-- The original primary inclusion transported to the actual native supported category. -/
def nativePrimaryInclusion (p : IsDedekindDomain.HeightOneSpectrum R) :
    SmallModel.{u} (PrimaryModule R p.asIdeal) ⥤ NativeSmallTorsion R :=
  (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse ⋙ primaryToTorsion R p ⋙
    (smallTorsionEquivalence R).inverse

/-- The chosen lower-universe primary realization is exact. -/
def nativePrimaryRealizationExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor
      (abelianExactStructure (SmallModel.{u} (PrimaryModule R p.asIdeal)))
      (abelianExactStructure (primaryObjectProperty R p.asIdeal).FullSubcategory) where
  toFunctor := (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse
  map_conflation _ hS := hS.map_of_exact _

/-- The transported original primary inclusion is exact on the original native support model. -/
def nativePrimaryInclusionExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor
      (abelianExactStructure (SmallModel.{u} (PrimaryModule R p.asIdeal)))
      (abelianExactStructure (Localization.supported.{u, u} (nonZeroDivisors R)).FullSubcategory) :=
  ((nativePrimaryRealizationExactFunctor R p).comp (primaryToTorsionExactFunctor R p)).comp
    (originalToSmallTorsionExactFunctor R)

@[simp]
theorem nativePrimaryInclusionExactFunctor_toFunctor
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    (nativePrimaryInclusionExactFunctor R p).toFunctor = nativePrimaryInclusion R p := rfl

/-- The native primary inclusion retains the original ambient finite-module inclusion square. -/
theorem nativePrimaryInclusion_comp_support_inclusion
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    nativePrimaryInclusion R p ⋙
        (Localization.supported.{u, u} (nonZeroDivisors R)).ι =
      (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).inverse ⋙
        (primaryObjectProperty R p.asIdeal).ι ⋙
        (equivSmallModel.{u} (FGModuleCat.{u} R)).functor := rfl

/-- The original primary-to-lower-model functor is exact. -/
def nativePrimaryModelExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor
      (abelianExactStructure (primaryObjectProperty R p.asIdeal).FullSubcategory)
      (abelianExactStructure (SmallModel.{u} (PrimaryModule R p.asIdeal))) where
  toFunctor := (equivSmallModel.{u} (PrimaryModule R p.asIdeal)).functor
  map_conflation _ hS := hS.map_of_exact _

/-- Native exact evaluation is the actual original coordinate chain on the same small endpoints. -/
theorem nativePrimaryExactFunctor_comp_evaluation (p : IsDedekindDomain.HeightOneSpectrum R) :
    (nativePrimaryExactFunctor R).comp (Pi.finiteCategoryEvaluation
      (fun q : IsDedekindDomain.HeightOneSpectrum R =>
        SmallModel.{u} (PrimaryModule R q.asIdeal)) p) =
      ((smallTorsionToOriginalExactFunctor R).comp (torsionPrimaryExactFunctor R p)).comp
        (nativePrimaryModelExactFunctor R p) := rfl

/-- The transported original primary inclusion has its exact original ambient inclusion square. -/
theorem nativePrimaryInclusionExactFunctor_comp_support_inclusion
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    (nativePrimaryInclusionExactFunctor R p).comp (ObjectProperty.exactInclusion
        (Localization.supported.{u, u} (nonZeroDivisors R))) =
      ((nativePrimaryRealizationExactFunctor R p).comp
        (ObjectProperty.exactInclusion (primaryObjectProperty R p.asIdeal))).comp
        (finiteModuleToNativeSmallExactFunctor R) := rfl

end Dedekind

end FGModuleCat.PrimaryDecomposition
