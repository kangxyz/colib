/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenModels
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeakEquivalence
public import Colib.KTheory.Bass.ModelDiagramStableEquivalence
/-! # Exact inverse comparisons for the original global localization rows

The original complete evaluation square proves inverse exactness on actual supported and
coarse rows. Finite stability is derived from those exact equivalences, not assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS KTheory.Bass
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionModelFunctor
  boundedAboveFlatCoefficientSectionWaldhausen
  boundedAboveFlatCoefficientOriginalEvaluation

@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:34"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
private theorem exactIntoEvaluation
    {A B C : Type*} [Category A] [Category B] [Category C]
    (WA : Structure A) (WC : Structure C) (e : B ≌ C) (z : B)
    (hz : IsZero (e.functor.obj z)) (F : A ⥤ B)
    (h : IsExact WA.cof WA.weq WC.cof WC.weq (F ⋙ e.functor)) :
    IsExact WA.cof WA.weq (WC.ofEquivalence e z hz).cof
      (WC.ofEquivalence e z hz).weq F where
  zero hx := IsZero.of_full_of_faithful_of_isZero e.functor _ (h.zero hx)
  cofibration g hg := h.cofibration g hg
  weak g hg := h.weak g hg
  pushout hi hp := IsPushout.of_map_of_faithful e.functor (h.pushout hi hp)

/-- The actual supported restriction inverse is exact for the original transported classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:47"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
theorem supportedRestriction_inverse_exact (R : CommRingCat.{u}) (c : Index R)
    {U : Scheme.{u}} (j : U ⟶ space c) [IsOpenImmersion j] :
    IsExact (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedAboveFlatGlobalSupportedWaldhausen (X :=
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).cof
      (boundedAboveFlatGlobalSupportedWaldhausen (X :=
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).weq
      (supportedRestriction R c j).asEquivalence.inverse := by
  let e := (supportedRestriction R c j).asEquivalence
  have hi : e.inverse ⋙ boundedAboveFlatGlobalSupportedEvaluation
      (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j ≅
      boundedAboveFlatCoefficientSupportedEvaluation j :=
    Functor.isoWhiskerLeft e.inverse (eqToIso (supportedRestriction_evaluation R c j).symm) ≪≫
      e.invFunIdAssoc (boundedAboveFlatCoefficientSupportedEvaluation j)
  apply exactIntoEvaluation _ _ (boundedAboveFlatGlobalSupportedEvaluation
    (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).asEquivalence
  exact ExtensionCategory.isExact_of_natIso _ _
    (boundedAboveFlatCoefficientSupportedEvaluation_exact j) hi.symm

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Each actual supported row component has its unchanged exact categorical inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:71"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
theorem supportedRowRestriction_inverse_exact (a : Under R) :
    IsExact ((boundedAboveFlatCoefficientSupportedModelFunctor f).obj a).obj.waldhausen.cof
      ((boundedAboveFlatCoefficientSupportedModelFunctor f).obj a).obj.waldhausen.weq
      ((supportedRow f).obj a).obj.waldhausen.cof ((supportedRow f).obj a).obj.waldhausen.weq
      (supportedRestriction R (op Q, a) (schemeMap f a)).asEquivalence.inverse :=
  supportedRestriction_inverse_exact R (op Q, a) (schemeMap f a)

/-- Every finite iterate retains the actual supported restriction and is stable. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:79"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
theorem supportedRowRestriction_iterate_isStableEquivalence
    (S : Under R ⥤ Arrow (Arrow (Under R))) (i : ℕ) (a : Under R) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)).app a) := by
  apply modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence S i
    (supportedRow f) (boundedAboveFlatCoefficientSupportedModelFunctor f)
    (supportedRowRestriction f)
    (fun a => (supportedRestriction R (op Q, a) (schemeMap f a)).asEquivalence)
    (fun _ => rfl)
  exact fun a => supportedRowRestriction_inverse_exact f a

/-- The actual coarse component is the unchanged ambient restriction functor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:91"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
theorem openRowRestriction_functor (a : Under R) :
    ((openRowRestriction f).app a).hom.toFunctor =
      ((boundedAboveFlatGlobalCoefficientModelRestriction R).app (op Q, a)).hom.toFunctor := by
  change ((boundedAboveFlatGlobalCoefficientModelRestriction R).app (op Q, a)).hom.toFunctor ⋙ 𝟭 _
    = _
  exact Functor.comp_id _

/-- The actual coarse restriction is a categorical equivalence with the original ambient inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:98"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
def openRowRestrictionEquivalence (a : Under R) :
    ((openRow f).obj a).obj.Obj ≌ ((boundedAboveFlatCoefficientOpenModelFunctor f).obj a).obj.Obj :=
  ((boundedAboveFlatGlobalCoefficientModelRestriction R).app (op Q,
    a)).hom.toFunctor.asEquivalence.changeFunctor
    (eqToIso (openRowRestriction_functor f a).symm)

/-- The equivalence retains the actual coarse component functor literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:104"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
theorem openRowRestrictionEquivalence_functor (a : Under R) :
    (openRowRestrictionEquivalence f a).functor = ((openRowRestriction f).app a).hom.toFunctor :=
      rfl

/-- The coarse categorical inverse is the original fine restriction inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:108"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
theorem openRowRestrictionEquivalence_inverse (a : Under R) :
    (openRowRestrictionEquivalence f a).inverse =
      ((boundedAboveFlatGlobalCoefficientModelRestriction R).app (op Q,
        a)).hom.toFunctor.asEquivalence.inverse := rfl

attribute [local semireducible] boundedAboveFlatGlobalSectionModelFunctor in
/-- The original fine restriction inverse is also exact for the actual coarse weak classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:113"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
theorem openRowRestriction_inverse_exact (a : Under R) :
    IsExact ((boundedAboveFlatCoefficientOpenModelFunctor f).obj a).obj.waldhausen.cof
      ((boundedAboveFlatCoefficientOpenModelFunctor f).obj a).obj.waldhausen.weq
      ((openRow f).obj a).obj.waldhausen.cof ((openRow f).obj a).obj.waldhausen.weq
      ((boundedAboveFlatGlobalCoefficientModelRestriction R).app (op Q,
        a)).hom.toFunctor.asEquivalence.inverse := by
  exact Structure.withInverseImageWeak_inverse_exact
    ((boundedAboveFlatGlobalCoefficientModelRestriction R).app (op Q,
      a)).hom.toFunctor.asEquivalence
    ((boundedAboveFlatGlobalCoefficientModelRestriction R).app (op Q, a)).hom.isExact
    (boundedAboveFlatGlobalCoefficientRestriction_inverse_exact R (op Q, a))
    (boundedAboveFlatCoefficientOpenNested f a)

/-- Every finite iterate retains the actual coarse restriction and is stable. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationEquivalence.lean:125"
  "adaptation" "Original exact inverse and derived finite stability of global localization rows"]
theorem openRowRestriction_iterate_isStableEquivalence
    (S : Under R ⥤ Arrow (Arrow (Under R))) (i : ℕ) (a : Under R) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)).app a) := by
  apply modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence S i
    (openRow f) (boundedAboveFlatCoefficientOpenModelFunctor f) (openRowRestriction f)
    (openRowRestrictionEquivalence f) (openRowRestrictionEquivalence_functor f)
  intro a
  rw [openRowRestrictionEquivalence_inverse]
  exact openRowRestriction_inverse_exact f a

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
