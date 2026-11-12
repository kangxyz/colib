/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationEquivalence
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.ExactTransport

/-!
# Actual restriction from coarse global sections to fine global open sections

The underlying functor is the original joint global reindexing. Exactness is transported
through the actual coefficient restriction equivalence; the chosen global zero is unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionModelFunctor
  boundedAboveFlatCoefficientSectionWaldhausen
  boundedAboveFlatCoefficientOriginalEvaluation
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The original fine global cross-row reindexing. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenModels.lean:32"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def globalOpenFineRestriction : globalRow Q ⟶ globalRow P :=
  Functor.whiskerRight (rowTransformation f)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R ⋙
      boundedAboveFlatGlobalSectionModelFunctor)

/-- Full-index naturality retains the original joint section reindexing. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenModels.lean:37"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem globalOpenRestriction_functor_square (a : Under R) :
    ((globalOpenFineRestriction f).app a).hom.toFunctor ⋙ ((rowRestriction P).app a).hom.toFunctor =
      ((openRowRestriction f).app a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientOpenRestrictionModelMap f a).hom.toFunctor := by
  rw [openRowRestriction_functor]
  exact congrArg (fun k => k.hom.toFunctor)
    ((boundedAboveFlatGlobalCoefficientModelRestriction R).naturality (show (op Q, a) ⟶ (op P, a)
      from (f.op, 𝟙 a)))

attribute [local semireducible] boundedAboveFlatGlobalSectionModelFunctor in
/-- Coarse-to-fine exactness follows from the actual restriction inverse and its unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenModels.lean:46"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem globalOpenRestriction_exact (a : Under R) :
    IsExact ((openRow f).obj a).obj.waldhausen.cof ((openRow f).obj a).obj.waldhausen.weq
      ((globalRow P).obj a).obj.waldhausen.cof ((globalRow P).obj a).obj.waldhausen.weq
      ((globalOpenFineRestriction f).app a).hom.toFunctor := by
  let e := ((boundedAboveFlatGlobalCoefficientModelRestriction R).app (op P,
    a)).hom.toFunctor.asEquivalence
  have h := (((openRowRestriction f).app a).hom.isExact.comp
    (boundedAboveFlatCoefficientOpenRestrictionModelMap f a).hom.isExact).comp
      (boundedAboveFlatGlobalCoefficientRestriction_inverse_exact R (op P, a))
  let i : (((openRowRestriction f).app a).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientOpenRestrictionModelMap f a).hom.toFunctor) ⋙ e.inverse ≅
      ((globalOpenFineRestriction f).app a).hom.toFunctor :=
    Functor.isoWhiskerRight (eqToIso (globalOpenRestriction_functor_square f a).symm)
      e.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _
  exact ExtensionCategory.isExact_of_natIso _ _ h i

/-- The original reindexing with coarse source weakness and the same chosen global zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenModels.lean:64"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def globalOpenRestrictionModelMap (a : Under R) :
    (openRow f).obj a ⟶ (globalRow P).obj a :=
  ⟨⟨((globalOpenFineRestriction f).app a).hom.toFunctor,
    globalOpenRestriction_exact f a⟩, ((globalOpenFineRestriction f).app a).property⟩

/-- Actual restriction is strictly natural in the coefficient object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenModels.lean:71"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def globalOpenRestriction : openRow f ⟶ globalRow P where
  app := globalOpenRestrictionModelMap f
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change ((globalRow Q).map g).hom.toFunctor ⋙
        ((globalOpenFineRestriction f).app b).hom.toFunctor =
      ((globalOpenFineRestriction f).app a).hom.toFunctor ⋙ ((globalRow P).map g).hom.toFunctor
    exact congrArg (fun k => k.hom.toFunctor) ((globalOpenFineRestriction f).naturality g)

/-- The actual full-open coefficient comparison square is strict. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenModels.lean:81"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem globalOpenRestriction_square :
    globalOpenRestriction f ≫ rowRestriction P =
      openRowRestriction f ≫ boundedAboveFlatCoefficientOpenRestrictionModelTransformation f := by
  apply NatTrans.ext
  funext a
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact globalOpenRestriction_functor_square f a

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

