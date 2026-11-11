/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationComponents

/-!
# The actual raw affine evaluation source transport
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Explicit propositional transport between witnesses of one proposition. -/
private theorem transportProofWitness {Q : Prop} (p q : Q) (F : Q → Prop)
    (h : F p) : F q :=
  Eq.mp (congrArg F (Subsingleton.elim p q)) h

/-- One named equality in the original raw section functor categories. -/
theorem boundedAboveFlatAffineEvaluationRawCompSource
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineSectionsMap (f ≫ g) ⋙
      boundedAboveFlatAffineOriginalEvaluation T : BoundedAboveFlatAffineSections R ⥤
        (boundedAboveFlatPerfectComplex (Spec T).toRingedSpace).FullSubcategory) =
      (boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineSectionsMap g) ⋙
        boundedAboveFlatAffineOriginalEvaluation T :=
  congrArg (fun G : BoundedAboveFlatAffineSections R ⥤ BoundedAboveFlatAffineSections T =>
    G ⋙ boundedAboveFlatAffineOriginalEvaluation T) (boundedAboveFlatAffineSectionsMap_comp f g)

/-- The original component equation with the same named raw source equality. -/
theorem boundedAboveFlatAffineEvaluationRawComp_app
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s : BoundedAboveFlatAffineSections R) :
    (boundedAboveFlatAffineEvaluationCoefficientIso (f ≫ g)).hom.app s ≫
        (boundedAboveFlatAffineNormalizedCompIso f g).hom.app
          ((boundedAboveFlatAffineOriginalEvaluation R).obj s) =
      (eqToHom (boundedAboveFlatAffineEvaluationRawCompSource f g)).app s ≫
        (boundedAboveFlatAffineEvaluationCoefficientIso g).hom.app
          ((boundedAboveFlatAffineSectionsMap f).obj s) ≫
        (boundedAboveFlatAffineNormalizedPullback g).map
          ((boundedAboveFlatAffineEvaluationCoefficientIso f).hom.app s) := by
  exact transportProofWitness
    (congrArg (fun G => G ⋙ boundedAboveFlatAffineOriginalEvaluation T)
      (boundedAboveFlatAffineSectionsMap_comp f g))
    (boundedAboveFlatAffineEvaluationRawCompSource f g)
    (fun sourceEquality =>
      (boundedAboveFlatAffineEvaluationCoefficientIso (f ≫ g)).hom.app s ≫
          (boundedAboveFlatAffineNormalizedCompIso f g).hom.app
            ((boundedAboveFlatAffineOriginalEvaluation R).obj s) =
        (eqToHom sourceEquality).app s ≫
          (boundedAboveFlatAffineEvaluationCoefficientIso g).hom.app
            ((boundedAboveFlatAffineSectionsMap f).obj s) ≫
          (boundedAboveFlatAffineNormalizedPullback g).map
            ((boundedAboveFlatAffineEvaluationCoefficientIso f).hom.app s))
    (boundedAboveFlatAffineEvaluationCoefficientIso_comp_app f g s)

end AlgebraicGeometry.Scheme.Modules
