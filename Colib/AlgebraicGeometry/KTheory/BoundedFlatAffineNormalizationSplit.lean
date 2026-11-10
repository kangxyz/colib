/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoherence
public import Colib.KTheory.Waldhausen.Iterated.NormalizationCompositionHomotopy

/-!
# The actual affine normalized composition and its geometric split

The geometric isomorphism retains the contravariant spectrum transport. Factoring
its normalized constraint cancels only the intermediate canonical normalization.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual geometric composition iso includes the original contravariant Spec transport. -/
def boundedAboveFlatAffineGeometricCompIso {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatPerfectPullback (Spec.map (f ≫ g)) ≅
      boundedAboveFlatPerfectPullback (Spec.map f) ⋙
        boundedAboveFlatPerfectPullback (Spec.map g) :=
  eqToIso (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g)) ≪≫
    boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)

/-- Its forward transformation is the already fixed geometric comparison. -/
theorem boundedAboveFlatAffineGeometricCompIso_hom {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineGeometricCompIso f g).hom =
      boundedAboveFlatAffineGeometricComp f g := by
  rw [boundedAboveFlatAffineGeometricComp_eq]
  simp only [boundedAboveFlatAffineGeometricCompIso, Iso.trans_hom, eqToIso.hom]

/-- The actual total constraint is the two specified normalized transformations composed. -/
theorem boundedAboveFlatAffineNormalizedCompIso_split_hom
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineNormalizedCompIso f g).hom =
      normalizedWeakTransformation (boundedAboveFlatPerfectPullback_isExact (Spec.map (f ≫ g)))
        ((boundedAboveFlatPerfectPullback_isExact (Spec.map f)).comp
          (boundedAboveFlatPerfectPullback_isExact (Spec.map g)))
        (boundedAboveFlatAffineGeometricCompIso f g).hom ≫
          (exactNormalizationCompIso (boundedAboveFlatPerfectPullback_isExact (Spec.map f))
            (boundedAboveFlatPerfectPullback_isExact (Spec.map g))).hom := by
  rw [normalizedWeakTransformation_comp_exactNormalizationCompIso,
    boundedAboveFlatAffineGeometricCompIso_hom]
  exact boundedAboveFlatAffineNormalizedCompIso_hom f g

end AlgebraicGeometry.Scheme.Modules
