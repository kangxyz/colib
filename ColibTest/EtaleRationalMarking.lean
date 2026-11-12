/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Morphisms.Etale.RationalMarking
import Colib.AlgebraicGeometry.Sites.Smooth.Etale.AffineSpaceInduction

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite

universe u

noncomputable section

example {k Ω : Type u} [Field k] [IsSepClosed k] [Field Ω]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (x : Spec (.of k) ⟶ X) (c : Spec (.of Ω) ⟶ Spec (.of k))
    (ξ : Spec (.of Ω) ⟶ U) (hξ : ξ ≫ f = c ≫ x) :
    ∃ l : Spec (.of k) ⟶ U, l ≫ f = x ∧ c ≫ l = ξ :=
  Scheme.exists_rational_lift_of_etale_marking f x c ξ hξ

example {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Etale f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.Spec.residueFieldIsoOfField (f x)).inv ≫ f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable k (X.residueField x) ∧ Module.Finite k (X.residueField x) ∧
      Function.Bijective (algebraMap k (X.residueField x)) :=
  ⟨f.residueFieldMapFromField_isSeparable x, f.residueFieldMapFromField_finite x,
    f.residueFieldMapFromField_bijective x⟩

/-- The original algebraic-closure marking descends as the original scheme morphism. -/
example (k : Type u) [Field k] [IsSepClosed k] (d : ℕ)
    (A : EtaleNeighborhood (affineSpaceObject k d) (affineSpaceOriginGeometricPoint k d).hom) :
    ∃ l : Spec (.of k) ⟶ ((etaleNeighborhoodToSmooth (affineSpaceObject k d)
        (affineSpaceOriginGeometricPoint k d).hom).obj A).left,
      l ≫ (etaleNeighborhoodHom (affineSpaceObject k d)
        (affineSpaceOriginGeometricPoint k d).hom A).left = affineSpaceOrigin k d ∧
      Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ l =
        etaleNeighborhoodMark (affineSpaceObject k d)
          (affineSpaceOriginGeometricPoint k d).hom A := by
  exact Scheme.exists_rational_lift_of_etale_marking
    (etaleNeighborhoodHom (affineSpaceObject k d)
      (affineSpaceOriginGeometricPoint k d).hom A).left
    (affineSpaceOrigin k d) _ _ (etaleNeighborhoodMark_hom _ _ A)

#print axioms Scheme.Hom.residueFieldMapFromField_isSeparable
#print axioms Scheme.Hom.residueFieldMapFromField_bijective
#print axioms Scheme.Hom.residueFieldMapFromField_finite
#print axioms Scheme.exists_rational_section_of_etale_marking
#print axioms Scheme.exists_rational_lift_of_etale_marking

end
