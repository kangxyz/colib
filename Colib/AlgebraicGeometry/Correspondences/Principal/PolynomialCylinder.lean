/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# The principal polynomial cylinder in native affine-line coordinates

The polynomial pullback and its literal evaluation sections are identified with
those of the existing smooth-site cylinder. Transporting a correspondence uses
the actual graph functor; its endpoint composites are the original polynomial
endpoint composites, without assuming a principal-cycle specialization theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.SmoothSite Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] (X : Scheme.SmoothSite (Spec (.of k)))

/-- The polynomial cylinder's underlying scheme is the original parameter pullback. -/
theorem polynomialCylinder_left :
    (product X (polynomialAffineLine (.of k))).left = parameterSpace X.hom := rfl

/-- The actual polynomial endpoint is the scheme map of the smooth-site section. -/
theorem polynomialAffineSection_left (a : k) :
    (polynomialAffineSection (.of k) X a).left = endpoint X.hom a := rfl

/-- Native coordinates recover the original evaluation map, not merely an isomorphic fibre. -/
@[reassoc]
theorem nativeAffineSection_polynomialCylinder (a : k) :
    (nativeAffineSection (.of k) X a).left ≫
      (affineCylinderPolynomialIso (.of k) X).hom.left = endpoint X.hom a := by
  exact congrArg (fun f => f.left) (nativeAffineSection_polynomialIso (.of k) X a)

variable (Y : Scheme.SmoothSite (Spec (.of k)))

/-- Transport a genuine polynomial correspondence through the existing cylinder graph. -/
def nativeCylinderCorrespondence
    (α : (Cor.graphFunctor k).obj (product X (polynomialAffineLine (.of k))) ⟶
      (Cor.graphFunctor k).obj Y) :
    (Cor.graphFunctor k).obj (affineLineCylinder.obj X) ⟶ (Cor.graphFunctor k).obj Y :=
  (Cor.graphFunctor k).map (affineCylinderPolynomialIso (.of k) X).hom ≫ α

/-- Endpoint graph composition commutes with the exact cylinder transport. -/
theorem graph_nativeAffineSection_comp
    (α : (Cor.graphFunctor k).obj (product X (polynomialAffineLine (.of k))) ⟶
      (Cor.graphFunctor k).obj Y) (a : k) :
    (Cor.graphFunctor k).map (nativeAffineSection (.of k) X a) ≫
        nativeCylinderCorrespondence X Y α =
      (Cor.graphFunctor k).map (polynomialAffineSection (.of k) X a) ≫ α := by
  rw [nativeCylinderCorrespondence, ← Category.assoc, ← Functor.map_comp,
    nativeAffineSection_polynomialIso]

end AlgebraicGeometry.PrincipalFamilyUnitOpen
