/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectPullback
public import Colib.AlgebraicGeometry.Scheme.QuasiCompactCategory

/-!
# Perfect K-theory as a contravariant functor

The actual flat K-functor is defined on all schemes. On quasi-compact schemes its literal
inclusion into perfect K-theory is a natural isomorphism. The bounded-vector-bundle comparison
is a natural transformation, not asserted to be an equivalence.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullbackFunctor.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The actual bounded-above flat chain K-map gives a functor on all schemes. -/
def boundedAboveFlatPerfectKFunctor (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (X.unop.toRingedSpace.boundedAboveFlatPerfectK n)
  map f := GrpCat.ofHom (boundedAboveFlatPerfectKPullback f.unop n)
  map_id X := by apply GrpCat.hom_ext; exact boundedAboveFlatPerfectKPullback_id X.unop n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact boundedAboveFlatPerfectKPullback_comp g.unop f.unop n

/-- All-perfect connective K-theory under arbitrary morphisms of quasi-compact schemes. -/
@[colib_tag "COL-0326",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullbackFunctor.lean:33-44"
    "adaptation" "Contravariant perfect K-functor on the full category of quasi-compact schemes"]
def perfectKFunctor (n : ℕ) : QuasiCompactSchemes.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of ((perfectComplexesWaldhausen X.unop.obj.toRingedSpace).K n)
  map f := GrpCat.ofHom (perfectKPullback f.unop.hom n)
  map_id X := by apply GrpCat.hom_ext; exact perfectKPullback_id X.unop.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact perfectKPullback_comp g.unop.hom f.unop.hom n

/-- The proved literal flat inclusion comparison is a natural isomorphism. -/
@[colib_tag "COL-0326"]
def boundedAboveFlatPerfectToPerfectNatIso (n : ℕ) :
    quasiCompactSchemesInclusion.op ⋙ boundedAboveFlatPerfectKFunctor.{u} n ≅
      perfectKFunctor n :=
  NatIso.ofComponents
    (fun X => (boundedAboveFlatPerfectKEquiv X.unop.obj.toRingedSpace n).toGrpIso)
    (fun f => by
      apply GrpCat.hom_ext
      exact (boundedAboveFlatPerfectToPerfectKMap_pullback f.unop.hom n).symm)

/-- The forward natural comparison is exactly the original literal inclusion K-map. -/
@[simp]
theorem boundedAboveFlatPerfectToPerfectNatIso_hom_app (n : ℕ)
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    ((boundedAboveFlatPerfectToPerfectNatIso n).hom.app X).hom =
      boundedAboveFlatPerfectToPerfectKMap X.unop.obj.toRingedSpace n := rfl

/-- Bounded vector-bundle inclusion is natural for the actual perfect K-pullback. -/
def boundedFiniteLocallyFreeToPerfectNatTrans (n : ℕ) :
    quasiCompactSchemesInclusion.op ⋙ boundedFiniteLocallyFreeKFunctor.{u} n ⟶
      perfectKFunctor n where
  app X := GrpCat.ofHom (boundedFiniteLocallyFreeToPerfectKMap X.unop.obj n)
  naturality {X Y} f := by
    apply GrpCat.hom_ext
    exact (boundedFiniteLocallyFreeToPerfectKMap_pullback f.unop.hom n).symm

end AlgebraicGeometry.Scheme
