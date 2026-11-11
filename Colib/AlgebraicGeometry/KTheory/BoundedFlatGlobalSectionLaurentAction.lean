/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalCoefficientRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientBassSeed
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSectionUnit
public import Colib.CategoryTheory.FiberedCategory.SectionChangeIndexUnit

/-! # The same Laurent action under actual global section restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Functor.IdentityAutomorphism KTheory.Bass
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent
universe u
open CategoryTheory.SectionChangeIndex
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}}

/-- Actual coefficient restriction preserves the original geometric scalar on every section. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionRestrictionUnit.lean:23"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem coefficientRestriction_unit_preserves (R : CommRingCat.{u}) (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) :
    Preserves ((boundedAboveFlatGlobalCoefficientModelRestriction R).app i).hom.toFunctor
      (boundedAboveFlatGlobalSectionUnit
        ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj i) r)
      (boundedAboveFlatCoefficientSectionUnitIso i r) := by
  exact restriction_lift_preserves boundedAboveFlatPerfectPseudofunctor
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R) i
    (boundedAboveFlatPerfectGlobalUnitIso (space i) r)

/-- The actual coefficient projection pulls the forward Laurent coordinate back literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentScalar.lean:30"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem globalLaurentScalar_map {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b : Under R} (g : a ⟶ b) :
    Units.map (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      (show (op P, (laurentUnderFunctor R).obj a) ⟶
          (op P, (laurentUnderFunctor R).obj b) from
        (𝟙 (op P), (laurentUnderFunctor R).map g))).appTop.hom.toMonoidHom
      (boundedAboveFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (laurentCoordinate a.right)) =
      boundedAboveFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)
        (laurentCoordinate b.right) := by
  rw [boundedAboveFlatCoefficientUnit_map]
  have hr : Units.map (Spec.map ((laurentUnderFunctor R).map g).right).appTop.hom.toMonoidHom
      (laurentCoordinate a.right) = laurentCoordinate b.right :=
    laurentCoordinate_coefficient g.right
  exact congrArg (boundedAboveFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj b)) hr

/-- The same forward Laurent coordinate lifted through global identity evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentAction.lean:35"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def globalLaurentUnit (P : Over (Spec R)) (a : Under R) :
    𝟭 ((globalRow P).obj ((laurentUnderFunctor R).obj a)).obj.Obj ≅
      𝟭 ((globalRow P).obj ((laurentUnderFunctor R).obj a)).obj.Obj :=
  boundedAboveFlatGlobalSectionUnit ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor
    R).obj
    (op P, (laurentUnderFunctor R).obj a))
    (boundedAboveFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (laurentCoordinate a.right))

/-- The original Laurent coordinate is preserved under every coefficient arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentAction.lean:44"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem globalLaurentUnit_naturality (P : Over (Spec R)) {a b : Under R} (g : a ⟶ b) :
    Preserves ((globalRow P).map ((laurentUnderFunctor R).map g)).hom.toFunctor
      (globalLaurentUnit P a) (globalLaurentUnit P b) := by
  exact boundedAboveFlatGlobalSectionUnit_reindex_of_eq
    ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).map
      (show (op P, (laurentUnderFunctor R).obj a) ⟶
          (op P, (laurentUnderFunctor R).obj b) from
        (𝟙 (op P), (laurentUnderFunctor R).map g)))
    _ _ (globalLaurentScalar_map P g)

/-- The global Laurent action uses the original forward coordinate and no chosen replacement. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentAction.lean:55"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def globalLaurentAction (P : Over (Spec R)) : LaurentSeed.ModelAction (globalRow P) where
  unit := globalLaurentUnit P
  naturality := globalLaurentUnit_naturality P

/-- Actual restriction preserves the original Laurent action at every coefficient. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentAction.lean:60"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem rowRestriction_unit (P : Over (Spec R)) (a : Under R) :
    Preserves ((rowRestriction P).app ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((globalLaurentAction P).unit a)
      ((boundedAboveFlatCoefficientAmbientLaurentAction P).unit a) := by
  dsimp only [rowRestriction, Functor.whiskerLeft_app, globalLaurentAction,
    globalLaurentUnit, boundedAboveFlatCoefficientAmbientLaurentAction,
    boundedAboveFlatCoefficientSectionLaurentUnitIso]
  exact coefficientRestriction_unit_preserves R (op P, (laurentUnderFunctor R).obj a)
    (boundedAboveFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (laurentCoordinate a.right))

/-- Every value of the original Laurent track commutes with actual restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentAction.lean:72"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem rowRestriction_track (P : Over (Spec R)) (a : Under R) (n : ℕ)
    (t : unitInterval) (x : (prespectrum ((globalRow P).obj a)).space n) :
    (prespectrumMap ((rowRestriction P).app ((laurentUnderFunctor R).obj a))).map n
      (((globalLaurentAction P).track.homotopy a).level n (t, x)) =
    ((boundedAboveFlatCoefficientAmbientLaurentAction P).track.homotopy a).level n
      (t, (prespectrumMap ((rowRestriction P).app a)).map n x) :=
  LaurentSeed.ModelAction.track_square (globalLaurentAction P)
    (boundedAboveFlatCoefficientAmbientLaurentAction P) (rowRestriction P)
    (rowRestriction_unit P) a n t x

/-- The original scalar/null seed commutes with actual restriction as a whole natural map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentAction.lean:83"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem rowRestriction_seed (P : Over (Spec R)) :
    (globalLaurentAction P).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (rowRestriction P) prespectrumFunctor) =
    Functor.whiskerRight (rowRestriction P) prespectrumFunctor ≫
      (boundedAboveFlatCoefficientAmbientLaurentAction P).track.seed :=
  LaurentSeed.Track.seed_square _ _ _ (rowRestriction_track P)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
