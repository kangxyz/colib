/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionDiagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionLaurentUnit
public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.CategoryTheory.Functor.IdentityAutomorphismSquare

/-!
# Original Laurent tracks on the fixed-open supported coefficient diagram

The actual supported Model functor carries the genuine Laurent coefficient square in Under R.
The already proved original scalar coefficient equation supplies its automorphism square.
Realization therefore gives literal naturality at every original homotopy time, including
level zero. No homotopy naturality or seed compatibility is assumed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
open Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original Laurent action on the unchanged supported coefficient Model arrow. -/
def boundedAboveFlatAffineSupportedDiagramLaurentPullbackUnitIso (a : Under R) :
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).hom.toFunctor ≅
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).hom.toFunctor :=
  Functor.IdentityAutomorphism.onFunctor
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).hom.toFunctor
    (boundedAboveFlatAffineSupportedSectionUnitIso
      (inclusion j ((laurentUnderFunctor R).obj a)) (laurentCoordinate a.right))

/-- The actual fixed-base Laurent coefficient square remains a literal Model square. -/
theorem boundedAboveFlatAffineSupportedDiagramLaurentModelSquare {a b : Under R} (f : a ⟶ b) :
    (boundedAboveFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a) ≫
        (boundedAboveFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderFunctor R).map f) =
      (boundedAboveFlatAffineSupportedSectionModelFunctor j).map f ≫
        (boundedAboveFlatAffineSupportedSectionModelFunctor j).map
          ((laurentUnderCoefficient R).app b) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (boundedAboveFlatAffineSupportedSectionModelFunctor j).map
    ((laurentUnderCoefficient R).naturality f).symm

/-- The literal Model square intertwines the unchanged original Laurent automorphisms. -/
theorem boundedAboveFlatAffineSupportedDiagramLaurentModelUnitSquare {a b : Under R} (f : a ⟶ b) :
    Functor.whiskerRight (boundedAboveFlatAffineSupportedDiagramLaurentPullbackUnitIso j a).hom
        ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map
          ((laurentUnderFunctor R).map f)).hom.toFunctor ≫
        eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSupportedDiagramLaurentModelSquare j f)) =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSupportedDiagramLaurentModelSquare j f)) ≫
        Functor.whiskerLeft
          ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map f).hom.toFunctor
          (boundedAboveFlatAffineSupportedDiagramLaurentPullbackUnitIso j b).hom :=
  Functor.IdentityAutomorphism.onFunctor_whisker_square
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).hom.toFunctor
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app b)).hom.toFunctor
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map f).hom.toFunctor
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map
      ((laurentUnderFunctor R).map f)).hom.toFunctor
    (eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
      (boundedAboveFlatAffineSupportedDiagramLaurentModelSquare j f)))
    (boundedAboveFlatAffineSupportedSectionUnitIso
      (inclusion j ((laurentUnderFunctor R).obj a)) (laurentCoordinate a.right))
    (boundedAboveFlatAffineSupportedSectionUnitIso
      (inclusion j ((laurentUnderFunctor R).obj b)) (laurentCoordinate b.right))
    (by
      have hr : Units.map
          (Spec.map ((laurentUnderFunctor R).map f).right).appTop.hom.toMonoidHom
            (laurentCoordinate a.right) = laurentCoordinate b.right :=
        laurentCoordinate_coefficient f.right
      exact (boundedAboveFlatAffineSupportedSectionUnitIso_coefficient_hom
        (inclusion j ((laurentUnderFunctor R).obj a))
        (inclusion j ((laurentUnderFunctor R).obj b))
        ((laurentUnderFunctor R).map f).right
        (openMap j ((laurentUnderFunctor R).map f))
        (openMap_inclusion j ((laurentUnderFunctor R).map f)) (laurentCoordinate a.right)).trans
          (congrArg (fun r ↦ Functor.whiskerLeft
            ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map
              ((laurentUnderFunctor R).map f)).hom.toFunctor
            (boundedAboveFlatAffineSupportedSectionUnitIso
              (inclusion j ((laurentUnderFunctor R).obj b)) r).hom) hr))

/-- The whole Laurent loop of the original fixed-open coefficient prespectrum. -/
def boundedAboveFlatAffineSupportedDiagramLaurentHomotopy (a : Under R) :
    Homotopy
      ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a))
      ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a)) :=
  prespectrumIsoHomotopy
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a))
    (boundedAboveFlatAffineSupportedDiagramLaurentPullbackUnitIso j a)

/-- The diagram loop is precisely the original supported Laurent action on its actual pair square.
-/
theorem boundedAboveFlatAffineSupportedDiagramLaurentHomotopy_eq (a : Under R) :
    boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a =
      boundedAboveFlatAffineSupportedSectionUnitHomotopy
        (inclusion j a) (inclusion j ((laurentUnderFunctor R).obj a))
        ((laurentUnderCoefficient R).app a).right
        (openMap j ((laurentUnderCoefficient R).app a))
        (openMap_inclusion j ((laurentUnderCoefficient R).app a)) (laurentCoordinate a.right) := rfl

/-- Every original coefficient map preserves every interval value of the actual Laurent loop. -/
theorem boundedAboveFlatAffineSupportedDiagramLaurentHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map
        ((laurentUnderFunctor R).map f)).map n
        ((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j b).level n
        (t, ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n x) :=
  prespectrumIsoHomotopy_square_apply
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app a))
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderCoefficient R).app b))
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map f)
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map ((laurentUnderFunctor R).map f))
    (boundedAboveFlatAffineSupportedDiagramLaurentPullbackUnitIso j a)
    (boundedAboveFlatAffineSupportedDiagramLaurentPullbackUnitIso j b)
    (boundedAboveFlatAffineSupportedDiagramLaurentModelSquare j f)
    (boundedAboveFlatAffineSupportedDiagramLaurentModelUnitSquare j f) n t x

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SupportedSectionDiagramLaurent.lean:36-113"
  "adaptation"
  "Actual fixed-base supported Laurent Waldhausen-model squares and full same-time homotopies"]
  boundedAboveFlatAffineSupportedDiagramLaurentPullbackUnitIso
  boundedAboveFlatAffineSupportedDiagramLaurentModelSquare
  boundedAboveFlatAffineSupportedDiagramLaurentModelUnitSquare
  boundedAboveFlatAffineSupportedDiagramLaurentHomotopy
  boundedAboveFlatAffineSupportedDiagramLaurentHomotopy_eq
  boundedAboveFlatAffineSupportedDiagramLaurentHomotopy_naturality_apply

end AlgebraicGeometry.Scheme.Modules
