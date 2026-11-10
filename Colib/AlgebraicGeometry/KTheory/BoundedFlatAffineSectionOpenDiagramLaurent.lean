/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenDiagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentHomotopy
public import Colib.RingTheory.Polynomial.LaurentUnderSquare

/-!
# The original Laurent-unit track on relative-open sections

The coarse Model diagram uses exactly the original section functors and scalar automorphisms.
The actual original Laurent coefficient equation proves the transformation square; its original
realization supplies the whole coefficient-natural loop, including degree zero. The genuine
fixed-open pullbacks and both original Laurent legs remain unchanged.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original target Laurent unit acts on the unchanged relative-open coefficient functor. -/
def boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso (a : Under R) :
    ((boundedAboveFlatAffineSectionOpenModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).hom.toFunctor ≅
    ((boundedAboveFlatAffineSectionOpenModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).hom.toFunctor :=
  Functor.IdentityAutomorphism.onFunctor
    ((boundedAboveFlatAffineSectionOpenModelFunctor j).map
      ((laurentUnderCoefficient R).app a)).hom.toFunctor
    (boundedAboveFlatAffineSectionLaurentUnitIso a.right)

/-- The coarse action is exactly the existing original section Laurent pullback action. -/
theorem boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso_eq (a : Under R) :
    boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a =
      boundedAboveFlatAffineSectionLaurentPullbackUnitIso a.right := rfl

/-- The unchanged Laurent coefficient square is a literal square of actual coarse Models. -/
theorem boundedAboveFlatAffineSectionOpenDiagramLaurentModelSquare {a b : Under R} (f : a ⟶ b) :
    (boundedAboveFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a) ≫
        (boundedAboveFlatAffineSectionOpenModelFunctor j).map ((laurentUnderFunctor R).map f) =
      (boundedAboveFlatAffineSectionOpenModelFunctor j).map f ≫
        (boundedAboveFlatAffineSectionOpenModelFunctor j).map
          ((laurentUnderCoefficient R).app b) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (boundedAboveFlatAffineSectionOpenModelFunctor j).map
    ((laurentUnderCoefficient R).naturality f).symm

/-- The actual coarse coefficient square intertwines the same original Laurent automorphisms. -/
theorem boundedAboveFlatAffineSectionOpenDiagramLaurentModelUnitSquare {a b : Under R} (f : a ⟶ b) :
    Functor.whiskerRight (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a).hom
        ((boundedAboveFlatAffineSectionOpenModelFunctor j).map
          ((laurentUnderFunctor R).map f)).hom.toFunctor ≫
        eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSectionOpenDiagramLaurentModelSquare j f)) =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSectionOpenDiagramLaurentModelSquare j f)) ≫
        Functor.whiskerLeft ((boundedAboveFlatAffineSectionOpenModelFunctor j).map f).hom.toFunctor
          (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j b).hom :=
  Functor.IdentityAutomorphism.onFunctor_whisker_square _ _ _ _ _ _ _
    (boundedAboveFlatAffineSectionLaurentUnitIso_coefficient f.right)

/-- The original scalar action supplies the entire relative-open Laurent loop. -/
def boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy (a : Under R) :
    Homotopy
      ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a))
      ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a)) :=
  prespectrumIsoHomotopy
    ((boundedAboveFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a))
    (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a)

/-- Every coefficient map preserves the whole original Laurent track at the identical time. -/
theorem boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map
        ((laurentUnderFunctor R).map f)).map n
        ((boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j b).level n
        (t, ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map f).map n x) :=
  prespectrumIsoHomotopy_square_apply
    ((boundedAboveFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app a))
    ((boundedAboveFlatAffineSectionOpenModelFunctor j).map ((laurentUnderCoefficient R).app b))
    ((boundedAboveFlatAffineSectionOpenModelFunctor j).map f)
    ((boundedAboveFlatAffineSectionOpenModelFunctor j).map ((laurentUnderFunctor R).map f))
    (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a)
    (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j b)
    (boundedAboveFlatAffineSectionOpenDiagramLaurentModelSquare j f)
    (boundedAboveFlatAffineSectionOpenDiagramLaurentModelUnitSquare j f) n t x

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionOpenDiagramLaurent.lean:32-98"
  "adaptation" "Actual relative-open section construction with the original maps and weak class"]
  boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso
  boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso_eq
  boundedAboveFlatAffineSectionOpenDiagramLaurentModelSquare
  boundedAboveFlatAffineSectionOpenDiagramLaurentModelUnitSquare
  boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy
  boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy_naturality_apply

end AlgebraicGeometry.Scheme.Modules
