module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionTelescope

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
open CategoryTheory.Functor.IdentityAutomorphism CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
noncomputable section
variable {R : CommRingCat.{u}} (P : Over (Spec R))

example (i : Index R) (r : (Γ(space i, ⊤))ˣ)
    (S : BoundedAboveFlatCoefficientSections i) :
    (boundedAboveFlatCoefficientOriginalEvaluation i).map
      ((boundedAboveFlatCoefficientSectionUnitIso i r).hom.app S) =
    (boundedAboveFlatPerfectGlobalUnitIso (space i) r).hom.app
      ((boundedAboveFlatCoefficientOriginalEvaluation i).obj S) :=
  boundedAboveFlatCoefficientSectionUnitIso_evaluation_hom i r S

example (a : Under R) :
    Preserves ((rowRestriction P).app ((laurentUnderFunctor R).obj a)).hom.toFunctor
      ((globalLaurentAction P).unit a)
      ((boundedAboveFlatCoefficientAmbientLaurentAction P).unit a) :=
  rowRestriction_unit P a

example (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (prespectrum ((globalRow P).obj a)).space n) :
    (prespectrumMap ((rowRestriction P).app ((laurentUnderFunctor R).obj a))).map n
      (((globalLaurentAction P).track.homotopy a).level n (t, x)) =
    ((boundedAboveFlatCoefficientAmbientLaurentAction P).track.homotopy a).level n
      (t, (prespectrumMap ((rowRestriction P).app a)).map n x) :=
  rowRestriction_track P a n t x

example :
    (globalLaurentAction P).track.seed ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (Functor.whiskerRight (rowRestriction P) prespectrumFunctor) =
    Functor.whiskerRight (rowRestriction P) prespectrumFunctor ≫
      (boundedAboveFlatCoefficientAmbientLaurentAction P).track.seed :=
  rowRestriction_seed P

example (i : ℕ) :
    finiteRestriction P i ≫ boundedAboveFlatCoefficientAmbientBassTransition P i =
      globalTransition P i ≫ finiteRestriction P (i + 1) :=
  finiteRestriction_transition P i

example (i : ℕ) (a : Under R) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      ((finiteRestriction P i).app a)) :=
  finiteRestriction_isStableEquivalence P i a _

example (a : Under R) (n i : ℕ) (s : unitInterval)
    (x : ((globalDiagram P i).obj a).space n) :
    ((telescopeRestriction P).app a).map n
      (Telescope.cylinder (fun j => (globalDiagram P j).obj a)
        (fun j => (globalTransition P j).app a) n i (s, x)) =
    Telescope.cylinder (fun j => (boundedAboveFlatCoefficientAmbientBassDiagram P j).obj a)
      (fun j => (boundedAboveFlatCoefficientAmbientBassTransition P j).app a) n i
      (s, ((finiteRestriction P i).app a).map n x) :=
  telescopeRestriction_cylinder P a n i s x

example (i : ℕ) :
    Telescope.diagramInclusion (globalDiagram P) (globalTransition P) i ≫
      telescopeRestriction P =
    finiteRestriction P i ≫ boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i :=
  telescopeRestriction_inclusion P i

example (a : Under R) : IsStableEquivalence ((telescopeRestriction P).app a) :=
  telescopeRestriction_isStableEquivalence P a
