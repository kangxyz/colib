/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputMixedDesc
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputCommutingSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputConeSource

/-!
# The original Laurent evaluation face at the strict diagonal

The zero-to-three edge is the unchanged Laurent input evaluation. Its compact face is constant
in the independent source-cylinder height because the original strict comparison is constant
there. No equality of evaluated values is used to replace its full reference nodes.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputLaurentFace
open GlobalSectionChangeIndex

/-- The original five composition nodes retain their complete anchors. -/
def firstNodes {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (i : Fin 5) :
    CommonReferenceNerve.Node (InputSimplex.sourceMap f g) :=
  ⟨InputSimplex.vertices f g i, InputSimplex.anchors f g i⟩

/-- The unchanged first evaluation edge inside its original composition diagram. -/
def firstCurve {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :=
  (CommonReferenceNerve.parameter (InputSimplex.sourceMap f g) (firstNodes f g)).comp
    (SimplexParameters.edge (k := 4) 0 3).toContinuousMap

private theorem first_native {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    PathLift (InputSimplex.simplex f g) (SimplexParameters.edge (k := 4) 0 3)
      (InputCommutingSquare.firstLeg f g) := by
  have h := PathLift.trans_left _
    (HomotopyLift.target _ (InputSimplex.composition_native f g))
  intro n r x
  exact h n r x

/-- The entire compact first-edge family is the original strict-precomposed evaluation track. -/
theorem firstCurve_native {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputSimplex.sourceMap f g)
      (firstCurve f g) n = (InputCommutingSquare.firstLeg f g).level n := by
  apply ContinuousMap.ext
  rintro ⟨r, x⟩
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputSimplex.sourceMap f g) (firstCurve f g) (firstNodes f g) r
    (SimplexParameters.edge (k := 4) 0 3 r) rfl n x).trans ?_
  exact first_native f g n r x

private theorem first_leg_whole {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    (InputCommutingSquare.firstLeg f g).level n =
      ((evaluationComparison f).level n).comp
        ⟨fun z => (z.1, (sectionMap g).map n z.2), by fun_prop⟩ := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual Laurent evaluation edge in precisely the fixed mixed reference. -/
def curve : C(unitInterval,
    |nerve (Codiscrete (CommonReferenceNerve.Node (InputMixedDesc.sourceMap g)))|) :=
  firstCurve (laurent.map g) (GlobalRawBass.laurentProjection.app Y)

/-- The source face retains its independent cylinder height, along which it is constant. -/
def parameter : C(unitInterval × unitInterval,
    |nerve (Codiscrete (CommonReferenceNerve.Node (InputMixedDesc.sourceMap g)))|) :=
  (curve g).comp ContinuousMap.fst

/-- Every height has the same literal Laurent carrier path. -/
theorem parameter_apply (r s : unitInterval) : parameter g (r, s) = curve g r := rfl

/-- The entire compact two-coordinate face retains the original first-leg family. -/
theorem native_level (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g) (parameter g) n =
      ((InputCommutingSquare.firstLeg (laurent.map g)
        (GlobalRawBass.laurentProjection.app Y)).level n).comp
        ⟨fun z => (z.1.1, z.2), by fun_prop⟩ := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  obtain ⟨k, N, z, hz⟩ := CommonReferenceNerve.exists_parameter
    (InputMixedDesc.sourceMap g) (curve g r)
  have hp : parameter g (r, s) = CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) N z :=
    hz.symm
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputMixedDesc.sourceMap g) (parameter g) N (r, s) z hp n x).trans
      ((CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
        (InputMixedDesc.sourceMap g) (curve g) N r z hz.symm n x).symm.trans
          (DFunLike.congr_fun
            (firstCurve_native (laurent.map g) (GlobalRawBass.laurentProjection.app Y) n) (r, x)))

/-- The whole L0 face is the original Laurent evaluation at the actual strict diagonal. -/
theorem diagonal_native_level (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g) (parameter g) n =
      ((evaluationComparison (laurent.map g)).level n).comp
        ⟨fun z => (z.1.1, (StrictSquare.comparison (sectionSquare Y)).map n
          (HomotopyPushout.cylinder (sectionMap (projection.app Y))
            (sectionMap (projection.app Y)) n (z.1.2, z.2))), by
          exact (continuous_fst.comp continuous_fst).prodMk
            (((StrictSquare.comparison (sectionSquare Y)).map n).continuous.comp
              ((HomotopyPushout.cylinder (sectionMap (projection.app Y))
                (sectionMap (projection.app Y)) n).continuous.comp (by fun_prop)))⟩ := by
  rw [native_level, first_leg_whole, ContinuousMap.comp_assoc]
  apply congrArg (fun P => ((evaluationComparison (laurent.map g)).level n).comp P)
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  exact Prod.ext rfl (strict_comparison_cylinder Y n s x).symm

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputLaurentFace
