/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSeedCospan
public import Colib.KTheory.Bass.LoopFactor

/-!
# The double Laurent face of the two finite cone comparisons

The actual geometric comparison carries the original double Laurent inclusion
through the original contravariant product swap. The parameter-loop comparison
carries the same inclusion without that swap. Both equations are equalities of
actual prespectrum maps, and their value formulas retain an arbitrary based
loop and its independent time. No equality or inequality between the two full
comparisons, and no tower comparison, is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
universe u w
namespace KTheory.Bass.DoubleLaurentInclusion
open GeometricSquareInterchange SquareConeStrength
open PushoutCofiberSquare

/-- The original unlooped cone diagram of the geometric Bass square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DoubleLaurentInclusion.lean:36"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
def geometricCone (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  mappingConeDiagram (comparison (geometricSquare F))

/-- The unchanged Laurent target inclusion into the original comparison cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DoubleLaurentInclusion.lean:41"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
def laurentInclusion (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    F.obj (laurent.op.obj X) ⟶ (geometricCone F).obj X :=
  mappingConeInclusion ((comparison (geometricSquare F)).app X)

/-- The exact contravariant direction of the two original Laurent-factor swap. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DoubleLaurentInclusion.lean:46"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
def doubleLaurentSwap (X : Scheme.{u}ᵒᵖ) :
    laurent.op.obj (laurent.op.obj X) ⟶ laurent.op.obj (laurent.op.obj X) :=
  (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
    (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op

variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)

/-- The first Laurent face is transported by the original geometric eta. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DoubleLaurentInclusion.lean:54"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
theorem chiGeom_laurentInclusion :
    laurentInclusion ((strictDiagramFunctor squareFunctor).obj F) X ≫
        (GeometricSeedCospan.chiGeom F).app X =
      (eta (laurentProjection (.of (ULift.{u} ℤ))) F).hom.app X ≫
        (((strictDiagramFunctor squareFunctor).map
          (coneInclusion (comparison (geometricSquare F)))).app X) := by
  have h := WholeSeedCospan.chiAlong_inclusion (geometricSquare F)
    squareFunctor (squareInterchangeMap F) X
  rw [squareInterchange_laurent] at h
  exact h

/-- The geometric comparison retains the original double Laurent swap. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DoubleLaurentInclusion.lean:66"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
theorem geometric_doubleLaurent :
    parameterLoopingMap (laurentInclusion F (laurent.op.obj X)) ≫
        laurentInclusion ((strictDiagramFunctor squareFunctor).obj F) X ≫
        (GeometricSeedCospan.chiGeom F).app X =
      parameterLoopingMap (F.map (doubleLaurentSwap X) ≫
        laurentInclusion F (laurent.op.obj X) ≫ laurentInclusion (geometricCone F) X) := by
  rw [chiGeom_laurentInclusion]
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  rfl

/-- The original loop-distribution comparison has no geometric variable swap. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DoubleLaurentInclusion.lean:82"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
theorem looping_doubleLaurent :
    parameterLoopingMap (laurentInclusion F (laurent.op.obj X)) ≫
        laurentInclusion ((strictDiagramFunctor squareFunctor).obj F) X ≫
        LoopFactor.coneStrength
          ((geometricCone F).mapArrow.mapArrow.obj (square X)) =
      parameterLoopingMap
        (laurentInclusion F (laurent.op.obj X) ≫ laurentInclusion (geometricCone F) X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  rfl

/-- The geometric equation on an actual based loop at its unchanged time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DoubleLaurentInclusion.lean:98"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
theorem geometric_doubleLaurent_apply (n : ℕ)
    (γ : Path ((F.obj (laurent.op.obj (laurent.op.obj X))).point n)
      ((F.obj (laurent.op.obj (laurent.op.obj X))).point n)) (t : unitInterval) :
    Path.toContinuousMap (((GeometricSeedCospan.chiGeom F).app X).map n
      ((laurentInclusion ((strictDiagramFunctor squareFunctor).obj F) X).map n
        ((parameterLoopingMap (laurentInclusion F (laurent.op.obj X))).map n γ))) t =
      (laurentInclusion (geometricCone F) X).map n
        ((laurentInclusion F (laurent.op.obj X)).map n
          ((F.map (doubleLaurentSwap X)).map n (γ t))) := by
  exact congrArg (fun f => Path.toContinuousMap (f.map n γ) t)
    (geometric_doubleLaurent F X)

/-- The loop-distribution equation on the same based loop and unchanged time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DoubleLaurentInclusion.lean:111"
  "adaptation" "Original double Laurent face and actual geometric scalar-cell equations."]
theorem looping_doubleLaurent_apply (n : ℕ)
    (γ : Path ((F.obj (laurent.op.obj (laurent.op.obj X))).point n)
      ((F.obj (laurent.op.obj (laurent.op.obj X))).point n)) (t : unitInterval) :
    Path.toContinuousMap ((LoopFactor.coneStrength
      ((geometricCone F).mapArrow.mapArrow.obj (square X))).map n
        ((laurentInclusion ((strictDiagramFunctor squareFunctor).obj F) X).map n
          ((parameterLoopingMap (laurentInclusion F (laurent.op.obj X))).map n γ))) t =
      (laurentInclusion (geometricCone F) X).map n
        ((laurentInclusion F (laurent.op.obj X)).map n (γ t)) := by
  exact congrArg (fun f => Path.toContinuousMap (f.map n γ) t)
    (looping_doubleLaurent F X)

end KTheory.Bass.DoubleLaurentInclusion
