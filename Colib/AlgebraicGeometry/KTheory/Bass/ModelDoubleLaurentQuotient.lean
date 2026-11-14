/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.ConnectiveConeQuotient
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeDoubleLaurent
public import Colib.KTheory.Bass.TwoChartStableSequence
public import Colib.KTheory.Waldhausen.Iterated.FiniteConnectivity
public import Colib.KTheory.Waldhausen.Iterated.PointHEP

/-!
# Original double-Laurent representatives in degree zero

The actual Model levels supply zero-offset growth. Each original unlooped
geometric cone preserves it, so the original double-Laurent inclusion is an
epimorphism on degree-zero stable groups. Both inner and both outer chart
relations vanish under this same map. This avoids all negative-degree casts.

Adapted from the original construction in
`Quillen/KTheory/Bass/ModelDoubleLaurentQuotient.lean`.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.GeometricConeInterchange

/-- The original target inclusion with its explicit geometric corner endpoints. -/
def coneInclusion (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    F.obj (laurent.op.obj X) ⟶ (coneFunctor.obj F).obj X :=
  mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (square X)))

private theorem doubleLaurentInclusion_zero_eq
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    (stableHomotopyFunctor 0).map (doubleLaurentInclusion F X) =
      (stableHomotopyFunctor 0).map (coneInclusion F (laurent.op.obj X)) ≫
        (stableHomotopyFunctor 0).map (coneInclusion (coneFunctor.obj F) X) :=
  (stableHomotopyFunctor 0).map_comp
    (coneInclusion F (laurent.op.obj X)) (coneInclusion (coneFunctor.obj F) X)

/-- Original Model points and finite connectivity give the actual zero-offset cone input. -/
theorem model_linearZeroGrowth (M : WideSubcategory preservesZero.{w}) :
    LinearZeroGrowth (prespectrumFunctor.obj M) where
  point := prespectrum_point_homotopyExtensionProperty M
  vanishing n x k hk :=
    prespectrum_positiveLevel_homotopyGroup_subsingleton_at M (n + 1) k (by omega) x

/-- The original unlooped geometric cone keeps the same degree-zero connectivity. -/
theorem cone_linearZeroGrowth (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : Scheme.{u}ᵒᵖ) :
    LinearZeroGrowth ((coneFunctor.obj F).obj X) :=
  LinearZeroGrowth.cone (F.mapArrow.mapArrow.obj (square X))
    (hF (square X).left.left) (hF (square X).left.right)
    (hF (square X).right.left) (hF (square X).right.right)

/-- The original first unlooped inclusion is surjective on actual stable degree zero. -/
theorem coneInclusion_zero_epi (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : Scheme.{u}ᵒᵖ) :
    Epi ((stableHomotopyFunctor 0).map
      (coneInclusion F X)) :=
  LinearZeroGrowth.inclusion_epi (F.mapArrow.mapArrow.obj (square X))
    (hF (square X).left.left) (hF (square X).left.right)
    (hF (square X).right.left) (hF (square X).right.right)

/-- Every degree-zero double-cone class has an original double-Laurent representative. -/
theorem doubleLaurentInclusion_zero_epi (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (X : Scheme.{u}ᵒᵖ) :
    Epi ((stableHomotopyFunctor 0).map
      (doubleLaurentInclusion (M ⋙ prespectrumFunctor) X)) := by
  let F := M ⋙ prespectrumFunctor
  have hF : ∀ Y, LinearZeroGrowth (F.obj Y) := fun Y => model_linearZeroGrowth (M.obj Y)
  let := coneInclusion_zero_epi F hF (laurent.op.obj X)
  let := coneInclusion_zero_epi (coneFunctor.obj F) (cone_linearZeroGrowth F hF) X
  rw [doubleLaurentInclusion_zero_eq]
  infer_instance

/-- Actual strict-square naturality preserves the original degree-zero target inclusion. -/
@[reassoc]
theorem coneInclusion_zero_naturality (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (stableHomotopyFunctor 0).map (F.map (laurent.op.map f)) ≫
        (stableHomotopyFunctor 0).map
          (coneInclusion F Y) =
      (stableHomotopyFunctor 0).map
          (coneInclusion F X) ≫
        (stableHomotopyFunctor 0).map ((coneFunctor.obj F).map f) :=
  KTheory.Bass.TwoChartStable.comparisonConeMap_inclusion
    (F.mapArrow.mapArrow.map (squareFunctor.map f)) 0

/-- The positive chart vanishes under the original first cone inclusion. -/
@[reassoc]
theorem coneInclusion_zero_plus (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : Scheme.{u}ᵒᵖ) :
    (stableHomotopyFunctor 0).map (F.map ((NatTrans.op plus).app X)) ≫
      (stableHomotopyFunctor 0).map
        (coneInclusion F X) = 0 :=
  LinearZeroGrowth.left_zero (F.mapArrow.mapArrow.obj (square X))
    (hF (square X).left.left) (hF (square X).left.right)
    (hF (square X).right.left) (hF (square X).right.right)

/-- The inverse chart vanishes under the original first cone inclusion. -/
@[reassoc]
theorem coneInclusion_zero_minus (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : Scheme.{u}ᵒᵖ) :
    (stableHomotopyFunctor 0).map (F.map ((NatTrans.op minus).app X)) ≫
      (stableHomotopyFunctor 0).map
        (coneInclusion F X) = 0 :=
  LinearZeroGrowth.right_zero (F.mapArrow.mapArrow.obj (square X))
    (hF (square X).left.left) (hF (square X).left.right)
    (hF (square X).right.left) (hF (square X).right.right)

/-- The original inner positive relation dies in the original double cone. -/
theorem doubleLaurentInclusion_zero_inner_plus (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : Scheme.{u}ᵒᵖ) :
    (stableHomotopyFunctor 0).map (F.map ((NatTrans.op plus).app (laurent.op.obj X))) ≫
      (stableHomotopyFunctor 0).map (doubleLaurentInclusion F X) = 0 := by
  rw [doubleLaurentInclusion_zero_eq,
    ← Category.assoc, coneInclusion_zero_plus F hF, zero_comp]

/-- The original inner inverse relation dies in the original double cone. -/
theorem doubleLaurentInclusion_zero_inner_minus (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : Scheme.{u}ᵒᵖ) :
    (stableHomotopyFunctor 0).map (F.map ((NatTrans.op minus).app (laurent.op.obj X))) ≫
      (stableHomotopyFunctor 0).map (doubleLaurentInclusion F X) = 0 := by
  rw [doubleLaurentInclusion_zero_eq,
    ← Category.assoc, coneInclusion_zero_minus F hF, zero_comp]

/-- Actual inclusion naturality sends the outer positive relation to the second chart. -/
theorem doubleLaurentInclusion_zero_outer_plus (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : Scheme.{u}ᵒᵖ) :
    (stableHomotopyFunctor 0).map (F.map (laurent.op.map ((NatTrans.op plus).app X))) ≫
      (stableHomotopyFunctor 0).map (doubleLaurentInclusion F X) = 0 := by
  rw [doubleLaurentInclusion_zero_eq,
    ← Category.assoc, coneInclusion_zero_naturality, Category.assoc,
    coneInclusion_zero_plus (coneFunctor.obj F) (cone_linearZeroGrowth F hF), comp_zero]

/-- Actual inclusion naturality sends the outer inverse relation to the second chart. -/
theorem doubleLaurentInclusion_zero_outer_minus (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (X : Scheme.{u}ᵒᵖ) :
    (stableHomotopyFunctor 0).map (F.map (laurent.op.map ((NatTrans.op minus).app X))) ≫
      (stableHomotopyFunctor 0).map (doubleLaurentInclusion F X) = 0 := by
  rw [doubleLaurentInclusion_zero_eq,
    ← Category.assoc, coneInclusion_zero_naturality, Category.assoc,
    coneInclusion_zero_minus (coneFunctor.obj F) (cone_linearZeroGrowth F hF), comp_zero]

end KTheory.Bass.GeometricConeInterchange
