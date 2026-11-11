/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Bass.ModelRowZigzagBackward

noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v w

namespace Topology.LoopPrespectrum
section


example (E : LoopPrespectrum.{u}) :
    suspensionCone (parameterLooping E) ⟶ E :=
  suspensionLoopCounit E

end
end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum
section


example (E : LoopPrespectrum.{u}) :
    suspensionLoopUnit (parameterLooping E) ≫
      parameterLoopingMap (suspensionLoopCounit E) = 𝟙 (parameterLooping E) :=
  suspensionLoopUnit_counit E

end
end Topology.LoopPrespectrum

namespace KTheory.Bass.ModelDiagramSuspension
section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

example (X : C) :
    ((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X =
      parameterLooping ((ConeTrack.diagram Q
        ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X) :=
  successor_obj Q i F X

end
end KTheory.Bass.ModelDiagramSuspension

namespace KTheory.Bass.ModelDiagramRowStabilizedTarget
section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})

example (X : C) :
    suspensionLoopUnit (parameterLooping (cone Q i F X)) ≫ refinement Q i F X =
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i F X) :=
  unit_refinement Q i F X

example (X : C) :
    suspensionLoopUnit
        (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X) ≫
      currentRefinement Q i F X =
    eqToHom (ModelDiagramSuspension.successor_obj Q i F X) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i F X) :=
  current_unit_refinement Q i F X

end
end KTheory.Bass.ModelDiagramRowStabilizedTarget

namespace KTheory.Bass.ModelRowZigzagSequentialization
section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C)

example (n : ℕ) :
    backward Q M X n = eqToHom (ModelDiagramSuspension.successor_obj Q n M X) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q n M X) :=
  backward_eq Q M X n

end
end KTheory.Bass.ModelRowZigzagSequentialization
