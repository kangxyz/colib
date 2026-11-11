module
import Colib.KTheory.Bass.FiniteConeStrength

open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.HomotopyPushout.Looping
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open KTheory.Bass KTheory.Bass.LoopFactor KTheory.Bass.LoopStrength
universe u v w
noncomputable section
example (E : LoopPrespectrum.{u}) [∀ n, T1Space (E.space n)]
    (h : HEP E) : HEP (parameterLooping E) := loop_hep E h
example (E : LoopPrespectrum.{u}) (c : ℕ) (h : Growth E c) :
    Growth (parameterLooping E) (c + 1) := loop_growth E c h
example {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    strength Q F X =
      parameterLoopingMap (coneStrength (F.mapArrow.mapArrow.obj (Q.obj X))) ≫
        (LoopTranspose.iso
          (mappingCone (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))).hom :=
  LoopStable.strength_factor Q F X
example {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ)
    (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C) :
    IsStableEquivalence (strength Q
      (FiniteParameterLooping.loopDiagram j
        (FiniteConeTopology.iterate Q i (M ⋙ prespectrumFunctor))) X) :=
  FiniteConeStrength.model_strength_stable Q i j M X
