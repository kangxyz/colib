module
import Colib.KTheory.Bass.LoopFactor

open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.HomotopyPushout
open Topology.LoopPrespectrum.HomotopyPushout.Looping
universe u
noncomputable section
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

example : inl (parameterLoopingMap f) (parameterLoopingMap g) ≫ comparison f g =
    parameterLoopingMap (inl f g) := comparison_left f g
example : inr (parameterLoopingMap f) (parameterLoopingMap g) ≫ comparison f g =
    parameterLoopingMap (inr f g) := comparison_right f g
example (S : Arrow (Arrow LoopPrespectrum.{u})) :
    KTheory.Bass.LoopFactor.loopSquare S =
      parameterLoopingFunctor.mapArrow.mapArrow.obj S := rfl
example (S : Arrow (Arrow LoopPrespectrum.{u})) :
    comparison S.left.hom S.hom.left ≫ parameterLoopingMap (StrictSquare.comparison S) =
      StrictSquare.comparison (KTheory.Bass.LoopFactor.loopSquare S) :=
  KTheory.Bass.LoopFactor.span_square S
