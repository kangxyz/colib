module
import Colib.Topology.Prespectrum.PushoutStableEquivalence

open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.HomotopyPushout
universe u
noncomputable section
example {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B)
    (hA : IsStableEquivalence (mappingConeFiberComparison A.hom))
    (hB : IsStableEquivalence (mappingConeFiberComparison B.hom))
    (hl : IsStableEquivalence sq.left) (hc : IsStableEquivalence (mappingConeMap sq)) :
    IsStableEquivalence sq.right := right_isStableEquivalence_of_coneMap sq hA hB hl hc

example {A B C A' B' C' : LoopPrespectrum.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') :
    mappingConeMap (rightInclusionSquare f g f' g' a b c wf wg) ≫ rightConeCollapse f' g' =
      rightConeCollapse f g ≫
        mappingConeMap (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk f') a b wf.symm) :=
  rightConeCollapse_naturality f g f' g' a b c wf wg
