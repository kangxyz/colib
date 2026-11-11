module
import Colib.KTheory.Bass.NormalizedStageMapStable

open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open KTheory.Bass KTheory.Bass.FiniteConeTopology KTheory.Bass.IteratedLoopStrength
open KTheory.Bass.NormalizedStageMap
universe u v w
noncomputable section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C)

example (i j : ℕ) : IsStableEquivalence
    ((iteratedStrength Q j (iterate Q i (M ⋙ prespectrumFunctor))).app X) :=
  iterated_model_stable Q i j M X
example (i : ℕ) : IsStableEquivalence ((stageMap Q i (M ⋙ prespectrumFunctor)).app X) :=
  model_stageMap_stable Q i M X
example {S T : Arrow (Arrow LoopPrespectrum.{w})} (a : S ⟶ T)
    (hS : IsStableEquivalence (mappingConeFiberComparison (StrictSquare.comparison S)))
    (hT : IsStableEquivalence (mappingConeFiberComparison (StrictSquare.comparison T)))
    (hs : IsStableEquivalence (StrictSquare.spanMap a))
    (hf : IsStableEquivalence a.right.right) :
    IsStableEquivalence (strictSquareLoopedConeFunctor.map a) :=
  strictSquareLoopedConeFunctor_map_isStableEquivalence_of_excision a hS hT hs hf
