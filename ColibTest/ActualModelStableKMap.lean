module
import Colib.KTheory.Waldhausen.Iterated.ModelStableKMap

open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
noncomputable section

example (W : WideSubcategory preservesZero.{u}) (n : ℕ) :
    smallModelKStableEquiv W n =
      levelOneStableEquiv (prespectrum W) (prespectrum_isOmega W) n := rfl

example {W V : WideSubcategory preservesZero.{u}} (f : W ⟶ V)
    (n : ℕ) (hf : Function.Injective (KMap f.hom.isExact n)) :
    Function.Injective ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)) :=
  prespectrumMap_stable_nonnegative_injective f n hf

example {W V : WideSubcategory preservesZero.{u}} (f : W ⟶ V)
    (n : ℕ) (hf : Function.Surjective (KMap f.hom.isExact n)) :
    Function.Surjective ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap f)) :=
  prespectrumMap_stable_nonnegative_surjective f n hf

example (W : WideSubcategory preservesZero.{u}) (k : ℕ) :
    Subsingleton (stableHomotopyGroup (prespectrum W) (-((k : ℤ) + 1))) :=
  prespectrum_stableHomotopyGroup_neg_subsingleton W _ (by omega)
