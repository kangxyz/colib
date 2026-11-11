/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Bass.FiniteConeLoopTopology
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.FiniteConeTopology
variable {C : Type u} [Category.{v} C]

example (j : ℕ) (E : LoopPrespectrum.{w})
    [∀ m, T1Space (E.space m)] (m : ℕ) : T1Space ((loops j E).space m) :=
  loopsSpaceT1Space j E m

example (j : ℕ) (E : LoopPrespectrum.{w})
    [∀ m, T1Space (E.space m)]
    (h : ∀ m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} (E.point m)))) (m : ℕ) :
    TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((loops j E).point m))) :=
  loops_point_homotopyExtensionProperty j E h m

example (j : ℕ) (E : LoopPrespectrum.{w}) (c : ℕ)
    (hπ : ∀ n k, k < n + 2 → ∀ x : E.space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
    (n k : ℕ) (hk : k < n + 2) (x : (loops j E).space (n + (c + j) + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((loops j E).space (n + (c + j) + 2)) x) :=
  loops_homotopyGroup_subsingleton j E c hπ n k hk x

example (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ)
    (F : C ⥤ WideSubcategory preservesZero.{w}) (X : C) (m : ℕ) :
    T1Space ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space m) :=
  modelLoopsIterateSpaceT1Space Q i j F X m

example
    (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})
    (X : C) (m : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).point m))) :=
  modelLoopsIterate_point_homotopyExtensionProperty Q i j F X m

example
    (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})
    (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : (loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space (n + j + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space (n + j + 2)) x) :=
  modelLoopsIterate_homotopyGroup_subsingleton Q i j F X n k hk x

end KTheory.Bass.FiniteConeTopology
end
