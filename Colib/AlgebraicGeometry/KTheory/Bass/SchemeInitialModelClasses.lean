/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeStageZeroComparison
public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparison

/-! # Original nonnegative Model classes in the independent current-stage inclusion -/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan

/-- The current class uses the original Model K/stable map and its literal initial inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInitialModelClasses.lean:22"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def currentModelClass (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (x : (M.obj X).obj.waldhausen.K n) :
    stableHomotopyGroup ((currentTelescope A).obj X) (n : ℤ) :=
  (stableHomotopyFunctor (n : ℤ)).map ((currentInitial A).app X)
    (smallModelKStableEquiv (M.obj X) n (Additive.ofMul x))

/-- The stable zigzag preserves this independent original Model class, including degree zero. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeInitialModelClasses.lean:30"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem currentIteratedStableIso_modelClass (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) (x : (M.obj X).obj.waldhausen.K n) :
    (currentIteratedStableIso M A X (n : ℤ)).hom (currentModelClass M A X n x) =
      (stableHomotopyFunctor (n : ℤ)).map ((iteratedInitial A).app X)
        (smallModelKStableEquiv (M.obj X) n (Additive.ofMul x)) :=
  ConcreteCategory.congr_hom (currentIteratedStableIso_initial M A X (n : ℤ))
    (smallModelKStableEquiv (M.obj X) n (Additive.ofMul x))

end KTheory.Bass.SchemeNaturalSeed
