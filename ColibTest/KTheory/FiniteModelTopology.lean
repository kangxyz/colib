/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Bass.ModelDiagramSuspension
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped unitInterval
universe u v w

namespace KTheory.Bass
section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})
example (X : C) (m : ℕ) :
    T1Space ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space m) :=
  modelDiagramIterateSpaceT1Space Q i F X m

example (X : C) (m : ℕ)
    (hm : i + 2 ≤ m) (k : ℕ) (hk : k + i < m)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space m) :
    Subsingleton (HomotopyGroup.Pi k
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space m) x) :=
  modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F X m hm k hk x

end
end KTheory.Bass

namespace KTheory.Bass.FiniteConeTopology
section
variable {C : Type u} [Category.{v} C]
example (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (h : ∀ X m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (c : ℕ)
    (hπ : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x))
    (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : ((iterate Q i F).obj X).space (n + c + 2)) :
    Subsingleton (HomotopyGroup.Pi k (((iterate Q i F).obj X).space (n + c + 2)) x) :=
  iterate_homotopyGroup_subsingleton Q i F h c hπ X n k hk x

end
end KTheory.Bass.FiniteConeTopology

namespace Topology.LoopPrespectrum
section
example (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{u + 1} (pointPrespectrum.{u}.point n))) :=
  pointPrespectrum_point_homotopyExtensionProperty n

end
end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum
section
example (E : LoopPrespectrum.{u}) :
    parameterLooping E ≅ homotopyFiber (zeroHom pointPrespectrum E) :=
  pointFiberIso E

end
end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum
section
example
    (E : LoopPrespectrum.{u}) (c : ℕ) [∀ n, T1Space (E.space n)]
    (hE : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n))))
    (hπ : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x)) :
    IsStableEquivalence (suspensionLoopCounit E) :=
  suspensionLoopCounit_isStableEquivalence_of_linearGrowth E c hE hπ

end
end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum
section
example
    (E : LoopPrespectrum.{u}) (hE : IsStableEquivalence (suspensionLoopCounit E)) :
    IsStableEquivalence (suspensionLoopUnit (parameterLooping E)) :=
  suspensionLoopUnit_parameterLooping_isStableEquivalence E hE

end
end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum
section
example (E : LoopPrespectrum.{u}) (c : ℕ)
    (hE : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n))))
    (hπ : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
    (n : ℕ) (x : (parameterLooping (suspensionCone E)).space (n + (c + 1) + 2))
    (k : ℕ) (hk : k < n + 2) :
    Subsingleton (HomotopyGroup.Pi k
      ((parameterLooping (suspensionCone E)).space (n + (c + 1) + 2)) x) :=
  suspensionLoop_homotopyGroup_subsingleton E c hE hπ n x k hk

end
end Topology.LoopPrespectrum

namespace KTheory.Bass.ModelDiagramSuspension
section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})
example (X : C) :
    IsStableEquivalence (suspensionLoopUnit
      (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X)) :=
  unit_stable Q i F X

example (X : C) (c : ℕ) (hc : i + 1 ≤ c)
    (n k : ℕ) (hk : k < n + 2)
    (x : (parameterLooping (suspensionCone
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).space (n + c + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((parameterLooping (suspensionCone
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X))).space (n + c + 2)) x) :=
  homotopyGroup_subsingleton_at_offset Q i F X c hc n k hk x

end
end KTheory.Bass.ModelDiagramSuspension

end
