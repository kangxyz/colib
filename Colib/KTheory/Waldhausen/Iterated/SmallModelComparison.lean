/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.StableHomotopy
public import Colib.KTheory.Waldhausen.ExactEquivalence

/-! # Canonical K-maps of direct small models on zero spaces and stable groups -/
@[expose] public section
noncomputable section
open CategoryTheory Topology SSet
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology.LoopPrespectrum
variable (W : WideSubcategory preservesZero.{u})

/-- The original K-group maps to the actual first stable stage by the displayed structure map. -/
def smallModelKStableStageEquiv (n : ℕ) :
    Additive (W.obj.waldhausen.K n) ≃+ (stableSystem (prespectrum W) (n : ℤ)).obj 0 :=
  (structurePiEquiv (prespectrum W) (prespectrum_isOmega W) 1 n).toAdditive.trans
      (nonnegativeStableStageEquiv (prespectrum W) n)

/-- Every nonnegative actual stable homotopy group is the unchanged original K-group,
including degree zero and its group law. -/
def smallModelKStableEquiv (n : ℕ) :
    Additive (W.obj.waldhausen.K n) ≃+ stableHomotopyGroup (prespectrum W) (n : ℤ) :=
  (smallModelKStableStageEquiv W n).trans
    (stableHomotopyStageZeroIso (prespectrum W) (prespectrum_isOmega W) (n :
      ℤ)).symm.addCommGroupIsoToAddEquiv

/-- The comparison is exactly the original first-stage inclusion after the displayed K-stage map. -/
theorem smallModelKStableEquiv_apply (n : ℕ) (a : Additive (W.obj.waldhausen.K n)) :
    smallModelKStableEquiv W n a = stableHomotopyι (prespectrum W) (n : ℤ) 0
      (smallModelKStableStageEquiv W n a) := by
  change (stableHomotopyStageZeroIso (prespectrum W) (prespectrum_isOmega W) (n
    : ℤ)).inv
    (smallModelKStableStageEquiv W n a) = _
  rw [stableHomotopyStageZeroIso_inv]

variable {W V : WideSubcategory preservesZero.{u}} (F : W ⟶ V)

/-- The strict model map acts on the actual zeroth loop space by its canonical K-map. -/
theorem smallModelZeroSpace_naturality (n : ℕ) (a : W.obj.waldhausen.K n) :
    zeroSpaceHomotopyEquiv V n (KMap F.hom.isExact n a) =
      HomotopyGroup.map ((prespectrumMap F).map 0) ((prespectrumMap F).map_point 0)
        (zeroSpaceHomotopyEquiv W n a) := by
  rw [KMap_eq_piMap_of_zeroEq F.hom.isExact F.property]
  exact loopShiftEquiv_natural n (deloopingMap F.hom.isExact).hom (stageMap_point 0 F) a

/-- The first actual stable stage retains the unchanged original K-map. -/
theorem smallModelKStableStageEquiv_naturality (n : ℕ) (a : W.obj.waldhausen.K n) :
    smallModelKStableStageEquiv V n (Additive.ofMul (KMap F.hom.isExact n a)) =
      (stableSystemMap (prespectrumMap F) (n : ℤ)).app 0
        (smallModelKStableStageEquiv W n (Additive.ofMul a)) := by
  have hs := KMap_eq_piMap_of_zeroEq F.hom.isExact F.property n
  change nonnegativeStableStageEquiv (prespectrum V) n
    (Additive.ofMul (structurePiMap (prespectrum V) 1 n
      (KMap F.hom.isExact n a))) =
    (stableSystemMap (prespectrumMap F) (n : ℤ)).app 0
      (nonnegativeStableStageEquiv (prespectrum W) n
        (Additive.ofMul (structurePiMap (prespectrum W) 1 n a)))
  rw [← nonnegativeStableStageEquiv_naturality]
  apply congrArg (nonnegativeStableStageEquiv (prespectrum V) n)
  apply congrArg Additive.ofMul
  change structurePiMap (prespectrum V) 1 n (KMap F.hom.isExact n a) =
    HomotopyGroup.piMap (n+1) ((prespectrumMap F).map 2)
      ((prespectrumMap F).map_point 2)
      (structurePiMap (prespectrum W) 1 n a)
  rw [hs]
  exact congrArg (fun h ↦ h a)
    (structurePiMap_naturality (prespectrumMap F) 1 n)

/-- The actual stable map is exactly the unchanged original K-map under the constructed
equivalence. -/
theorem smallModelKStableEquiv_naturality (n : ℕ) (a : W.obj.waldhausen.K n) :
    smallModelKStableEquiv V n (Additive.ofMul (KMap F.hom.isExact n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap F)
        (smallModelKStableEquiv W n (Additive.ofMul a)) := by
  rw [smallModelKStableEquiv_apply, smallModelKStableEquiv_apply,
    smallModelKStableStageEquiv_naturality F]
  exact (ConcreteCategory.congr_hom
    (stableHomotopyι_naturality (prespectrumMap F) (n : ℤ) 0)
    (smallModelKStableStageEquiv W n (Additive.ofMul a))).symm

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0357",
  colib_ref "Waldhausen1985" "Section 1.3, Proposition 1.3.1, pp. 330-331" "background"
    "Actual exact-functor maps and weak-natural-transformation invariance"]
  CategoryTheory.Waldhausen.IteratedS.smallModelKStableEquiv
  CategoryTheory.Waldhausen.IteratedS.smallModelZeroSpace_naturality
  CategoryTheory.Waldhausen.IteratedS.smallModelKStableEquiv_naturality
