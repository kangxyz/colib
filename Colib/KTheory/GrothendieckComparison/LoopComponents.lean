/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.KTheory.GrothendieckComparison.ObjectLoops
public import Colib.Topology.ClassifyingSpace.FundamentalGroup
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.FundamentalGroup
public import Colib.KTheory.Quillen.Map.Functoriality
public import Colib.Topology.Homotopy.HomotopyGroup.FundamentalGroup

/-!
# Components of the original Q-loop space are the original K₀

This is precisely the existing loop-degree shift and the standard zeroth
homotopy quotient, transported through the unchanged fundamental-group
identification. An actual loop is sent to its original homotopical K₀ class.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/GrothendieckComparison/LoopComponents.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
open Topology CategoryTheory
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The original loop shift identifies actual Q-loop components with unchanged Quillen K₀. -/
def loopComponentsKZeroEquiv :
    ZerothHomotopy (Path E.kBasepoint E.kBasepoint) ≃ E.K 0 :=
  ((E.kZeroFundamentalGroupEquiv.toEquiv.trans
    (fundamentalGroupLoopComponentEquiv E.kBasepoint)).trans
      HomotopyGroup.pi0EquivZerothHomotopy).symm

/-- Every actual original loop retains its path-quotient fundamental-group class. -/
@[simp] theorem loopComponentsKZeroEquiv_mk (γ : Path E.kBasepoint E.kBasepoint) :
    E.loopComponentsKZeroEquiv (ZerothHomotopy.mk γ) =
      E.kZeroFundamentalGroupEquiv.symm (FundamentalGroup.fromPath ⟦γ⟧) := by
  apply E.loopComponentsKZeroEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  change ZerothHomotopy.mk γ = HomotopyGroup.pi0EquivZerothHomotopy
    (fundamentalGroupLoopComponentEquiv E.kBasepoint
      (E.kZeroFundamentalGroupEquiv
        (E.kZeroFundamentalGroupEquiv.symm (FundamentalGroup.fromPath ⟦γ⟧))))
  rw [MulEquiv.apply_symm_apply, fundamentalGroupLoopComponentEquiv_path]
  rfl

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor
open Topology CategoryTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The original normalized-Q loop map induces exactly the original K₀ map. -/
theorem loopComponentsKZeroEquiv_naturality (F : ExactFunctor EC ED)
    (γ : Path EC.kBasepoint EC.kBasepoint) :
    F.KMap 0 (EC.loopComponentsKZeroEquiv (ZerothHomotopy.mk γ)) =
      ED.loopComponentsKZeroEquiv (ZerothHomotopy.mk
        (basedLoopMap (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point γ)) := by
  rw [CategoryTheory.ExactCategory.ExactStructure.loopComponentsKZeroEquiv_mk,
    CategoryTheory.ExactCategory.ExactStructure.loopComponentsKZeroEquiv_mk]
  apply ED.kZeroFundamentalGroupEquiv.injective
  rw [MulEquiv.apply_symm_apply, F.KMap_eq_piMap]
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map (classifyingSpaceMap F.normalizedQ).hom
      F.normalizedQ_map_point (EC.kZeroFundamentalGroupEquiv.symm
        (FundamentalGroup.fromPath ⟦γ⟧))) = _
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  change FundamentalGroup.mapOfEq _ _
    (EC.kZeroFundamentalGroupEquiv
      (EC.kZeroFundamentalGroupEquiv.symm (FundamentalGroup.fromPath ⟦γ⟧))) = _
  rw [MulEquiv.apply_symm_apply, FundamentalGroup.mapOfEq_apply]
  rfl

end CategoryTheory.ExactCategory.ExactFunctor
