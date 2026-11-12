/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveExtensionCocycle
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionZerothHomotopy
public import Colib.KTheory.GrothendieckComparison.LoopComponents
public import Colib.KTheory.GrothendieckComparison.PathPotential
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionLoops
public import Colib.Topology.ClassifyingSpace.FiberPotential

/-!
# Original completion-loop classes and the sign of the Q-cocycle

The original homotopy fiber and its potential calculations remain unchanged.
The canonical comparison reverses the loop/fiber inverse and therefore has input grade
minus displayed basepoint grade. Original Q cocycles, K-groups, and grades are unchanged.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveCompletionLoopKZero.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Topology
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- The original vertex path, with only the exact realization-map endpoint equality inserted. -/
def completionQVertexPath (U : GroupCompletionCategory R) :
    Path (classifyingSpaceMapUniversal (localizedExtensionProjection R)
      (classifyingSpacePoint ((completionIdentityEntry R).obj U)))
      (classifyingSpacePoint (exactStructure R).qZero) :=
  (classifyingSpacePath ((completionIdentityProjectionIsoZero R).inv.app U)).symm.cast
    (classifyingSpaceMapUniversal_point (localizedExtensionProjection R) _) rfl

/-- The original fiber vertex has exactly the identity-extension source and original Q-edge path. -/
theorem completionQFiberPoint_vertex (U : GroupCompletionCategory R) :
    completionQFiberPoint R U = HomotopyFiber.pointWithPath
      (classifyingSpaceMapUniversal (localizedExtensionProjection R))
      (classifyingSpacePoint ((completionIdentityEntry R).obj U))
      (classifyingSpacePoint (exactStructure R).qZero) (completionQVertexPath R U) := by
  apply Subtype.ext
  apply Prod.ext
  · exact completionToOriginalQHomotopyFiber_vertex_source R U
  · apply ContinuousMap.ext
    intro t
    exact completionToOriginalQHomotopyFiber_vertex_path R U t

/-- The zero-apex arrow to an identity quotient is its unchanged zero-isomorphism inverse. -/
theorem fromZero_completionIdentityProjection (U : GroupCompletionCategory R) :
    (exactStructure R).fromZero
      ((localizedExtensionProjection R).obj ((completionIdentityEntry R).obj U)) =
        (completionIdentityProjectionIsoZero R).inv.app U := by
  apply (cancel_mono ((completionIdentityProjectionIsoZero R).hom.app U)).1
  rw [Iso.inv_hom_id_app]
  exact (exactStructure R).qZero_endomorphism_eq_id _

/-- The actual fundamental-groupoid potential for the unchanged localized projection. -/
def completionQPathPotential :
    classifyingFundamentalGroupoidFunctor (LocalizedExtensionCategory R) ⋙
      FundamentalGroupoid.map (classifyingSpaceMapUniversal (localizedExtensionProjection R)) ⟶
        (Functor.const (LocalizedExtensionCategory R)).obj
          (FundamentalGroupoid.mk (classifyingSpacePoint (exactStructure R).qZero)) :=
  (exactStructure R).realizedQCocyclePotential (localizedExtensionProjection R)
    (localizedExtensionPotential R) (qGrothendieckWeight_localizedExtensionProjection R)

/-- On an original identity entry the potential is its stored fiber path followed by its algebraic
grade. -/
theorem completionQPathPotential_entry (U : GroupCompletionCategory R) :
    (completionQPathPotential R).app ((completionIdentityEntry R).obj U) =
      (Path.Homotopic.Quotient.mk (completionQVertexPath R U) :
        FundamentalGroupoid.mk (classifyingSpaceMapUniversal (localizedExtensionProjection R)
          (classifyingSpacePoint ((completionIdentityEntry R).obj U))) ⟶
            FundamentalGroupoid.mk (classifyingSpacePoint (exactStructure R).qZero)) ≫
        ((exactStructure R).grothendieckLoopClass
          (Multiplicative.ofAdd (completionGrade R U))).asHom := by
  dsimp only [completionQPathPotential,
    CategoryTheory.ExactCategory.ExactStructure.realizedQCocyclePotential,
    NatTrans.comp_app, classifyingFundamentalGroupoidUniversalNaturality,
    CategoryTheory.ExactCategory.ExactStructure.qCocyclePotential]
  simp only [← Groupoid.inv_eq_inv, fromZero_completionIdentityProjection]
  change eqToHom (congrArg FundamentalGroupoid.mk
    (classifyingSpaceMapUniversal_point (localizedExtensionProjection R)
      ((completionIdentityEntry R).obj U))) ≫
        (((Path.Homotopic.Quotient.mk
          (classifyingSpacePath ((completionIdentityProjectionIsoZero R).inv.app U))).symm :
            FundamentalGroupoid.mk (classifyingSpacePoint
              ((localizedExtensionProjection R).obj ((completionIdentityEntry R).obj U))) ⟶
                FundamentalGroupoid.mk (classifyingSpacePoint (exactStructure R).qZero)) ≫
          ((exactStructure R).grothendieckLoopClass
            (Multiplicative.ofAdd (completionGrade R U))).asHom) = _
  rw [← Category.assoc]
  congr 1
  dsimp only [completionQVertexPath]
  rw [Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_symm]
  have h := FundamentalGroupoid.conj_eqToHom
    (p := (Path.Homotopic.Quotient.mk
      (classifyingSpacePath ((completionIdentityProjectionIsoZero R).inv.app U))).symm)
    (classifyingSpaceMapUniversal_point (localizedExtensionProjection R)
      ((completionIdentityEntry R).obj U)) rfl
  simpa only [eqToHom_refl, Category.comp_id] using h

/-- The standard comparison has input grade minus displayed basepoint grade on each vertex. -/
theorem completionToOriginalQLoops_vertex_class (U V : GroupCompletionCategory R) :
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (completionToOriginalQLoops R U (classifyingSpacePoint V))) :
        FundamentalGroup (exactStructure R).KSpace (exactStructure R).kBasepoint) =
      (exactStructure R).grothendieckLoopClass
        (Multiplicative.ofAdd (completionGrade R V - completionGrade R U)) := by
  let : ContractibleSpace (ClassifyingSpace (LocalizedExtensionCategory R)) :=
    localizedExtension_classifyingSpace_contractible R
  have hfiber : (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((originalQLoopFiberHomotopyEquiv R U).invFun (completionQFiberPoint R V))) :
        FundamentalGroup (exactStructure R).KSpace (exactStructure R).kBasepoint) =
      (exactStructure R).grothendieckLoopClass
        (Multiplicative.ofAdd (completionGrade R U - completionGrade R V)) := by
    apply CategoryTheory.End.ext
    change Path.Homotopic.Quotient.mk
      ((HomotopyFiber.loopEquivOfContractibleSourcePath
        (classifyingSpaceMapUniversal (localizedExtensionProjection R))
        (completionQFiberPoint R U).val.1 (classifyingSpacePoint (exactStructure R).qZero)
        (HomotopyFiber.toPath _ _ (completionQFiberPoint R U))).invFun
          (completionQFiberPoint R V)) = _
    rw [completionQFiberPoint_vertex R U, completionQFiberPoint_vertex R V]
    exact loopInverse_classifyingSpace_potential
      (classifyingSpaceMapUniversal (localizedExtensionProjection R))
      (classifyingSpacePoint (exactStructure R).qZero) (completionQPathPotential R)
      (exactStructure R).grothendieckLoopClass
      ((completionIdentityEntry R).obj U) ((completionIdentityEntry R).obj V)
      (Multiplicative.ofAdd (completionGrade R U))
      (Multiplicative.ofAdd (completionGrade R V))
      (completionQVertexPath R U) (completionQVertexPath R V)
      (completionQPathPotential_entry R U) (completionQPathPotential_entry R V)
  have h := congrArg (Inv.inv (α := FundamentalGroup
    (exactStructure R).KSpace (exactStructure R).kBasepoint)) hfiber
  have hi := (map_inv (exactStructure R).grothendieckLoopClass
    (Multiplicative.ofAdd (completionGrade R U - completionGrade R V))).symm
  rw [← ofAdd_neg, neg_sub] at hi
  apply Eq.trans ?_ hi
  convert h using 1 <;> rfl

/-- The standard comparison induces its literal map on actual path components. -/
def completionToOriginalQLoopsComponents (U : GroupCompletionCategory R) :
    ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R)) →
      ZerothHomotopy (Path (exactStructure R).kBasepoint (exactStructure R).kBasepoint) :=
  ZerothHomotopy.lift
    (fun x ↦ ZerothHomotopy.mk (completionToOriginalQLoops R U x))
    (fun _ _ p ↦ ZerothHomotopy.sound (p.map (completionToOriginalQLoops R U).continuous))

/-- A component representative passes through the exact standard continuous map. -/
@[simp] theorem completionToOriginalQLoopsComponents_mk (U : GroupCompletionCategory R)
    (x : ClassifyingSpace (GroupCompletionCategory R)) :
    completionToOriginalQLoopsComponents R U (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (completionToOriginalQLoops R U x) := rfl

/-- The standard Q-loop label is input component class divided by displayed basepoint class. -/
theorem completionToOriginalQLoopsComponents_kZero (U : GroupCompletionCategory R)
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R))) :
    (exactStructure R).loopComponentsKZeroEquiv (completionToOriginalQLoopsComponents R U a) =
      completionZerothHomotopyKZeroEquiv R a / completionKZeroClass R U := by
  obtain ⟨c, hc⟩ := (classifyingSpaceComponentsEquiv (GroupCompletionCategory R)).surjective a
  obtain ⟨V, rfl⟩ := Quotient.exists_rep c
  rw [classifyingSpaceComponentsEquiv_mk] at hc
  subst a
  rw [completionToOriginalQLoopsComponents_mk,
    CategoryTheory.ExactCategory.ExactStructure.loopComponentsKZeroEquiv_mk,
    completionZerothHomotopyKZeroEquiv_point]
  apply (exactStructure R).kZeroFundamentalGroupEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  erw [completionToOriginalQLoops_vertex_class]
  dsimp only [CategoryTheory.ExactCategory.ExactStructure.grothendieckLoopClass,
    MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, completionKZeroClass]
  rw [ofAdd_sub, map_div, map_div]
  rfl

/-- A zero-grade displayed basepoint gives exactly the preexisting algebraic label. -/
theorem completionToOriginalQLoopsComponents_kZero_of_grade_zero
    (U : GroupCompletionCategory R) (hU : completionGrade R U = 0)
    (a : ZerothHomotopy (ClassifyingSpace (GroupCompletionCategory R))) :
    (exactStructure R).loopComponentsKZeroEquiv (completionToOriginalQLoopsComponents R U a) =
      completionZerothHomotopyKZeroEquiv R a := by
  rw [completionToOriginalQLoopsComponents_kZero]
  have h : completionKZeroClass R U = 1 := by
    simp only [completionKZeroClass, hU, ofAdd_zero, map_one]
  rw [h, div_one]

/-- The actual additive zero pair has its unchanged algebraic grade zero. -/
@[simp] theorem completionGrade_completionZeroPair :
    completionGrade R (completionZeroPair R) = 0 :=
  completionGrade_diagonal R _

/-- The actual canonical additive-zero-pair comparison has the standard algebraic label. -/
theorem originalQComparison_kZero (x : ClassifyingSpace (GroupCompletionCategory R)) :
    (exactStructure R).loopComponentsKZeroEquiv (ZerothHomotopy.mk (originalQComparison R x)) =
      completionZerothHomotopyKZeroEquiv R (ZerothHomotopy.mk x) :=
  completionToOriginalQLoopsComponents_kZero_of_grade_zero R (completionZeroPair R)
    (completionGrade_completionZeroPair R) (ZerothHomotopy.mk x)

end ModuleCat.FiniteProjective
