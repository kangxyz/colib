/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.RankedChain.Resolution
public import Colib.Topology.ClassifyingSpace.AsSmall
public import Colib.Topology.Realization.VertexHEP
public import Colib.Topology.Homotopy.Equiv.BasedReplacement
public import Colib.Topology.Homotopy.Equiv.BasedLoop

/-!
# Original classifying-space loops and the actual poset resolution

The proved poset-resolution homotopy equivalence sends the canonical
singleton-chain vertex to the original categorical vertex. Vertex HEP
constructs a based inverse and point-fixed inverse homotopies, which then
loop to a genuine equivalence of the actual compact-open loop spaces.

In particular, loops of the original Q classifying space reduce to loops of
a poset nerve. This does not yet supply a realization model or CW type for
either loop space.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/ClassifyingSpace/PosetLoop.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped Topology unitInterval

universe u v
namespace CategoryTheory.RankedChainOrder

variable (C : Type u) [SmallCategory C]

/-- The singleton chain at the singleton semisimplex of the original object. -/
def resolutionVertex (c : C) : ResolutionPoset C :=
  vertex (SemisimplexResolution.Obj C) SemisimplexResolution.Obj.dim
    (SemisimplexResolution.vertexObj C c)

@[simp]
theorem resolutionFunctor_vertex (c : C) :
    (resolutionFunctor C).obj (resolutionVertex C c) = c := rfl

/-- The original resolution homotopy equivalence is strictly based at this vertex. -/
theorem resolutionHomotopyEquiv_vertex (c : C) :
    resolutionHomotopyEquiv C (classifyingSpacePoint (resolutionVertex C c)) =
      classifyingSpacePoint c := by
  rw [resolutionHomotopyEquiv_toFun, classifyingSpaceMap_point, resolutionFunctor_vertex]

/-- Proved point cofibrancy corrects the actual inverse, leaving the original
resolution map fixed and making both inverse homotopies point-fixed. -/
def resolutionBasedHomotopyEquiv (c : C) :
    BasedHomotopyEquiv (classifyingSpacePoint (resolutionVertex C c)) (classifyingSpacePoint c) :=
  BasedHomotopyEquiv.ofHomotopyEquiv (resolutionHomotopyEquiv C)
    (resolutionHomotopyEquiv_vertex C c)
    (SSet.homotopyExtensionProperty_vertex (nerveVertex (resolutionVertex C c)))
    (SSet.homotopyExtensionProperty_vertex (nerveVertex c))

@[simp]
theorem resolutionBasedHomotopyEquiv_toMap (c : C) :
    (resolutionBasedHomotopyEquiv C c).toMap =
      (classifyingSpaceMap (resolutionFunctor C)).hom :=
  resolutionHomotopyEquiv_toFun C

/-- Actual compact-open loops in the poset resolution and original category
are genuinely homotopy equivalent. No loop-CW hypothesis is assumed. -/
def resolutionLoopHomotopyEquiv (c : C) :
    ContinuousMap.HomotopyEquiv
      (Path (classifyingSpacePoint (resolutionVertex C c))
        (classifyingSpacePoint (resolutionVertex C c)))
      (Path (classifyingSpacePoint c) (classifyingSpacePoint c)) :=
  (resolutionBasedHomotopyEquiv C c).loopHomotopyEquiv

/-- Its forward map is exactly looping the original categorical resolution map. -/
theorem resolutionLoopHomotopyEquiv_toFun (c : C) :
    (resolutionLoopHomotopyEquiv C c).toFun =
      basedLoopMap (classifyingSpaceMap (resolutionFunctor C)).hom
        (classifyingSpaceMap_point (resolutionFunctor C) (resolutionVertex C c)) := by
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  exact ContinuousMap.congr_fun (resolutionBasedHomotopyEquiv_toMap C c) (γ t)

/-- The original constant loop is preserved exactly. -/
@[simp]
theorem resolutionLoopHomotopyEquiv_refl (c : C) :
    resolutionLoopHomotopyEquiv C c
        (Path.refl (classifyingSpacePoint (resolutionVertex C c))) =
      Path.refl (classifyingSpacePoint c) :=
  (resolutionBasedHomotopyEquiv C c).loopHomotopyEquiv_refl

end CategoryTheory.RankedChainOrder

namespace CategoryTheory.RankedChainOrder

variable (C : Type u) [Category.{v} C]

/-- The actual resolution vertex after the proved common-universe homeomorphism. -/
def universalResolutionVertex (c : C) : ResolutionPoset (AsSmall.{0} C) :=
  resolutionVertex (AsSmall.{0} C) (AsSmall.up.obj c)

/-- The poset-resolution equivalence, transported to the unchanged original
classifying space when its object and morphism universes differ. -/
def universalResolutionHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (ResolutionPoset (AsSmall.{0} C))) (ClassifyingSpace C) :=
  (resolutionHomotopyEquiv (AsSmall.{0} C)).trans
    (CategoryTheory.asSmallClassifyingHomeomorph C).symm.toHomotopyEquiv

/-- The original vertex survives both actual equivalences exactly. -/
theorem universalResolutionHomotopyEquiv_vertex (c : C) :
    universalResolutionHomotopyEquiv C
        (classifyingSpacePoint (universalResolutionVertex C c)) = classifyingSpacePoint c := by
  change (CategoryTheory.asSmallClassifyingHomeomorph C).symm
    (resolutionHomotopyEquiv (AsSmall.{0} C)
      (classifyingSpacePoint (resolutionVertex (AsSmall.{0} C) (AsSmall.up.obj c)))) = _
  rw [resolutionHomotopyEquiv_vertex,
    ← CategoryTheory.asSmallClassifyingHomeomorph_point]
  exact (CategoryTheory.asSmallClassifyingHomeomorph C).symm_apply_apply _

/-- A based inverse with point-fixed homotopies for the original categorical space. -/
def universalResolutionBasedHomotopyEquiv (c : C) :
    BasedHomotopyEquiv (classifyingSpacePoint (universalResolutionVertex C c))
      (classifyingSpacePoint c) :=
  BasedHomotopyEquiv.ofHomotopyEquiv (universalResolutionHomotopyEquiv C)
    (universalResolutionHomotopyEquiv_vertex C c)
    (SSet.homotopyExtensionProperty_vertex (nerveVertex (universalResolutionVertex C c)))
    (SSet.homotopyExtensionProperty_vertex (nerveVertex c))

/-- The actual compact-open loop equivalence for independent category universes. -/
def universalResolutionLoopHomotopyEquiv (c : C) :
    ContinuousMap.HomotopyEquiv
      (Path (classifyingSpacePoint (universalResolutionVertex C c))
        (classifyingSpacePoint (universalResolutionVertex C c)))
      (Path (classifyingSpacePoint c) (classifyingSpacePoint c)) :=
  (universalResolutionBasedHomotopyEquiv C c).loopHomotopyEquiv

/-- The common-universe passage does not change the original constant loop. -/
@[simp]
theorem universalResolutionLoopHomotopyEquiv_refl (c : C) :
    universalResolutionLoopHomotopyEquiv C c
        (Path.refl (classifyingSpacePoint (universalResolutionVertex C c))) =
      Path.refl (classifyingSpacePoint c) :=
  (universalResolutionBasedHomotopyEquiv C c).loopHomotopyEquiv_refl

end CategoryTheory.RankedChainOrder
