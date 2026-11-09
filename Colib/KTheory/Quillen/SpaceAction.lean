/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Homotopy.HomotopyGroup.HSpaceAction
public import Colib.KTheory.Waldhausen.QuillenComparison.Equivalence
public import Colib.KTheory.Waldhausen.Iterated.OmegaSpectrum

/-!
# Trivial loop action on the original Quillen space

Every loop at the original Q-zero basepoint acts trivially by path transport
on every finite homotopy group of the original Q-space. The actual Q/S
comparison, its specified inverse-homotopy track, the small-model delooping
homeomorphism and the iterated-S loop map give an actual weak equivalence
into a loop H-space. No multiplicativity of Q/S is assumed.

The degree-two specialization supplies the genuine source group law for the
original degree-zero self-track operation. This theorem alone does not identify
an ordered-symbol marking or an original matrix representative.
-/
/-! Implementation provenance: `Quillen/KTheory/SpaceAction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual Q/S comparison,
native as-small Waldhausen model and original zero basepoint are retained. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuillenComparison
  CategoryTheory.Waldhausen.IteratedS Topology
open scoped Topology
universe u v
namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The original Q-space has trivial based-loop transport, in every finite
homotopy degree, through the actual Q/S and iterated-S maps. -/
theorem qSpace_pathTransport_loop (E : ExactStructure C)
    (p : Path E.kBasepoint E.kBasepoint) (n : ℕ)
    (a : HomotopyGroup.Pi n E.KSpace E.kBasepoint) :
    pathTransport p n a = a := by
  let W := ofExactCategory E
  let M := asSmallCategory W
  let small : C(W.Delooping, stageSpace 0 M) :=
    W.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
  let e := realizationComparisonHomotopyEquiv E
  let k : C(SubdivisionSpace E, Path (stagePoint 1 M) (stagePoint 1 M)) :=
    (stageLoopMap 0 M).comp (small.comp (realizationEndpoint E).hom)
  let f : C(E.KSpace, Path (stagePoint 1 M) (stagePoint 1 M)) := k.comp e.invFun
  have he : IsWeakHomotopyEquivalence (realizationEndpoint E).hom :=
    isWeakHomotopyEquivalence_of_homotopyEquiv
      (SSet.EdgewiseSubdivision.realizationHomotopyEquiv
        (sSet E.inflation (MorphismProperty.isomorphisms C)))
  have hs : IsWeakHomotopyEquivalence small :=
    isWeakHomotopyEquivalence_of_homotopyEquiv W.asSmallDeloopingHomeomorph.toHomotopyEquiv
  have hk : IsWeakHomotopyEquivalence k := (stageLoopMap_weak 0 M).comp (hs.comp he)
  have hf : IsWeakHomotopyEquivalence f :=
    hk.comp (isWeakHomotopyEquivalence_of_homotopyEquiv e.symm)
  have hb : e (subdivisionBasepoint E) = E.kBasepoint :=
    realizationComparison_basepoint E
  let d : Path (e.invFun E.kBasepoint) (subdivisionBasepoint E) :=
    (e.left_inv.some.evalAt (subdivisionBasepoint E)).cast
      (congrArg e.invFun hb).symm rfl
  have hsmall : small W.kBasepoint = stagePoint 0 M :=
    W.asSmallDeloopingHomeomorph_basepoint
  have hkb : k (subdivisionBasepoint E) = Path.refl (stagePoint 1 M) := by
    change stageLoopMap 0 M (small (realizationEndpoint E (subdivisionBasepoint E))) = _
    rw [realizationEndpoint_basepoint E, hsmall]
    exact stageLoopMap_point 0 M
  let γ : Path (f E.kBasepoint) HSpace.e :=
    (d.map k.continuous).cast rfl hkb.symm
  exact pathTransport_loop_trivial_of_hSpace_detection f E.kBasepoint γ n
    (hf.homotopy_bijective E.kBasepoint n).injective p a

/-- Q1 marking specialization: the object loop acts trivially on the actual
Pi 2 of BQ, without replacement of its basepoint or homotopy-group model. -/
theorem qSpace_piTwo_pathTransport_loop (E : ExactStructure C)
    (p : Path E.kBasepoint E.kBasepoint)
    (a : HomotopyGroup.Pi 2 E.KSpace E.kBasepoint) : pathTransport p 2 a = a :=
  qSpace_pathTransport_loop E p 2 a

end CategoryTheory.ExactCategory

attribute [colib_ref "quillen"
  "Quillen/KTheory/SpaceAction.lean:41-83"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  CategoryTheory.ExactCategory.qSpace_pathTransport_loop
  CategoryTheory.ExactCategory.qSpace_piTwo_pathTransport_loop
