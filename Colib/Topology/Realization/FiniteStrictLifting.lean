/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HELP.StrictFiniteCriterion
public import Colib.Topology.Realization.FiniteCompact
public import Colib.Topology.Realization.MapWeakEquivalence

/-!
# Detecting weak realization equivalences by finite subcomplexes

For a monomorphism, a retraction and a homotopy on every finite target
subcomplex suffice when their boundary values agree with the original map.
The finite strict cube test retains the entire original boundary.
This is the finite lifting criterion used for bounded subpresheaves in
Jardine, *Simplicial presheaves*, Lemma 2.4, pp. 65–66.
https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory Topology
open scoped Simplicial unitInterval

universe u

namespace SSet

/-- Relative homotopies of finite target inclusions through the original source
imply weakness of a monomorphism. -/
theorem isRealizationWeakEquivalence_of_finiteSubcomplex_lifting
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (h : ∀ (A : Y.Subcomplex), SSet.Finite A →
      ∃ (r : C(|(A : SSet.{u})|, |X|))
        (H : ((SSet.toTop.map f).hom.comp r).Homotopy (SSet.toTop.map A.ι).hom),
        ∀ (t : unitInterval) (x : |(A : SSet.{u})|),
          (SSet.toTop.map A.ι) x ∈ Set.range (SSet.toTop.map f) →
            H (t, x) = (SSet.toTop.map A.ι) x) :
    IsRealizationWeakEquivalence f := by
  let F := (SSet.toTop.map f).hom
  have hF : Function.Injective F := (realization_mono_isClosedEmbedding f).injective
  apply FiniteCubeStrictHELP.isWeakHomotopyEquivalence (f := F)
  intro n a b hb
  let i := CubicalTests.boundaryInclusion.{u} n
  let : CompactSpace (CubicalTests.cube.{u} n) := inferInstance
  obtain ⟨A, hA, b', hB⟩ := realization_continuousMap_factors_finiteSubcomplex b
  obtain ⟨r, H, hH⟩ := h A hA
  have ha (x : CubicalTests.boundary.{u} n) :
      (SSet.toTop.map A.ι) (b' (i x)) = F (a x) := by
    exact (ContinuousMap.congr_fun hB (i x)).trans (ContinuousMap.congr_fun hb x).symm
  have hr (x : CubicalTests.boundary.{u} n) : r (b' (i x)) = a x :=
    hF (((H.map_zero_left (b' (i x))).symm.trans
      (hH 0 (b' (i x)) ⟨a x, (ha x).symm⟩)).trans (ha x))
  refine ⟨r.comp b', ContinuousMap.ext hr,
    ⟨{ toHomotopy := (H.compContinuousMap b').cast rfl hB, prop' := ?_ }⟩⟩
  rintro t _ ⟨x, rfl⟩
  exact (hH t (b' (i x)) ⟨a x, (ha x).symm⟩).trans
    ((ha x).trans (congrArg F (hr x).symm))

end SSet
