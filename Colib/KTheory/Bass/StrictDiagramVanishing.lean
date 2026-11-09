/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.StrictDiagramPointHEP
public import Colib.Topology.Prespectrum.StrictSquareVanishing

/-!
# Quantified finite vanishing under actual Bass iteration

Every application of the original strict Bass endofunctor loses one degree, by the genuine
pushout, cone and parameter-loop proofs. The original diagram's point HEP and T1 properties
propagate through all iterates. At stage i the original level is n+c+i+2 and vanishing is below
n+2; the explicit cutoff excludes unsupported low-level component assertions.
-/
/-! Implementation provenance: `Quillen/KTheory/Bass/StrictDiagramVanishing.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- One unchanged Bass step raises the actual linear vanishing offset by exactly one. -/
theorem strictDiagramFunctor_homotopyGroup_subsingleton
    (F : C ⥤ LoopPrespectrum.{w})
    (h : ∀ X m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (c : ℕ)
    (hπ : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x))
    (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space (n + (c + 1) + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      ((((strictDiagramFunctor Q).obj F).obj X).space (n + (c + 1) + 2)) x) := by
  have he : n + (c + 1) + 2 = (n + 1) + c + 2 := by omega
  revert x
  rw [he]
  intro x
  exact LoopPrespectrum.StrictSquare.loopedCone_homotopyGroup_subsingleton
    (F.mapArrow.mapArrow.obj (Q.obj X)) ((n + 1) + c + 2) (n + 1)
    (h (Q.obj X).left.left _) (h (Q.obj X).left.right _)
    (h (Q.obj X).right.left _) (h (Q.obj X).right.right _)
    (fun a j hj ↦ hπ (Q.obj X).left.left (n + 1) j hj a)
    (fun b j hj ↦ hπ (Q.obj X).left.right (n + 1) j hj b)
    (fun d j hj ↦ hπ (Q.obj X).right.left (n + 1) j hj d)
    (fun d j hj ↦ hπ (Q.obj X).right.right (n + 1) j hj d) x k hk

/-- Each finite original Bass iterate has the explicitly proved linear offset and high-level
cutoff, with no new connectivity hypothesis on later stages. -/
theorem strictDiagramIterate_homotopyGroup_subsingleton (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w}) [∀ X m, T1Space ((F.obj X).space m)]
    (h : ∀ X m, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1} ((F.obj X).point m))))
    (c : ℕ)
    (hπ : ∀ X n k, k < n + 2 → ∀ x : (F.obj X).space (n + c + 2),
      Subsingleton (HomotopyGroup.Pi k ((F.obj X).space (n + c + 2)) x))
    (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : (((strictDiagramIterate Q i).obj F).obj X).space (n + (c + i) + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      ((((strictDiagramIterate Q i).obj F).obj X).space (n + (c + i) + 2)) x) := by
  induction i generalizing F c with
  | zero => exact hπ X n k hk x
  | succ i ih =>
    have he : n + (c + (i + 1)) + 2 = n + ((c + 1) + i) + 2 := by omega
    revert x
    rw [he]
    intro x
    exact ih ((strictDiagramFunctor Q).obj F)
      (strictDiagramFunctor_point_homotopyExtensionProperty Q F h) (c + 1)
      (strictDiagramFunctor_homotopyGroup_subsingleton Q F h c hπ) x

end KTheory.Bass

attribute [colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramVanishing.lean:27"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  KTheory.Bass.strictDiagramFunctor_homotopyGroup_subsingleton

attribute [colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramVanishing.lean:53"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  KTheory.Bass.strictDiagramIterate_homotopyGroup_subsingleton
