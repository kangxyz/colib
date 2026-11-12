/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.FiniteRepresentatives.LiftIndependence
public import Colib.AlgebraicGeometry.Correspondences.Graph.PostcompositionPointControl

/-!
# Packing actual signed lift families into the literal disjoint union

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Sheaf/Germs/FiniteRepresentatives/FamilyAssembly.lean`,
blob `57212348ac7b97701381e42b739bf98d4c5722f6`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u v

namespace AlgebraicGeometry.Cor
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {U Y : SmoothSite (Spec (.of k))}
  {n m : ℕ} (V : Fin n → SmoothSite (Spec (.of k))) (label : Fin m → Fin n)
  (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)))

/-- The original signed sum followed by actual component graph injections. -/
def packFiniteFamily : Cor.mk U ⟶ Cor.mk (SmoothSite.finiteCoproduct V) :=
  ∑ j, β j ≫ (graphFunctor k).map (SmoothSite.finiteCoproductι V (label j))

/-- Packing preserves the exact graph image, including signed cancellation. -/
theorem packFiniteFamily_comp_graph (q : ∀ i, V i ⟶ Y) :
    packFiniteFamily k (U := U) V label β ≫
      (graphFunctor k).map (SmoothSite.finiteCoproductDesc q) =
      ∑ j, β j ≫ (graphFunctor k).map (q (label j)) := by
  let ι (j : Fin m) : Cor.mk (V (label j)) ⟶ Cor.mk (SmoothSite.finiteCoproduct V) :=
    (graphFunctor k).map (SmoothSite.finiteCoproductι V (label j))
  let Q : Cor.mk (SmoothSite.finiteCoproduct V) ⟶ Cor.mk Y :=
    (graphFunctor k).map (SmoothSite.finiteCoproductDesc q)
  change (∑ j, β j ≫ ι j) ≫ Q = _
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  have h : ι j ≫ Q = (graphFunctor k).map (q (label j)) :=
    ((graphFunctor k).map_comp _ _).symm.trans
      (congrArg (graphFunctor k).map (SmoothSite.finiteCoproductι_desc q (label j)))
  exact (Category.assoc _ _ _).trans (congrArg (fun δ ↦ β j ≫ δ) h)

/-- All-point designated-center control is preserved by the actual signed packing. -/
theorem packFiniteFamily_target_control (chosen : ∀ i, (V i).left) (x : U.left)
    (hβ : ∀ j, finiteCorrespondences.TargetsIn (f := U.hom) (g := (V (label j)).hom)
      (β j) x {chosen (label j)}) :
    finiteCorrespondences.TargetsIn (f := U.hom) (g := (SmoothSite.finiteCoproduct V).hom)
      (packFiniteFamily k (U := U) V label β) x
      (Set.range (fun i => (SmoothSite.finiteCoproductι V i).left (chosen i))) := by
  classical
  let terms (j : Fin m) : finiteCorrespondences U.hom (SmoothSite.finiteCoproduct V).hom :=
    β j ≫ (graphFunctor k).map (SmoothSite.finiteCoproductι V (label j))
  change finiteCorrespondences.TargetsIn (∑ j, terms j) x _
  refine finiteCorrespondences.TargetsIn.sum Finset.univ terms (fun j _ ↦ ?_)
  intro b hb t ht
  refine ⟨label j, ?_⟩
  symm
  apply target_eq_of_comp_graph k (X := U) (β j) (SmoothSite.finiteCoproductι V (label j))
    x (chosen (label j)) ?_ b hb t ht
  intro a d hd
  apply hβ j a.val ?_ d hd
  simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using a.property

end AlgebraicGeometry.Cor

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {U : SmoothSite (Spec (.of k))} {n m : ℕ}
  (V : Fin n → SmoothSite (Spec (.of k))) (label : Fin m → Fin n)
  (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)))

/-- Actual transfer on the packed signed family is exactly the finite sum of
transfers on the original component restrictions. -/
theorem transfer_packFiniteFamily
    (s : P.sections (Cor.mk (SmoothSite.finiteCoproduct V))) :
    P.transfer (Cor.packFiniteFamily k (U := U) V label β) s =
      ∑ j, P.transfer (β j)
        (((toPresheaf k).obj P).map (SmoothSite.finiteCoproductι V (label j)).op s) := by
  let e : (Cor.mk U ⟶ Cor.mk (SmoothSite.finiteCoproduct V)) →+ P.sections (Cor.mk U) :=
    { toFun := fun γ => P.transfer γ s
      map_zero' := by simp
      map_add' := fun γ δ => by simp only [transfer_add, AddCommGrpCat.hom_add_apply] }
  change e (∑ j, β j ≫ (Cor.graphFunctor k).map (SmoothSite.finiteCoproductι V (label j))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  let ι : Cor.mk (V (label j)) ⟶ Cor.mk (SmoothSite.finiteCoproduct V) :=
    (Cor.graphFunctor k).map (SmoothSite.finiteCoproductι V (label j))
  change P.transfer (β j ≫ ι) s = P.transfer (β j) (P.transfer ι s)
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (transfer_comp P (β j) ι) s

end AlgebraicGeometry.PresheafWithTransfers
