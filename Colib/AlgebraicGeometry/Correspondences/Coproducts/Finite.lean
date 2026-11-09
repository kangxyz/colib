/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Coproducts.Binary
public import Colib.AlgebraicGeometry.Sites.Smooth.FiniteCovers

/-!
# Gluing actual finite correspondences along finite disjoint unions

The finite total scheme is the same literal disjoint union used to normalize
Nisnevich covers. Correspondences out of this scheme glue uniquely from their
restrictions along its actual component graph cycles, including the empty union.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Coproducts/Finite.lean`,
blob `79f4914ab048a2b5ce01929405d41de35db8ef70`.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Cor
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- The correspondence out of a finite disjoint union with prescribed components. -/
def finiteCoproductDesc {T : Cor k} : {n : ℕ} →
    {Y : Fin n → SmoothSite (Spec (.of k))} →
    (∀ i, Cor.mk (Y i) ⟶ T) → (Cor.mk (SmoothSite.finiteCoproduct Y) ⟶ T)
  | 0, _, _ => 0
  | n + 1, Y, f =>
      (coproductIsColimit k (Cor.mk (Y 0))
        (Cor.mk (SmoothSite.finiteCoproduct (fun i : Fin n => Y i.succ)))).desc
          (BinaryCofan.mk (f 0) (finiteCoproductDesc (fun i : Fin n => f i.succ)))

@[reassoc (attr := simp)]
theorem finiteCoproductι_desc {n : ℕ} {T : Cor k}
    {Y : Fin n → SmoothSite (Spec (.of k))} (f : ∀ i, Cor.mk (Y i) ⟶ T)
    (i : Fin n) :
    (graphFunctor k).map (SmoothSite.finiteCoproductι Y i) ≫
      finiteCoproductDesc k f = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (coproductIsColimit k (Cor.mk (Y 0))
          (Cor.mk (SmoothSite.finiteCoproduct (fun i : Fin n => Y i.succ)))).fac
            (BinaryCofan.mk (f 0) (finiteCoproductDesc k (fun i : Fin n => f i.succ)))
              ⟨WalkingPair.left⟩
      · change (graphFunctor k).map
          (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) j ≫
            SmoothSite.coproductInr _ _) ≫ _ = _
        rw [Functor.map_comp]
        let ι : Cor.mk (Y j.succ) ⟶
            Cor.mk (SmoothSite.finiteCoproduct (fun i : Fin n => Y i.succ)) :=
          (graphFunctor k).map (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) j)
        let ρ : Cor.mk (SmoothSite.finiteCoproduct (fun i : Fin n => Y i.succ)) ⟶
            Cor.mk (SmoothSite.finiteCoproduct Y) :=
          (graphFunctor k).map (SmoothSite.coproductInr _ _)
        change (ι ≫ ρ) ≫ finiteCoproductDesc k f = _
        rw [Category.assoc]
        have h := (coproductIsColimit k (Cor.mk (Y 0))
          (Cor.mk (SmoothSite.finiteCoproduct (fun i : Fin n => Y i.succ)))).fac
            (BinaryCofan.mk (f 0) (finiteCoproductDesc k (fun i : Fin n => f i.succ)))
              ⟨WalkingPair.right⟩
        change ρ ≫ finiteCoproductDesc k f =
          finiteCoproductDesc k (fun i : Fin n => f i.succ) at h
        rw [h]
        exact ih _ _

/-- Component graph restrictions determine a correspondence on a finite disjoint union. -/
theorem finiteCoproduct_hom_ext {n : ℕ} {T : Cor k}
    {Y : Fin n → SmoothSite (Spec (.of k))}
    {α β : Cor.mk (SmoothSite.finiteCoproduct Y) ⟶ T}
    (h : ∀ i, (graphFunctor k).map (SmoothSite.finiteCoproductι Y i) ≫ α =
      (graphFunctor k).map (SmoothSite.finiteCoproductι Y i) ≫ β) : α = β := by
  induction n with
  | zero =>
      have : IsEmpty (Cor.mk (SmoothSite.finiteCoproduct Y)).toSmoothSite.left :=
        inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
      exact Subsingleton.elim α β
  | succ n ih =>
      apply BinaryCofan.IsColimit.hom_ext (coproductIsColimit k (Cor.mk (Y 0))
        (Cor.mk (SmoothSite.finiteCoproduct (fun i : Fin n => Y i.succ))))
      · exact h 0
      · apply ih
        intro i
        have hi := h i.succ
        change (graphFunctor k).map
          (SmoothSite.finiteCoproductι (fun j : Fin n => Y j.succ) i ≫
            SmoothSite.coproductInr _ _) ≫ α =
          (graphFunctor k).map
          (SmoothSite.finiteCoproductι (fun j : Fin n => Y j.succ) i ≫
            SmoothSite.coproductInr _ _) ≫ β at hi
        rw [Functor.map_comp] at hi
        let ι : Cor.mk (Y i.succ) ⟶
            Cor.mk (SmoothSite.finiteCoproduct (fun j : Fin n => Y j.succ)) :=
          (graphFunctor k).map (SmoothSite.finiteCoproductι (fun j : Fin n => Y j.succ) i)
        let ρ : Cor.mk (SmoothSite.finiteCoproduct (fun j : Fin n => Y j.succ)) ⟶
            Cor.mk (SmoothSite.finiteCoproduct Y) :=
          (graphFunctor k).map (SmoothSite.coproductInr _ _)
        change (ι ≫ ρ) ≫ α = (ι ≫ ρ) ≫ β at hi
        change ι ≫ ρ ≫ α = ι ≫ ρ ≫ β
        exact (Category.assoc _ _ _).symm.trans (hi.trans (Category.assoc _ _ _))

/-- Finite correspondence descent commutes with postcomposition. -/
@[reassoc]
theorem finiteCoproductDesc_comp {n : ℕ} {T T' : Cor k}
    {Y : Fin n → SmoothSite (Spec (.of k))} (f : ∀ i, Cor.mk (Y i) ⟶ T)
    (g : T ⟶ T') :
    finiteCoproductDesc k f ≫ g = finiteCoproductDesc k (fun i => f i ≫ g) := by
  apply finiteCoproduct_hom_ext k
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a : Cor.mk (Y i) ⟶ T => a ≫ g)
      (finiteCoproductι_desc k f i)).trans
        (finiteCoproductι_desc k (fun i => f i ≫ g) i).symm)

/-- Gluing actual graph cycles is the graph of the ordinary finite descendent. -/
theorem finiteCoproductDesc_graph {n : ℕ} {X : SmoothSite (Spec (.of k))}
    {Y : Fin n → SmoothSite (Spec (.of k))} (f : ∀ i, Y i ⟶ X) :
    finiteCoproductDesc k (fun i => (graphFunctor k).map (f i)) =
      (graphFunctor k).map (SmoothSite.finiteCoproductDesc f) := by
  let F (i : Fin n) : Cor.mk (Y i) ⟶ Cor.mk X := (graphFunctor k).map (f i)
  change finiteCoproductDesc k F = (graphFunctor k).map (SmoothSite.finiteCoproductDesc f)
  apply finiteCoproduct_hom_ext k
  intro i
  have hg : (graphFunctor k).map (SmoothSite.finiteCoproductι Y i) ≫
      (graphFunctor k).map (SmoothSite.finiteCoproductDesc f) = (graphFunctor k).map (f i) := by
    rw [← Functor.map_comp, SmoothSite.finiteCoproductι_desc]
  exact (finiteCoproductι_desc k F i).trans hg.symm

/-- Arbitrary finite systems of correspondence equations glue on the actual total scheme. -/
theorem finiteCoproductDesc_comp_eq {n : ℕ} {T T' : Cor k}
    {Y : Fin n → SmoothSite (Spec (.of k))} (f : ∀ i, Cor.mk (Y i) ⟶ T)
    (g : T ⟶ T') (h : Cor.mk (SmoothSite.finiteCoproduct Y) ⟶ T')
    (w : ∀ i, f i ≫ g = (graphFunctor k).map (SmoothSite.finiteCoproductι Y i) ≫ h) :
    finiteCoproductDesc k f ≫ g = h := by
  apply finiteCoproduct_hom_ext k
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a : Cor.mk (Y i) ⟶ T => a ≫ g)
      (finiteCoproductι_desc k f i)).trans (w i))

/-- The actual graph inclusions exhibit the same finite total scheme as a coproduct in `Cor`. -/
def finiteCoproductIsColimit {n : ℕ}
    (Y : Fin n → SmoothSite (Spec (.of k))) :
    IsColimit (Cofan.mk (Cor.mk (SmoothSite.finiteCoproduct Y))
      (fun i => (graphFunctor k).map (SmoothSite.finiteCoproductι Y i))) :=
  Cofan.IsColimit.mk _
    (fun s => finiteCoproductDesc k (fun i => s.inj i))
    (fun s i => finiteCoproductι_desc k (fun j => s.inj j) i)
    (fun s _m hm => finiteCoproduct_hom_ext k (fun i =>
      (hm i).trans (finiteCoproductι_desc k (fun j => s.inj j) i).symm))

end AlgebraicGeometry.Cor
