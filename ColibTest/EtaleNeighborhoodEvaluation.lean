/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEvaluation
import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite

universe u

noncomputable section

variable (k : Type u) [Field k] (X : Scheme.SmoothSite (Spec (.of k)))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left)
  (P : PresheafWithTransfers.{u + 1} k)

example {A B : EtaleNeighborhood X ξ} (f : A ⟶ B) :
    ((PresheafWithTransfers.toPresheaf k).obj P).map
        ((etaleNeighborhoodToSmooth X ξ).map f).op =
      PresheafWithTransfers.transfer P
        ((Cor.graphFunctor k).map ((etaleNeighborhoodToSmooth X ξ).map f)) := rfl

example {A B : EtaleNeighborhood X ξ} (f : A ⟶ B) :
    PresheafWithTransfers.transfer P
        ((Cor.graphFunctor k).map ((etaleNeighborhoodToSmooth X ξ).map f)) ≫
      toEtaleNeighborhoodValue X ξ A ((PresheafWithTransfers.toPresheaf k).obj P) =
        toEtaleNeighborhoodValue X ξ B ((PresheafWithTransfers.toPresheaf k).obj P) :=
  toEtaleNeighborhoodValue_w X ξ f _

example (A B : EtaleNeighborhood X ξ)
    (a : ((PresheafWithTransfers.toPresheaf k).obj P).obj
      (op ((etaleNeighborhoodToSmooth X ξ).obj A)))
    (b : ((PresheafWithTransfers.toPresheaf k).obj P).obj
      (op ((etaleNeighborhoodToSmooth X ξ).obj B)))
    (h : toEtaleNeighborhoodValue X ξ A _ a = toEtaleNeighborhoodValue X ξ B _ b) :
    ∃ (C : EtaleNeighborhood X ξ) (f : C ⟶ A) (g : C ⟶ B),
      PresheafWithTransfers.transfer P
          ((Cor.graphFunctor k).map ((etaleNeighborhoodToSmooth X ξ).map f)) a =
        PresheafWithTransfers.transfer P
          ((Cor.graphFunctor k).map ((etaleNeighborhoodToSmooth X ξ).map g)) b :=
  (toEtaleNeighborhoodValue_eq_iff X ξ _ A B a b).mp h

example : IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map
    (toSheafify (etaleTopology (Spec (.of k)))
      ((PresheafWithTransfers.toPresheaf k).obj P))) := inferInstance

example (A : EtaleNeighborhood X ξ) :
    colimit.ι ((etaleNeighborhoodToSmooth X ξ).op ⋙
        (PresheafWithTransfers.toPresheaf k).obj P) (op A) ≫
      (etaleNeighborhoodColimitIso X ξ ((PresheafWithTransfers.toPresheaf k).obj P)).hom =
        toEtaleNeighborhoodValue X ξ A ((PresheafWithTransfers.toPresheaf k).obj P) :=
  colimit_ι_etaleNeighborhoodColimitIso_hom X ξ _ A

#print axioms AlgebraicGeometry.Scheme.SmoothSite.etaleNeighborhoodValueIsColimit
#print axioms AlgebraicGeometry.Scheme.SmoothSite.exists_etaleNeighborhood_representatives₂
#print axioms AlgebraicGeometry.Scheme.SmoothSite.toEtaleNeighborhoodValue_eq_iff
#print axioms AlgebraicGeometry.Scheme.SmoothSite.toEtaleNeighborhoodValue_eq_zero_iff
#print axioms AlgebraicGeometry.Scheme.SmoothSite.etaleNeighborhoodValue_nsmul_eq_zero
#print axioms AlgebraicGeometry.Scheme.SmoothSite.colimit_ι_etaleNeighborhoodColimitIso_hom
#print axioms AlgebraicGeometry.Scheme.SmoothSite.etaleNeighborhoodSheafificationIso
#print axioms AlgebraicGeometry.Scheme.SmoothSite.toEtaleNeighborhoodValue_sheafificationIso_hom
