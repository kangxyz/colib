/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Representatives.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import Colib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineMarkedSourceRefinement
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.Opens


/-!
# Restriction of actual unit-image representatives

Restrict the two representatives to the affine marked refinement.
Their matching and unit equations follow through the literal open
inclusion and the map from the new overlap to the original overlap.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
Transfers/Presheaf/Sheafification/Representatives / Restriction.lean.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

namespace AlgebraicGeometry.PresheafWithTransfers
variable {k : Type u} [Field k]

/-- Restrict the original image representative, keeping its actual image in the
sheafification through the literal inclusion. -/
theorem affineOpen_representative_restriction
    (P : PresheafWithTransfers.{u + 1} k)
    {X V : SmoothSite (Spec (.of k))} (v : V ⟶ X)
    (W : V.left.Opens) [IsAffine W.toScheme]
    (t : (nisnevichImage P).sections (Cor.mk V))
    (g : ((nisnevichSheafify k).obj P).obj.sections (Cor.mk X))
    (ht : (nisnevichImageι P).hom.app (op (Cor.mk V)) t =
      ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map v) g) :
    (nisnevichImageι P).hom.app (op (Cor.mk (SmoothSite.affineOpenSite V W)))
      ((nisnevichImage P).transfer
        ((Cor.graphFunctor k).map (SmoothSite.affineOpenInclusion V W)) t) =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (SmoothSite.affineOpenInclusion V W ≫ v)) g := by
  have hn : (nisnevichImageι P).hom.app (op (Cor.mk (SmoothSite.affineOpenSite V W)))
      ((nisnevichImage P).transfer
        ((Cor.graphFunctor k).map (SmoothSite.affineOpenInclusion V W)) t) =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (SmoothSite.affineOpenInclusion V W))
        ((nisnevichImageι P).hom.app (op (Cor.mk V)) t) :=
    (nisnevichImageι P).hom.naturality_apply
      ((Cor.graphFunctor k).map (SmoothSite.affineOpenInclusion V W)).op t
  rw [hn, ht]
  simp only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply]

/-- Matching on the actual new overlap is the restriction of the original matching
pair along the canonical map between the two pullbacks. -/
theorem affineOpen_matching_restriction
    (P : PresheafWithTransfers.{u + 1} k)
    {X A V B : SmoothSite (Spec (.of k))}
    (i : A ⟶ X) [Etale i.left] (v : V ⟶ X)
    (bA : B ⟶ A) (bV : B ⟶ V) (H : IsPullback bA bV i v)
    (W : V.left.Opens) [IsAffine W.toScheme]
    (sA : (nisnevichImage P).sections (Cor.mk A))
    (sV : (nisnevichImage P).sections (Cor.mk V))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bA) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bV) sV) :
    (nisnevichImage P).transfer ((Cor.graphFunctor k).map
      (SmoothSite.etalePullbackFst i (SmoothSite.affineOpenInclusion V W ≫ v))) sA =
    (nisnevichImage P).transfer ((Cor.graphFunctor k).map
      (SmoothSite.etalePullbackSnd i (SmoothSite.affineOpenInclusion V W ≫ v)))
      ((nisnevichImage P).transfer
        ((Cor.graphFunctor k).map (SmoothSite.affineOpenInclusion V W)) sV) := by
  let c := SmoothSite.affineOpenInclusion V W
  let α := SmoothSite.etalePullbackFst i (c ≫ v)
  let β := SmoothSite.etalePullbackSnd i (c ≫ v)
  have hc : α ≫ i = (β ≫ c) ≫ v := by
    rw [Category.assoc]
    exact (SmoothSite.etalePullbackCone i (c ≫ v)).condition
  let δ := H.lift α (β ≫ c) hc
  have hA := congrArg (fun f => (nisnevichImage P).transfer
      ((Cor.graphFunctor k).map f) sA) (H.lift_fst α (β ≫ c) hc)
  have hB := congrArg (fun f => (nisnevichImage P).transfer
      ((Cor.graphFunctor k).map f) sV) (H.lift_snd α (β ≫ c) hc)
  simp only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] at hA hB
  exact hA.symm.trans ((congrArg (fun x => (nisnevichImage P).transfer
    ((Cor.graphFunctor k).map δ) x) hm).trans hB)

/-- Produce an affine source once and restrict the same representative and matching
pair to it. The full marked square is retained on the original coefficient open. -/
theorem exists_affine_marked_representative_refinement
    (P : PresheafWithTransfers.{u + 1} k)
    (R : Type u) [CommRing R] [IsDomain R]
    {X A V B : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine A.left]
    (q : X.left ⟶ Spec (.of R)) (v : V ⟶ X) [Etale v.left]
    (i : A ⟶ X) [Etale i.left]
    (bA : B ⟶ A) (bV : B ⟶ V) (HB : IsPullback bA bV i v)
    {Z : Scheme.{u}} (z : Z ⟶ X.left) [IsFinite (z ≫ q)]
    (s : Z ⟶ V.left) (hs : s ≫ v.left = z)
    (HZ : IsPullback s (𝟙 Z) v.left z)
    (sA : (nisnevichImage P).sections (Cor.mk A))
    (sV : (nisnevichImage P).sections (Cor.mk V))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bA) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bV) sV)
    (g : ((nisnevichSheafify k).obj P).obj.sections (Cor.mk X))
    (hg : (nisnevichImageι P).hom.app (op (Cor.mk V)) sV =
      ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map v) g) :
    ∃ (r : R), r ≠ 0 ∧ ∃ (W : V.left.Opens) (hWa : IsAffineOpen W)
      (hW : W ≤ v.left ⁻¹ᵁ (q ⁻¹ᵁ PrimeSpectrum.basicOpen r)),
      ∃ t : ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ⟶ W.toScheme,
        t ≫ W.ι = ((z ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι ≫ s ∧
        IsPullback t (𝟙 _)
          (v.left.resLE (q ⁻¹ᵁ PrimeSpectrum.basicOpen r) W hW)
          (z ∣_ (q ⁻¹ᵁ PrimeSpectrum.basicOpen r)) ∧
        let : IsAffine W.toScheme := hWa
        let c := SmoothSite.affineOpenInclusion V W
        let sW := (nisnevichImage P).transfer ((Cor.graphFunctor k).map c) sV
        IsAffine (SmoothSite.etalePullback i (c ≫ v)).left ∧
        (nisnevichImageι P).hom.app (op (Cor.mk (SmoothSite.affineOpenSite V W))) sW =
          ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map (c ≫ v)) g ∧
        (nisnevichImage P).transfer ((Cor.graphFunctor k).map
          (SmoothSite.etalePullbackFst i (c ≫ v))) sA =
          (nisnevichImage P).transfer ((Cor.graphFunctor k).map
            (SmoothSite.etalePullbackSnd i (c ≫ v))) sW := by
  obtain ⟨r, hr, W, hWa, hW, t, ht, Ht⟩ :=
    Scheme.exists_affine_marked_source_refinement R q v.left z s hs HZ
  refine ⟨r, hr, W, hWa, hW, t, ht, Ht, ?_⟩
  let : IsAffine W.toScheme := hWa
  exact ⟨SmoothSite.affineOpenOverlap_affine i v W,
    affineOpen_representative_restriction P v W sV g hg,
    affineOpen_matching_restriction P i v bA bV HB W sA sV hm⟩

end AlgebraicGeometry.PresheafWithTransfers
