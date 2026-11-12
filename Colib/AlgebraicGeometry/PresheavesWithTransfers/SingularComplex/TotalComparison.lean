/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Total
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
import Colib.Algebra.Homology.CochainComplex.TotalColumnComparison
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.InvariantUnit
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TermExactness
import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso

/-!
# Quasi-isomorphisms of bounded-above singular total complexes

Every antidiagonal lies in a finite interval of coefficient degrees.
Filtering by simplex degree computes coefficient quasi-isomorphisms,
and filtering by coefficient degree computes the augmentation of a
complex of A¹-invariant presheaves.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open StacksDraft.TotalComplexQuasiIso

set_option backward.isDefEq.respectTransparency false

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "c" => ComplexShape.up ℤ

/-- Only coefficient degrees from the total degree to the original bound
can contribute to a singular antidiagonal. -/
theorem finite_singularBicomplex_antidiagonal (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] (n : ℤ) :
    {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero ((((singularBicomplexFunctor k).obj K).X pq.1).X pq.2)}.Finite := by
  refine ((Set.finite_Icc n b).image (fun p : ℤ => (p, n - p))).subset ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  change ¬ IsZero ((singularCochainComplex (K.X p) 0).X q) at hz
  have hp : p ≤ b := by
    by_contra h
    let ev := singularCochainFunctor 0 ⋙ HomologicalComplex.eval (PresheafWithTransfers.{v} k) c q
    exact hz (ev.map_isZero (K.isZero_of_isStrictlyLE b p (by omega)))
  have hq : q ≤ 0 := by
    by_contra h
    exact hz (isZero_singularCochainComplex_X _ 0 q (by omega))
  have he : n - p = q := by omega
  exact ⟨p, ⟨by omega, hp⟩, congrArg (fun j : ℤ => (p, j)) he⟩

private theorem finite_singularBicomplex_flip_antidiagonal
    (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] (n : ℤ) :
    {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero ((((singularBicomplexFunctor k).obj K).flip.X pq.1).X pq.2)}.Finite := by
  refine ((finite_singularBicomplex_antidiagonal K b n).image Prod.swap).subset ?_
  rintro ⟨q, p⟩ ⟨hpq, hz⟩
  exact ⟨(p, q), ⟨by omega, hz⟩, rfl⟩

private theorem singularBicomplex_quasiIso_flip_column
    {K L : CochainComplex (PresheafWithTransfers.{v} k) ℤ} (f : K ⟶ L) [QuasiIso f] (q : ℤ) :
    let g := (singularBicomplexFunctor k).map f
    QuasiIso (((flipFunctor (PresheafWithTransfers.{v} k) c c).map g).f q) := by
  let B := (singularBicomplexFunctor k).obj K
  let C := (singularBicomplexFunctor k).obj L
  let g : B.flip ⟶ C.flip :=
    (flipFunctor (PresheafWithTransfers.{v} k) c c).map ((singularBicomplexFunctor k).map f)
  change QuasiIso (g.f q)
  by_cases hq : q ≤ 0
  · let r := (-q).toNat
    have h : (ComplexShape.embeddingUpIntLE 0).f r = q := by
      rw [ComplexShape.embeddingUpIntLE_f]
      dsimp [r]
      omega
    let E : PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k := singularTermFunctor r
    let eK : B.flip.X q ≅ (E.mapHomologicalComplex c).obj K :=
      HomologicalComplex.Hom.isoOfComponents
        (fun p => (singularComplex (K.X p)).extendXIso _ h) (by
          intro i j _
          let d := singularComplexMap (K.d i j)
          let e := ComplexShape.embeddingUpIntLE 0
          change (HomologicalComplex.extendXIso _ e h).hom ≫ d.f r =
            (HomologicalComplex.extendMap d e).f q ≫ (HomologicalComplex.extendXIso _ e h).hom
          rw [HomologicalComplex.extendMap_f d e h, Category.assoc, Category.assoc,
            Iso.inv_hom_id, Category.comp_id])
    let eL : C.flip.X q ≅ (E.mapHomologicalComplex c).obj L :=
      HomologicalComplex.Hom.isoOfComponents
        (fun p => (singularComplex (L.X p)).extendXIso _ h) (by
          intro i j _
          let d := singularComplexMap (L.d i j)
          let e := ComplexShape.embeddingUpIntLE 0
          change (HomologicalComplex.extendXIso _ e h).hom ≫ d.f r =
            (HomologicalComplex.extendMap d e).f q ≫ (HomologicalComplex.extendXIso _ e h).hom
          rw [HomologicalComplex.extendMap_f d e h, Category.assoc, Category.assoc,
            Iso.inv_hom_id, Category.comp_id])
    have he : g.f q ≫ eL.hom = eK.hom ≫ (E.mapHomologicalComplex c).map f := by
      apply HomologicalComplex.hom_f_injective
      funext p
      change (HomologicalComplex.extendMap (singularComplexMap (f.f p))
        (ComplexShape.embeddingUpIntLE 0)).f q ≫
          ((singularComplex (L.X p)).extendXIso _ h).hom =
        ((singularComplex (K.X p)).extendXIso _ h).hom ≫ (singularComplexMap (f.f p)).f r
      rw [HomologicalComplex.extendMap_f (singularComplexMap (f.f p)) _ h,
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hg : QuasiIso (g.f q ≫ eL.hom) := by
      rw [he]
      exact quasiIso_comp _ _
    exact quasiIso_of_comp_right _ eL.hom
  · have hzero (M : CochainComplex (PresheafWithTransfers.{v} k) ℤ) :
        IsZero (((singularBicomplexFunctor k).obj M).flip.X q) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply HomologicalComplex.hom_f_injective
      funext p
      exact (isZero_singularCochainComplex_X (M.X p) 0 q (by omega)).eq_of_src _ _
    let : IsIso (g.f q) := isIso_of_isZero _ (hzero K) (hzero L)
    infer_instance

/-- Total singularization preserves the given quasi-isomorphism between
bounded-above coefficient complexes. -/
theorem singularTotalFunctor_quasiIso {K L : CochainComplex (PresheafWithTransfers.{v} k) ℤ}
    (f : K ⟶ L) (b : ℤ) [K.IsStrictlyLE b] [L.IsStrictlyLE b] [QuasiIso f] :
    QuasiIso ((singularTotalFunctor k).map f) := by
  let B := (singularBicomplexFunctor k).obj K
  let C := (singularBicomplexFunctor k).obj L
  let g : B ⟶ C := (singularBicomplexFunctor k).map f
  have hB := finite_singularBicomplex_flip_antidiagonal K b
  have hC := finite_singularBicomplex_flip_antidiagonal L b
  let g' : B.flip ⟶ C.flip := (flipFunctor (PresheafWithTransfers.{v} k) c c).map g
  let : QuasiIso (HomologicalComplex₂.total.map g' c) :=
    quasiIso_totalMap_of_columnwise g' hB hC (singularBicomplex_quasiIso_flip_column f)
  have h := HomologicalComplex₂.totalFlipIso_hom_naturality_map g
  change QuasiIso (HomologicalComplex₂.total.map g c)
  have hcomp : QuasiIso ((B.totalFlipIso c).hom ≫ HomologicalComplex₂.total.map g c) := by
    rw [← h]
    exact quasiIso_comp _ _
  exact quasiIso_of_comp_left (B.totalFlipIso c).hom _

private theorem finite_singleRowZero_antidiagonal
    (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) (n : ℤ) :
    {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero (((singleRowZero K).X pq.1).X pq.2)}.Finite := by
  refine (Set.finite_singleton (n, 0)).subset ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hq : q = 0 := by
    by_contra h
    exact hz (HomologicalComplex.isZero_single_obj_X c 0 (K.X p) q h)
  have hp : p = n := by omega
  simp only [Set.mem_singleton_iff, hp, hq]

/-- On a bounded-above complex of invariant coefficients, the original
total augmentation is a quasi-isomorphism. -/
theorem singularTotalUnitApp_quasiIso_of_terms (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] (hK : ∀ p : ℤ, (K.X p).IsA1Invariant) :
    QuasiIso (singularTotalUnitApp k K) := by
  let B := (singularBicomplexFunctor k).obj K
  let M : HomologicalComplex₂ (PresheafWithTransfers.{v} k) c c := singleRowZero K
  let u₀ : (CochainComplex.singleFunctor (PresheafWithTransfers.{v} k) 0) ⟶
      (singularCochainFunctor 0) := singularCochainUnit
  let g : M ⟶ B := (NatTrans.mapHomologicalComplex u₀ c).app K
  have hg (p : ℤ) : g.f p = singularCochainUnitApp (K.X p) := by
    unfold g u₀ singularCochainUnit
    rfl
  have hM := finite_singleRowZero_antidiagonal K
  let e := totalSingleRowZeroUnit K
  let : IsIso e := isIso_totalSingleRowZeroUnit K
  let : QuasiIso (HomologicalComplex₂.total.map g c) :=
    quasiIso_totalMap_of_columnwise g hM (finite_singularBicomplex_antidiagonal K b)
      (fun p => (hg p).symm ▸ singularCochainUnitApp_quasiIso _ (hK p))
  have h : singularTotalUnitApp k K = e ≫ HomologicalComplex₂.total.map g c := by
    apply HomologicalComplex.hom_f_injective
    funext n
    change singularZeroInclusion (K.X n) ≫ B.ιTotal c n 0 n (add_zero n) =
      (HomologicalComplex.singleObjXSelf c 0 (K.X n)).inv ≫
        M.ιTotal c n 0 n (add_zero n) ≫ (HomologicalComplex₂.total.map g c).f n
    rw [ιTotal_map, hg, singularCochainUnitApp_f_zero]
    let j : (singularCochainComplex (K.X n) 0).X 0 ⟶ (B.total c).X n :=
      B.ιTotal c n 0 n (add_zero n)
    let e₀ := HomologicalComplex.singleObjXSelf c 0 (K.X n)
    let v₀ := singularZeroInclusion (K.X n)
    change v₀ ≫ j = e₀.inv ≫ (e₀.hom ≫ v₀) ≫ j
    exact ((Category.assoc e₀.inv (e₀.hom ≫ v₀) j).symm.trans
      (congrArg (fun m => m ≫ j) (e₀.inv_hom_id_assoc v₀))).symm
  rw [h]
  exact quasiIso_comp _ _

end AlgebraicGeometry.PresheafWithTransfers
