/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Singular.Functor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Singular complexes of presheaves with transfers

The actual exterior action makes every degree `U ↦ P(U × Δⁿ)` a presheaf
with transfers. The alternating coface differential is transfer-natural, so
these are a chain complex in presheaves with transfers, functorial in `P`.
The cochain placement sends chain degree `r` to degree `q-r`, preserving the
alternating differential and extending by zero above `q`.

Adapted from `Motivic/Transfers/SingularComplex/Presheaf.lean` at revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`. The construction uses native
Mathlib alternating-face chains and bundled additive functors; no generic
`SingularComplex` wrapper or new transfer action is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial ZeroObject

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.Scheme AlgebraicTopology

variable {k : Type u} [Field k]

/-- The degree-`n` singular transfer presheaf uses the actual exterior cycles. -/
def singularTerm (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    PresheafWithTransfers.{v} k :=
  AdditiveFunctor.of (singularFunctor P ⋙ HomologicalComplex.eval _ _ n)

/-- The all-degree alternating singular complex in presheaves with transfers. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/SingularComplex/Presheaf.lean: singularComplex"
  "adaptation" "Native internal chain complex with signed transfers"]
def singularComplex (P : PresheafWithTransfers.{v} k) :
    ChainComplex (PresheafWithTransfers.{v} k) ℕ where
  X := singularTerm P
  d i j := ⟨{
    app U := (singularObj P U.unop).d i j
    naturality _U _V f := (singularTransfer P f.unop).comm i j }⟩
  shape i j hij := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact (singularObj P U.unop).shape i j hij
  d_comp_d' i j l _ _ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact (singularObj P U.unop).d_comp_d i j l

@[simp]
theorem singularComplex_X_obj (P : PresheafWithTransfers.{v} k) (n : ℕ) (U : Cor k) :
    ((singularComplex P).X n).obj.obj (op U) = sections P (Cor.simplexProduct U n) := rfl

@[simp]
theorem singularComplex_X_map (P : PresheafWithTransfers.{v} k) (n : ℕ)
    {U V : Cor k} (α : U ⟶ V) :
    ((singularComplex P).X n).obj.map α.op = transfer P (Cor.simplexExterior n α) := rfl

/-- The differential is the original alternating sum of product-coface transfers. -/
theorem singularComplex_d_app (P : PresheafWithTransfers.{v} k) (n : ℕ) (U : Cor k) :
    ((singularComplex P).d (n + 1) n).hom.app (op U) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 U.toSmoothSite)
          ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i))) :=
  singularObj_d P U n

private theorem transfer_square (P : PresheafWithTransfers.{v} k)
    {A B C D : Cor k} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D}
    (h : a ≫ b = c ≫ d) :
    transfer P b ≫ transfer P a = transfer P d ≫ transfer P c := by
  rw [← transfer_comp, ← transfer_comp, h]

/-- An individual coface gives an actual transfer-natural morphism of singular terms. -/
def singularFace (P : PresheafWithTransfers.{v} k) (n : ℕ) (i : Fin (n + 2)) :
    (singularComplex P).X (n + 1) ⟶ (singularComplex P).X n :=
  ⟨{
    app U := transfer P ((Cor.graphFunctor k).map
      (SmoothSite.productMap (𝟙 U.unop.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i)))
    naturality U V f := by
      change transfer P (Cor.simplexExterior (n + 1) f.unop) ≫ _ =
        _ ≫ transfer P (Cor.simplexExterior n f.unop)
      exact transfer_square P (Cor.simplexExterior_graph_interchange
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i) f.unop).symm }⟩

@[simp]
theorem singularFace_app (P : PresheafWithTransfers.{v} k) (n : ℕ)
    (i : Fin (n + 2)) (U : Cor k) :
    (singularFace P n i).hom.app (op U) =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 U.toSmoothSite)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i))) := rfl

/-- The all-degree differential is the alternating sum of actual natural coface transfers. -/
theorem singularComplex_d (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    (singularComplex P).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • singularFace P n i := by
  apply (AdditiveFunctor.forget _ _).map_injective
  simp only [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_zsmul]
  apply NatTrans.ext
  funext U
  simp only [NatTrans.app_sum, NatTrans.app_zsmul]
  exact singularObj_d P U.unop n

/-- The first differential is the difference of the two actual natural coface transfers. -/
theorem singularComplex_d_one_zero (P : PresheafWithTransfers.{v} k) :
    (singularComplex P).d 1 0 = singularFace P 0 0 - singularFace P 0 1 := by
  rw [singularComplex_d]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- A coefficient morphism gives a chain map natural for every actual transfer. -/
def singularComplexMap {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q) :
    singularComplex P ⟶ singularComplex Q where
  f n := ⟨{
    app U := η.hom.app (op (Cor.simplexProduct U.unop n))
    naturality _U _V f := η.hom.naturality (Cor.simplexExterior n f.unop).op }⟩
  comm' i j _ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact ((alternatingFaceMapComplex AddCommGrpCat.{v}).map
      (Functor.whiskerLeft (Cor.simplexProductCosimplicial U.unop).op η.hom)).comm i j

@[simp]
theorem singularComplexMap_f_app {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    (n : ℕ) (U : Cor k) :
    ((singularComplexMap η).f n).hom.app (op U) =
      η.hom.app (op (Cor.simplexProduct U n)) := rfl

/-- The full singular construction is functorial in the transfer presheaf. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/SingularComplex/Presheaf.lean: singularComplexFunctor"
  "adaptation" "Functoriality of the actual internal transfer complex"]
def singularComplexFunctor : PresheafWithTransfers.{v} k ⥤
    ChainComplex (PresheafWithTransfers.{v} k) ℕ where
  obj := singularComplex
  map := singularComplexMap
  map_id P := by
    ext n : 1
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl
  map_comp η θ := by
    ext n : 1
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl

instance : (singularComplexFunctor.{v} (k := k)).Additive where
  map_add := by
    intro P Q η θ
    ext n : 1
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl

/-- Chain degree `r` is placed in cochain degree `q-r`, with zero extension. -/
def singularCochainFunctor (q : ℕ) : PresheafWithTransfers.{v} k ⥤
    CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
  singularComplexFunctor ⋙ (ComplexShape.embeddingUpIntLE (q : ℤ)).extendFunctor _

/-- The actual cochain complex of transfer presheaves in the stated placement. -/
abbrev singularCochainComplex (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
  (singularCochainFunctor q).obj P

/-- The term at `q-r` is the original singular transfer presheaf in degree `r`. -/
def singularCochainXIso (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (singularCochainComplex P q).X (((q : ℤ) - r)) ≅
      (singularComplex P).X r :=
  (singularComplex P).extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl

/-- The placed complex vanishes above `q`. -/
theorem isZero_singularCochainComplex_X (P : PresheafWithTransfers.{v} k)
    (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((singularCochainComplex P q).X i) := by
  apply (singularComplex P).isZero_extend_X
  exact (ComplexShape.notMem_range_embeddingUpIntLE_iff (q : ℤ) i).2 hi

/-- Placement retains the exact alternating differential, without an extra shift sign. -/
theorem singularCochainComplex_d (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (singularCochainComplex P q).d (((q : ℤ) - (r + 1)))
        (((q : ℤ) - r)) =
      (singularCochainXIso P q (r + 1)).hom ≫ (singularComplex P).d (r + 1) r ≫
        (singularCochainXIso P q r).inv :=
  (singularComplex P).extend_d_eq (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl rfl

end AlgebraicGeometry.PresheafWithTransfers
