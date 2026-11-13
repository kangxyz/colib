/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Functor
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Underlying
import Colib.AlgebraicGeometry.Simplex.HomotopyInvariance
import Colib.AlgebraicGeometry.Simplex.PolynomialInterval

/-!
# Homotopy invariance of transfer singular homology

Graph restriction and evaluation preserve the homology of the actual
alternating singular complex. The ordinary interval equivalence then makes
the original affine-line projection invertible on each transfer homology
presheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite.Contraction
open scoped Simplicial

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

private theorem ordinarySingularHomology_interval_isIso
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v})
    (n : ℕ) (U : SmoothSite (Spec (.of k))) :
    IsIso ((((AlgebraicSimplex.singularChainsFunctor k).obj P).homology n).map
      (SmoothSite.productFst U ((AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋1⦌)).op) := by
  let K := (AlgebraicSimplex.singularChainsFunctor k).obj P
  let f := SmoothSite.productFst U ((AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋1⦌)
  let τ := (evaluation _ AddCommGrpCat.{v}).map f.op
  let : IsIso (ShortComplex.homologyMap ((K.sc n).mapNatTrans τ)) := by
    change IsIso (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app K) n)
    exact AlgebraicSimplex.isIso_ordinaryInterval_homologyMap k P U n
  change IsIso (τ.app (K.sc n).homology)
  rw [NatTrans.app_homology τ (K.sc n)]
  infer_instance

private theorem ordinarySingularHomology_polynomial_isIso
    (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v})
    (n : ℕ) (U : SmoothSite (Spec (.of k))) :
    IsIso ((((AlgebraicSimplex.singularChainsFunctor k).obj P).homology n).map
      (SmoothSite.productFst U (polynomialAffineLine (.of k))).op) := by
  let e := AlgebraicSimplex.polynomialLineSimplexIso k
  let i : SmoothSite.product U (polynomialAffineLine (.of k)) ≅
      SmoothSite.product U ((AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋1⦌) :=
    { hom := SmoothSite.productMap (𝟙 U) e.hom
      inv := SmoothSite.productMap (𝟙 U) e.inv
      hom_inv_id := by
        rw [← SmoothSite.productMap_comp]
        simp only [Category.id_comp, Iso.hom_inv_id, SmoothSite.productMap_id]
      inv_hom_id := by
        rw [← SmoothSite.productMap_comp]
        simp only [Category.id_comp, Iso.inv_hom_id, SmoothSite.productMap_id] }
  let p := SmoothSite.productFst U ((AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋1⦌)
  have hp : i.hom ≫ p = SmoothSite.productFst U (polynomialAffineLine (.of k)) := by
    simp only [i, p, SmoothSite.productMap_fst, Category.comp_id]
  let H := ((AlgebraicSimplex.singularChainsFunctor k).obj P).homology n
  let : IsIso (H.map p.op) := ordinarySingularHomology_interval_isIso P n U
  let : IsIso (H.map i.hom.op) := inferInstanceAs (IsIso (H.mapIso i.op).hom)
  change IsIso (H.map (SmoothSite.productFst U (polynomialAffineLine (.of k))).op)
  rw [← hp, op_comp, Functor.map_comp]
  infer_instance

/-- Each homology presheaf of the actual transfer singular complex is invariant
under the original affine-line projection. -/
@[colib_tag "COL-1030", colib_ref "MVW2006" "Lecture 2, Corollary 2.19, p. 18"
  "adaptation" "Homotopy invariance of transfer singular homology by exact graph restriction"]
theorem singularComplex_homology_isA1Invariant
    (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    ((HomologicalComplex.homologyFunctor (PresheafWithTransfers.{v} k)
      (ComplexShape.down ℕ) n).obj (singularComplex P)).IsA1Invariant := by
  let F := toPresheaf.{v} k
  let : PreservesFiniteLimits F := by
    dsimp [F, toPresheaf, restrictAlong]
    infer_instance
  let : PreservesFiniteColimits F := by
    dsimp [F, toPresheaf, restrictAlong]
    infer_instance
  let K := singularComplex P
  let L := (AlgebraicSimplex.singularChainsFunctor k).obj (F.obj P)
  let e : F.obj (K.homology n) ≅ L.homology n :=
    ((K.sc n).mapHomologyIso F).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) n).mapIso
        (singularComplexUnderlyingNatIso.app P)
  apply (isA1Invariant_iff_polynomial_projection (K.homology n)).2
  intro U
  let f := (SmoothSite.productFst U (polynomialAffineLine (.of k))).op
  change IsIso ((F.obj (K.homology n)).map f)
  let : IsIso ((L.homology n).map f) := ordinarySingularHomology_polynomial_isIso (F.obj P) n U
  have : IsIso ((F.obj (K.homology n)).map f ≫ e.hom.app _) := by
    rw [e.hom.naturality f]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)

end AlgebraicGeometry.PresheafWithTransfers
