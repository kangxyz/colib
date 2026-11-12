/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalComparison
import Colib.Algebra.Homology.CochainComplex.TotalColumnComparison
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.HomotopyInvariance
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness
import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport

/-!
# A¹-invariant cohomology of the singular total complex

The original affine projection acts on the cohomology of each singular
column by an isomorphism. The finite antidiagonals pass this comparison
to the total cohomology.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction
open HomologicalComplex₂.TotalMap

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "c" => ComplexShape.up ℤ

private theorem singularCochain_homology_isA1Invariant (P : PresheafWithTransfers.{v} k) (i : ℤ) :
    ((singularCochainComplex P 0).homology i).IsA1Invariant := by
  let L := singularCochainComplex P 0
  by_cases hi : 0 < i
  · exact isA1Invariant_of_isZero
      (ShortComplex.isZero_homology_of_isZero_X₂ (L.sc i)
        (isZero_singularCochainComplex_X P 0 i hi))
  · let r := (-i).toNat
    have hr : (0 : ℤ) - r = i := by omega
    let e : L.homology i ≅ (singularComplex P).homology r :=
      (singularComplex P).extendHomologyIso (ComplexShape.embeddingUpIntLE 0) hr
    exact (singularComplex_homology_isA1Invariant P r).of_iso e.symm

private theorem finite_mapBicomplex_antidiagonal
    (K : HomologicalComplex₂ (PresheafWithTransfers.{v} k) c c)
    (E : PresheafWithTransfers.{v} k ⥤ AddCommGrpCat.{v}) [E.Additive] (n : ℤ)
    (hK : {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧
      ¬ IsZero (((mapBicomplex E K).X pq.1).X pq.2)}.Finite :=
  hK.subset fun _ h => ⟨h.1, fun hz => h.2 (E.map_isZero hz)⟩

/-- The total singular construction on a bounded-above transfer complex
has invariant cohomology for the actual affine projections. -/
theorem singularTotalFunctor_homology_isA1Invariant
    (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] (i : ℤ) :
    (((singularTotalFunctor k).obj K).homology i).IsA1Invariant := by
  intro X
  let Y := affineLineCylinder.obj X
  let U := toPresheaf.{v} k
  let : PreservesFiniteLimits U := by
    dsimp [U, toPresheaf, restrictAlong]
    infer_instance
  let : PreservesFiniteColimits U := by
    dsimp [U, toPresheaf, restrictAlong]
    infer_instance
  let E (Z : SmoothSite (Spec (.of k))) : PresheafWithTransfers.{v} k ⥤ AddCommGrpCat.{v} :=
    U ⋙ (CategoryTheory.evaluation _ AddCommGrpCat.{v}).obj (op Z)
  let F : PresheafWithTransfers.{v} k ⥤ AddCommGrpCat.{v} := E X
  let G : PresheafWithTransfers.{v} k ⥤ AddCommGrpCat.{v} := E Y
  let τ : F ⟶ G :=
    { app := fun P => A1.projectionPullback (.of k) (U.obj P) X
      naturality := fun P Q f =>
        (((U.map f).naturality
          ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject
            (Spec (.of k)))).app X).op)).symm }
  let B := (singularBicomplexFunctor k).obj K
  let B₀ := mapBicomplex F B
  let B₁ := mapBicomplex G B
  have hB := finite_singularBicomplex_antidiagonal K b
  have h₀ := fun n => finite_mapBicomplex_antidiagonal B F n (hB n)
  have h₁ := fun n => finite_mapBicomplex_antidiagonal B G n (hB n)
  let : B₀.HasTotal c := HomologicalComplex₂.hasTotal_of_finite _ _ h₀
  let : B₁.HasTotal c := HomologicalComplex₂.hasTotal_of_finite _ _ h₁
  let f : B₀ ⟶ B₁ :=
    (NatTrans.mapHomologicalComplex (NatTrans.mapHomologicalComplex τ c) c).app B
  have hf (p : ℤ) : QuasiIso (f.f p) :=
    HomologicalComplex.quasiIso_mapNatTrans_app τ (B.X p)
      (fun q => singularCochain_homology_isA1Invariant (K.X p) q X)
  let : QuasiIso (HomologicalComplex₂.total.map f c) :=
    HomologicalComplex₂.quasiIso_totalMap_of_columnwise f h₀ h₁ hf
  let e₀ := totalIsoOfFinite (c₁₂ := c) F B hB
  let e₁ := totalIsoOfFinite (c₁₂ := c) G B hB
  let g := (NatTrans.mapHomologicalComplex τ c).app (B.total c)
  have h : HomologicalComplex₂.total.map f c ≫ e₁.hom = e₀.hom ≫ g :=
    totalMap_naturality_functor F B τ
  have hg : QuasiIso (e₀.hom ≫ g) := by
    rw [← h]
    exact quasiIso_comp _ _
  let : QuasiIso g := quasiIso_of_comp_left e₀.hom g
  let L := B.total c
  let a := (L.sc i).mapHomologyIso F
  let d := (L.sc i).mapHomologyIso G
  let H := (L.sc i).homology
  let m := ShortComplex.homologyMap ((L.sc i).mapNatTrans τ)
  let : IsIso (ShortComplex.homologyMap ((L.sc i).mapNatTrans τ)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap g i))
  have hτ : τ.app H = a.inv ≫ m ≫ d.hom :=
    CategoryTheory.NatTrans.app_homology τ (L.sc i)
  change IsIso (τ.app H)
  exact hτ.symm ▸ IsIso.comp_isIso' a.isIso_inv
    (IsIso.comp_isIso' (inferInstanceAs (IsIso m)) d.isIso_hom)

end AlgebraicGeometry.PresheafWithTransfers
