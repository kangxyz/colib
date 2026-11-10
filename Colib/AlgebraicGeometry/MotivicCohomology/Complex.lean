/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus
public import Colib.AlgebraicGeometry.Simplex.OrdinaryChains
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Sheafification
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# The ordinary Suslin–Voevodsky coefficient complex

Restrict the reduced transfer torus along the actual graph functor and take
ordinary singular chains using the literal relative simplex products. Apply
Nisnevich sheafification in each degree, extend chain degree `r` into cochain
degree `-r`, and take the signed shift `[-q]`. The result places chain degree
`r` in cochain degree `q-r`. Its differential carries the factor `(-1)^q`.
The sheafified chain stage is the target for comparison with transfer chains.

Finite coefficients use the multiplication-by-`n` cone on this same complex.
The integral connecting map and its mod-`n` composite retain the native cone
signs. The termwise tensor and `n²` coefficient-sequence comparisons are
separate obligations.

Adapted from `Motivic/Cohomology/SuslinVoevodsky/{Complex,OrdinaryShiftComparison}.lean`
and `Motivic/Cohomology/Coefficients/Finite/Complex.lean` at `kangxyz/motivic`
revision `a6805c4a87cdfd7717dd7a94039246a167f15380`. The ordinary chain model
here uses Colib's original products, graph restriction and alternating faces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The original alternating-face chains of the graph-restricted transfer presheaf. -/
def motivicPresheafChainsFunctor : PresheafWithTransfers.{u} k ⥤
    ChainComplex ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  PresheafWithTransfers.toPresheaf.{u} k ⋙ AlgebraicSimplex.singularChainsFunctor k

instance : (motivicPresheafChainsFunctor k).Additive := by
  dsimp only [motivicPresheafChainsFunctor]
  infer_instance

/-- Ordinary singular chains of the graph restriction, sheafified degree by degree. -/
def motivicSheafChainsFunctor : PresheafWithTransfers.{u} k ⥤
    ChainComplex
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u}) ℕ :=
  motivicPresheafChainsFunctor k ⋙
    (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u}).mapHomologicalComplex (.down ℕ)

/-- Before sheafification the terms use the original relative simplex products. -/
@[simp]
theorem motivicPresheafChains_obj_X_obj (P : PresheafWithTransfers.{u} k)
    (r : ℕ) (U : SmoothSite (Spec (.of k))) :
    (((motivicPresheafChainsFunctor k).obj P).X r).obj (op U) = PresheafWithTransfers.sections P
      (Cor.mk (SmoothSite.product U (AlgebraicSimplex.smoothSiteObj k r))) := rfl

/-- Ordinary restrictions are the actual graph maps of relative products. -/
@[simp]
theorem motivicPresheafChains_obj_X_map (P : PresheafWithTransfers.{u} k)
    (r : ℕ) {U V : SmoothSite (Spec (.of k))} (f : U ⟶ V) :
    (((motivicPresheafChainsFunctor k).obj P).X r).map f.op = PresheafWithTransfers.transfer P
      ((Cor.graphFunctor k).map
        (SmoothSite.productMap f (𝟙 (AlgebraicSimplex.smoothSiteObj k r)))) :=
  rfl

/-- The original presheaf differential is the signed sum of the product-coface graphs. -/
theorem motivicPresheafChains_obj_d_app (P : PresheafWithTransfers.{u} k)
    (r : ℕ) (U : SmoothSite (Spec (.of k))) :
    (((motivicPresheafChainsFunctor k).obj P).d (r + 1) r).app (op U) =
      ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • PresheafWithTransfers.transfer P
        ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 U)
          ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i))) :=
  AlgebraicSimplex.singularChainsFunctor_obj_d_app k ((PresheafWithTransfers.toPresheaf k).obj P)
    r (op U)

/-- Coefficient morphisms act at the same relative simplex product. -/
@[simp]
theorem motivicPresheafChains_map_f_app {P Q : PresheafWithTransfers.{u} k}
    (η : P ⟶ Q) (r : ℕ) (U : SmoothSite (Spec (.of k))) :
    (((motivicPresheafChainsFunctor k).map η).f r).app (op U) =
      η.hom.app (op (Cor.mk (SmoothSite.product U (AlgebraicSimplex.smoothSiteObj k r)))) := rfl

@[simp]
theorem motivicSheafChainsFunctor_obj_X (P : PresheafWithTransfers.{u} k) (r : ℕ) :
    ((motivicSheafChainsFunctor k).obj P).X r =
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u}).obj
        (((motivicPresheafChainsFunctor k).obj P).X r) := rfl

@[simp]
theorem motivicSheafChainsFunctor_obj_d (P : PresheafWithTransfers.{u} k) (r s : ℕ) :
    ((motivicSheafChainsFunctor k).obj P).d r s =
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u}).map
        (((motivicPresheafChainsFunctor k).obj P).d r s) := rfl

@[simp]
theorem motivicSheafChainsFunctor_map_f {P Q : PresheafWithTransfers.{u} k}
    (η : P ⟶ Q) (r : ℕ) :
    ((motivicSheafChainsFunctor k).map η).f r =
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u}).map
        (((motivicPresheafChainsFunctor k).map η).f r) := rfl

/-- Place chain degree `r` in cochain degree `-r` and then take the signed shift `[-q]`. -/
def motivicComplexFunctor (q : ℕ) :
    PresheafWithTransfers.{u} k ⥤ CochainComplex
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u}) ℤ :=
  motivicSheafChainsFunctor k ⋙ (ComplexShape.embeddingUpIntLE 0).extendFunctor _ ⋙
    CategoryTheory.shiftFunctor _ (-(q : ℤ))

instance (q : ℕ) : (motivicComplexFunctor k q).Additive := by
  dsimp only [motivicComplexFunctor, motivicSheafChainsFunctor]
  infer_instance

private theorem shiftedDegree (q r : ℕ) :
    (ComplexShape.embeddingUpIntLE 0).f r = (q : ℤ) - r + -(q : ℤ) := by
  change (0 : ℤ) - r = (q : ℤ) - r + -(q : ℤ)
  omega

/-- The shifted term in degree `q-r` is the sheafification of the literal chain term. -/
def motivicComplexFunctorXIso (q : ℕ) (P : PresheafWithTransfers.{u} k) (r : ℕ) :
    ((motivicComplexFunctor k q).obj P).X ((q : ℤ) - r) ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u}).obj
        (((motivicPresheafChainsFunctor k).obj P).X r) :=
  ((motivicSheafChainsFunctor k).obj P).extendXIso (ComplexShape.embeddingUpIntLE 0) (by
    change (0 : ℤ) - r = (q : ℤ) - r + -(q : ℤ)
    omega)

/-- The term comparison carries coefficient maps to their actual sheafifications. -/
@[reassoc]
theorem motivicComplexFunctorXIso_naturality (q : ℕ)
    {P Q : PresheafWithTransfers.{u} k} (η : P ⟶ Q) (r : ℕ) :
    ((motivicComplexFunctor k q).map η).f ((q : ℤ) - r) ≫
        (motivicComplexFunctorXIso k q Q r).hom =
      (motivicComplexFunctorXIso k q P r).hom ≫
        (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
          AddCommGrpCat.{u}).map
          (((motivicPresheafChainsFunctor k).map η).f r) :=
  ((ComplexShape.embeddingUpIntLE 0).extendFunctorCompEvalIso _
    (shiftedDegree q r)).hom.naturality ((motivicSheafChainsFunctor k).map η)

/-- The signed cochain differential is the sheafified alternating differential times `(-1)^q`. -/
theorem motivicComplexFunctor_obj_d (q : ℕ) (P : PresheafWithTransfers.{u} k) (r s : ℕ) :
    ((motivicComplexFunctor k q).obj P).d ((q : ℤ) - r) ((q : ℤ) - s) =
      (-1 : ℤ) ^ q • ((motivicComplexFunctorXIso k q P r).hom ≫
        (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
          AddCommGrpCat.{u}).map
          (((motivicPresheafChainsFunctor k).obj P).d r s) ≫
        (motivicComplexFunctorXIso k q P s).inv) := by
  let K := (motivicSheafChainsFunctor k).obj P
  let e := ComplexShape.embeddingUpIntLE 0
  change ((K.extend e)⟦-(q : ℤ)⟧).d ((q : ℤ) - r) ((q : ℤ) - s) =
    (-1 : ℤ) ^ q • ((K.extendXIso e (shiftedDegree q r)).hom ≫
      K.d r s ≫ (K.extendXIso e (shiftedDegree q s)).inv)
  rw [CochainComplex.shiftFunctor_obj_d', K.extend_d_eq e (shiftedDegree q r) (shiftedDegree q s)]
  simp only [Units.smul_def, Int.negOnePow_neg, Int.coe_negOnePow_natCast]

/-- The ordinary Nisnevich Suslin–Voevodsky coefficient complex in weight `q`. -/
def motivicComplex (q : ℕ) : CochainComplex
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u}) ℤ :=
  (motivicComplexFunctor k q).obj (PresheafWithTransfers.reducedTorus k q)

/-- The coefficient complex uses the actual extension and signed shift of the sheaf chains. -/
theorem motivicComplex_eq (q : ℕ) :
    motivicComplex k q =
      (((motivicSheafChainsFunctor k).obj (PresheafWithTransfers.reducedTorus k q)).extend
        (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧ := rfl

/-- An occupied term is the sheafification of the reduced torus on the simplex product. -/
def motivicComplexXIso (q r : ℕ) :
    (motivicComplex k q).X ((q : ℤ) - r) ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u}).obj
        (((motivicPresheafChainsFunctor k).obj (PresheafWithTransfers.reducedTorus k q)).X r) :=
  motivicComplexFunctorXIso k q (PresheafWithTransfers.reducedTorus k q) r

/-- The integral coefficient complex is strictly zero above its weight. -/
theorem isZero_motivicComplex_X (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((motivicComplex k q).X i) := by
  let K := (motivicSheafChainsFunctor k).obj (PresheafWithTransfers.reducedTorus k q)
  change IsZero ((K.extend (ComplexShape.embeddingUpIntLE 0)).X (i + -(q : ℤ)))
  exact K.isZero_extend_X _ _ ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 _).2 (by omega))

/-- Finite coefficients as a functor of the original transfer-presheaf input. -/
def motivicFiniteComplexFunctor (q n : ℕ) :
    PresheafWithTransfers.{u} k ⥤ CochainComplex
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u}) ℤ :=
  motivicComplexFunctor k q ⋙ CochainComplex.finiteCoefficients.functor n

/-- The actual multiplication-by-`n` cone on the integral coefficient complex. -/
def motivicFiniteComplex (q n : ℕ) : CochainComplex
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u}) ℤ :=
  CochainComplex.finiteCoefficients (motivicComplex k q) n

@[simp]
theorem motivicFiniteComplexFunctor_obj_reducedTorus (q n : ℕ) :
    (motivicFiniteComplexFunctor k q n).obj (PresheafWithTransfers.reducedTorus k q) =
      motivicFiniteComplex k q n := rfl

/-- Passing to finite coefficients retains the same upper degree bound. -/
theorem isZero_motivicFiniteComplex_X (q n : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((motivicFiniteComplex k q n).X i) :=
  (CochainComplex.mappingCone.isZero_X_iff _ i).2
    ⟨isZero_motivicComplex_X k q (i + 1) (by omega), isZero_motivicComplex_X k q i hi⟩

namespace motivicFiniteComplexFunctor

/-- Integral reduction is natural in the original transfer-presheaf input. -/
def integral (q n : ℕ) : motivicComplexFunctor k q ⟶ motivicFiniteComplexFunctor k q n where
  app P := CochainComplex.finiteCoefficients.integral ((motivicComplexFunctor k q).obj P) n
  naturality _ _ η :=
    (CochainComplex.finiteCoefficients.integral_naturality n
      ((motivicComplexFunctor k q).map η)).symm

/-- The integral connecting morphism retains its cone sign and is natural in the coefficient. -/
def bockstein (q n : ℕ) : motivicFiniteComplexFunctor k q n ⟶
    motivicComplexFunctor k q ⋙ CategoryTheory.shiftFunctor _ (1 : ℤ) where
  app P := CochainComplex.finiteCoefficients.bockstein ((motivicComplexFunctor k q).obj P) n
  naturality _ _ η :=
    CochainComplex.finiteCoefficients.bockstein_naturality n ((motivicComplexFunctor k q).map η)

/-- The same-level Bockstein composite is natural in the original coefficient. -/
def modBockstein (q n : ℕ) : motivicFiniteComplexFunctor k q n ⟶
    motivicFiniteComplexFunctor k q n ⋙ CategoryTheory.shiftFunctor _ (1 : ℤ) where
  app P := CochainComplex.finiteCoefficients.modBockstein ((motivicComplexFunctor k q).obj P) n
  naturality _ _ η :=
    CochainComplex.finiteCoefficients.modBockstein_naturality n ((motivicComplexFunctor k q).map η)

end motivicFiniteComplexFunctor
end AlgebraicGeometry

attribute [colib_tag "COL-0393"]
  AlgebraicGeometry.motivicComplex
  AlgebraicGeometry.motivicComplex_eq
  AlgebraicGeometry.motivicFiniteComplex

attribute [colib_ref "MVW2006"
  "Lecture 3, Definition 3.1, p. 21" "adaptation"
  "The weight complex after graph restriction and ordinary Nisnevich sheafification"]
  AlgebraicGeometry.motivicComplex
