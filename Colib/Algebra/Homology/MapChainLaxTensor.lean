/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.Homology.TotalComplexTransport

/-! # The native total-tensor comparison of an additive lax monoidal functor

The tensorator is only a morphism. Neither its invertibility nor preservation
of coproducts by the functor is assumed. Totalization supplies the differential
compatibility, with its original signs.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  (F : C ⥤ D) [F.Additive] [F.LaxMonoidal]

/-- The original lax tensorator, applied to the two degrees of the native
tensor bicomplex. Its two chain-map equations are the two naturality equations. -/
def mapChainLaxTensorBicomplex (K L : ChainComplex C ℕ) :
    (((curriedTensor D).mapBifunctorHomologicalComplex (.down ℕ) (.down ℕ)).obj
      ((F.mapHomologicalComplex (.down ℕ)).obj K)).obj
        ((F.mapHomologicalComplex (.down ℕ)).obj L) ⟶
    HomologicalComplex₂.mapBicomplex F
      ((((curriedTensor C).mapBifunctorHomologicalComplex (.down ℕ) (.down ℕ)).obj K).obj L) where
  f p :=
    { f q := LaxMonoidal.μ F (K.X p) (L.X q)
      comm' q q' _ := by
        exact (LaxMonoidal.μ_natural_right F (K.X p) (L.d q q')).symm }
  comm' p p' _ := by
    apply HomologicalComplex.hom_ext
    intro q
    exact (LaxMonoidal.μ_natural_left F (K.d p p') (L.X q)).symm

variable [HasCoproducts.{0} C] [HasCoproducts.{0} D]

/-- The native chain tensor comparison, obtained by totalizing the original
coefficient tensorator and then taking the forward totalization comparison. -/
def mapChainLaxTensor (K L : ChainComplex C ℕ) :
    HomologicalComplex.tensorObj ((F.mapHomologicalComplex (.down ℕ)).obj K)
      ((F.mapHomologicalComplex (.down ℕ)).obj L) ⟶
    (F.mapHomologicalComplex (.down ℕ)).obj (HomologicalComplex.tensorObj K L) :=
  HomologicalComplex₂.total.map (mapChainLaxTensorBicomplex F K L) (.down ℕ) ≫
    HomologicalComplex₂.totalMap F
      ((((curriedTensor C).mapBifunctorHomologicalComplex (.down ℕ) (.down ℕ)).obj K).obj L)

omit [HasZeroObject C] [HasZeroObject D] in
/-- On each original antidiagonal summand, the comparison is the coefficient
lax tensorator followed by the image of the original summand inclusion. -/
@[reassoc]
theorem ι_mapChainLaxTensor (K L : ChainComplex C ℕ)
    (p q n : ℕ) (h : p + q = n) :
    ιTensorObj ((F.mapHomologicalComplex (.down ℕ)).obj K)
        ((F.mapHomologicalComplex (.down ℕ)).obj L) p q n h ≫
      (mapChainLaxTensor F K L).f n =
    LaxMonoidal.μ F (K.X p) (L.X q) ≫
      F.map (ιTensorObj K L p q n h) := by
  change _ ≫ ((HomologicalComplex₂.total.map
      (mapChainLaxTensorBicomplex F K L) (.down ℕ)).f n ≫
    HomologicalComplex₂.totalMapf F
      ((((curriedTensor C).mapBifunctorHomologicalComplex (.down ℕ) (.down ℕ)).obj K).obj L) n) = _
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
    HomologicalComplex₂.ι_totalMapf]
  rfl

end CategoryTheory.Functor
