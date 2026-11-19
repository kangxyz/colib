/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleTensor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusOrdinaryTermFlat
public import StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-! # Smooth étale sheafification of the ordinary signed tensor total

The comparison uses the original strong tensorator, its two naturality laws,
and preservation of the actual integer antidiagonal coproducts. It does not
assert K-flatness of the sheafified factors or compute a sheaf-derived tensor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

attribute [local instance] smoothEtaleIntegral_isMonoidal_W Sheaf.monoidalCategory
  Sheaf.monoidalPreadditive

local notation "P" => SmoothEtaleIntegralPresheaves k
local notation "S" => SmoothEtaleIntegralSheaves k
local notation "a" => smoothEtaleIntegralSheafify k

local instance smoothEtaleIntegral_smallColimits : HasColimitsOfSize.{0, 0} S :=
  inferInstance

local instance smoothEtaleIntegral_smallCoproducts (I : Type) :
    HasColimitsOfShape (Discrete I) S :=
  @HasColimitsOfSize.has_colimits_of_shape S _
    (smoothEtaleIntegral_smallColimits k) (Discrete I) _

local instance smoothEtaleIntegral_tensorAdditive : (curriedTensor S).Additive :=
  inferInstance

local instance smoothEtaleIntegral_tensorObjAdditive (M : S) :
    ((curriedTensor S).obj M).Additive := inferInstance

local instance smoothEtaleIntegral_hasTotal
    (B : HomologicalComplex₂ S (.up ℤ) (.up ℤ)) : B.HasTotal (.up ℤ) :=
  fun _ => (smoothEtaleIntegral_smallCoproducts k _).has_colimit _

local instance smoothEtaleIntegral_hasMapBifunctor (K L : CochainComplex S ℤ) :
    HomologicalComplex.HasMapBifunctor K L (curriedTensor S) (.up ℤ) :=
  smoothEtaleIntegral_hasTotal k _

/-- The original sheafification preserves the coproduct indexing each signed total degree. -/
local instance smoothEtaleIntegral_antidiagonal (n : ℤ) :
    PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {n})) a :=
  inferInstance

/-- Sheafification commutes with the native signed ordinary tensor total. -/
def smoothEtaleIntegralTensorTotalIso (K L : CochainComplex P ℤ) :
    ((a).mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K L (curriedTensor P) (.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        (((a).mapHomologicalComplex (.up ℤ)).obj K)
        (((a).mapHomologicalComplex (.up ℤ)).obj L) (curriedTensor S) (.up ℤ) := by
  let ε := Functor.mapHomologicalComplexTensorComparison a
  have hleft : ∀ {X Y : P} (f : X ⟶ Y) (Z : P),
      (a).map (((curriedTensor P).map f).app Z) ≫ (ε Y Z).hom =
        (ε X Z).hom ≫ ((curriedTensor S).map ((a).map f)).app ((a).obj Z) :=
    fun {X Y} f Z =>
      Functor.mapHomologicalComplexTensorComparison_naturality_left a f Z
  have hright : ∀ (X : P) {Y Z : P} (f : Y ⟶ Z),
      (a).map (((curriedTensor P).obj X).map f) ≫ (ε X Z).hom =
        (ε X Y).hom ≫ ((curriedTensor S).obj ((a).obj X)).map ((a).map f) :=
    fun X {Y Z} f =>
      Functor.mapHomologicalComplexTensorComparison_naturality_right a X f
  letI : HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex a
      ((((curriedTensor P).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L))
      (.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso
      (Functor.mapBifunctorBicomplexIso (curriedTensor P) (curriedTensor S) a a a
        ε (.up ℤ) (.up ℤ) hleft hright K L).symm (.up ℤ)
  exact Functor.mapBifunctorTotalIso (curriedTensor P) (curriedTensor S) a a a
    ε (.up ℤ) (.up ℤ) (.up ℤ) hleft hright K L

/-- The comparison on the actual reduced-torus factors, without replacement complexes. -/
def reducedTorusEtaleTensorTotalIso (q : ℕ) :=
  smoothEtaleIntegralTensorTotalIso k
    (reducedTorusOrdinaryIntegralCochains k q) (reducedTorusOrdinaryIntegralCochains k 1)

end AlgebraicGeometry.PresheafWithTransfers
