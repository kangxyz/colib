/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusOrdinaryDerivedProduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusOrdinaryTermFlat
public import Colib.Algebra.Homology.Embedding.DownNatTensorIso

/-! # The original AW roof with native signed-total source

Only a chain isomorphism and the original AW roof are localized here.
The source is not identified with a derived tensor product.
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme

universe u v
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]

/-- The native signed tensor of the two actual reduced-torus cochain complexes
is isomorphic to the extension of their original ordinary chain tensor. -/
def reducedTorusSignedTotalChainIso (q : ℕ) :
    HomologicalComplex.tensorObj
        (reducedTorusOrdinaryIntegralCochains k q)
        (reducedTorusOrdinaryIntegralCochains k 1) ≅
      (HomologicalComplex.tensorObj
        (reducedTorusOrdinaryIntegralChains k q)
        (reducedTorusOrdinaryIntegralChains k 1)).extend ComplexShape.embeddingDownNat :=
  HomologicalComplex.DownNatTensor.totalIso
    (curriedTensor ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ))
    (reducedTorusOrdinaryIntegralChains k q) (reducedTorusOrdinaryIntegralChains k 1)

variable [HasDerivedCategory.{v}
  ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)]

/-- Localization of the actual chain comparison, without a derived-tensor assertion. -/
def reducedTorusSignedTotalLocalizedIso (q : ℕ) :
    DerivedCategory.Q.obj (HomologicalComplex.tensorObj
        (reducedTorusOrdinaryIntegralCochains k q)
        (reducedTorusOrdinaryIntegralCochains k 1)) ≅
      (integralPresheafChainToDerived k).obj (HomologicalComplex.tensorObj
        (reducedTorusOrdinaryIntegralChains k q)
        (reducedTorusOrdinaryIntegralChains k 1)) :=
  DerivedCategory.Q.mapIso (reducedTorusSignedTotalChainIso k q)

/-- The original ordinary AW roof, precomposed with the localized chain comparison. -/
def reducedTorusSignedTotalProduct (q : ℕ) :
    DerivedCategory.Q.obj (HomologicalComplex.tensorObj
        (reducedTorusOrdinaryIntegralCochains k q)
        (reducedTorusOrdinaryIntegralCochains k 1)) ⟶
      (integralPresheafChainToDerived k).obj (reducedTorusOrdinaryIntegralChains k (q + 1)) :=
  (reducedTorusSignedTotalLocalizedIso k q).hom ≫ reducedTorusOrdinaryTensorDerivedProduct k q

/-- Undoing the source comparison recovers the literal original AW roof. -/
theorem reducedTorusSignedTotalProduct_recover (q : ℕ) :
    (reducedTorusSignedTotalLocalizedIso k q).inv ≫ reducedTorusSignedTotalProduct k q =
      reducedTorusOrdinaryTensorDerivedProduct k q := by
  simp [reducedTorusSignedTotalProduct]

/-- The transported AW leg followed by the product is still the original pairing leg. -/
theorem reducedTorusSignedTotalProduct_fac (q : ℕ) :
    ((integralPresheafChainToDerived k).map (reducedTorusPresheafAW k q) ≫
        (reducedTorusSignedTotalLocalizedIso k q).inv) ≫
      reducedTorusSignedTotalProduct k q =
        (integralPresheafChainToDerived k).map (reducedTorusPresheafChainPairing k q) := by
  simp [reducedTorusSignedTotalProduct, Category.assoc,
    reducedTorusOrdinaryTensorDerivedProduct_fac]

end AlgebraicGeometry.PresheafWithTransfers
