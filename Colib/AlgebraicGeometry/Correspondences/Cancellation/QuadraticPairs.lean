/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.QuadraticPencil
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters

/-!
# Quadratic families with a retained torus coordinate

Pair a correspondence with an ordinary torus point on its source by the actual
exterior identity functor and a graph. The two endpoint restrictions of the
monic quadratic family retain the ordinary point and the full polynomial
cycle. Pairing with the factors interchanged uses the graph of the product
symmetry. Pairing each root with itself uses the graph of the diagonal.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme SmoothSite

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

local notation "Gₖ" => multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "γ" => CategoryTheory.Functor.map (graphFunctor k)

variable {U X Y : SmoothSite (Spec (.of k))}

/-- Retain the given ordinary torus point as the right target coordinate. -/
def pairWithTorusPoint (c : X ⟶ Gₖ) :
    (Cor.mk X ⟶ Cor.mk Y) →+ (Cor.mk X ⟶ Cor.mk (product Y Gₖ)) where
  toFun α := γ (productLift (𝟙 X) c) ≫ (parameterProduct Gₖ).map α
  map_zero' := by simp
  map_add' α β := by simp

@[simp]
theorem pairWithTorusPoint_graph (c : X ⟶ Gₖ) (a : X ⟶ Y) :
    pairWithTorusPoint c (γ a) = γ (productLift a c) := by
  change γ (productLift (𝟙 X) c) ≫ (parameterProduct Gₖ).map (γ a) = _
  rw [parameterProduct_graph, ← Functor.map_comp]
  congr 1
  apply product_hom_ext <;> simp

/-- Pull back both the correspondence and the original retained point by an ordinary graph. -/
theorem graph_comp_pairWithTorusPoint (i : U ⟶ X) (c : X ⟶ Gₖ)
    (α : Cor.mk X ⟶ Cor.mk Y) :
    γ i ≫ pairWithTorusPoint c α = pairWithTorusPoint (i ≫ c) (γ i ≫ α) := by
  have h : i ≫ productLift (𝟙 X) c =
      productLift (𝟙 U) (i ≫ c) ≫ SmoothSite.productMap i (𝟙 Gₖ) := by
    apply product_hom_ext <;> simp
  change γ i ≫ γ (productLift (𝟙 X) c) ≫ (parameterProduct Gₖ).map α =
    γ (productLift (𝟙 U) (i ≫ c)) ≫ (parameterProduct Gₖ).map (γ i ≫ α)
  rw [Functor.map_comp, parameterProduct_graph]
  simp only [← Category.assoc, ← Functor.map_comp, h]

/-- The actual symmetry of the binary torus product. -/
def torusProductSwap : product Gₖ Gₖ ⟶ product Gₖ Gₖ :=
  productLift (productSnd Gₖ Gₖ) (productFst Gₖ Gₖ)

/-- Retain the given ordinary torus point as the left target coordinate. -/
def pairWithTorusPointLeft (c : X ⟶ Gₖ) :
    (Cor.mk X ⟶ Cor.mk Gₖ) →+ (Cor.mk X ⟶ Cor.mk (product Gₖ Gₖ)) :=
  (Preadditive.rightComp (Cor.mk X) (γ (torusProductSwap (k := k)))).comp (pairWithTorusPoint c)

@[simp]
theorem pairWithTorusPointLeft_graph (c a : X ⟶ Gₖ) :
    pairWithTorusPointLeft c (γ a) = γ (productLift c a) := by
  change pairWithTorusPoint c (γ a) ≫ γ (torusProductSwap (k := k)) = _
  rw [pairWithTorusPoint_graph, ← Functor.map_comp]
  congr 1
  apply product_hom_ext <;> simp [torusProductSwap]

/-- Graph restriction commutes with retaining a left torus point. -/
theorem graph_comp_pairWithTorusPointLeft (i : U ⟶ X) (c : X ⟶ Gₖ)
    (α : Cor.mk X ⟶ Cor.mk Gₖ) :
    γ i ≫ pairWithTorusPointLeft c α = pairWithTorusPointLeft (i ≫ c) (γ i ≫ α) := by
  change γ i ≫ pairWithTorusPoint c α ≫ γ (torusProductSwap (k := k)) =
    pairWithTorusPoint (i ≫ c) (γ i ≫ α) ≫ γ (torusProductSwap (k := k))
  rw [← Category.assoc, graph_comp_pairWithTorusPoint]

/-- Send both target coordinates along the same actual torus point. -/
def torusDiagonalCorrespondence (X : SmoothSite (Spec (.of k))) :
    (Cor.mk X ⟶ Cor.mk Gₖ) →+ (Cor.mk X ⟶ Cor.mk (product Gₖ Gₖ)) :=
  Preadditive.rightComp (Cor.mk X) (γ (productLift (𝟙 Gₖ) (𝟙 Gₖ)))

@[simp]
theorem torusDiagonalCorrespondence_graph (a : X ⟶ Gₖ) :
    torusDiagonalCorrespondence X (γ a) = γ (productLift a a) := by
  change γ a ≫ γ (productLift (𝟙 Gₖ) (𝟙 Gₖ)) = _
  rw [← Functor.map_comp]
  congr 1
  apply product_hom_ext <;> simp

/-- Graph restriction commutes with the diagonal correspondence. -/
theorem graph_comp_torusDiagonalCorrespondence (i : U ⟶ X)
    (α : Cor.mk X ⟶ Cor.mk Gₖ) :
    γ i ≫ torusDiagonalCorrespondence X α = torusDiagonalCorrespondence U (γ i ≫ α) :=
  (Category.assoc _ _ _).symm

end AlgebraicGeometry.Cor

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {k R : Type u} [Field k] [CommRing R] [IsNoetherianRing R]
  [IsDomain R] [IsIntegrallyClosed R]
  (f : Spec (.of R[X]) ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]

local notation "Gₖ" => multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)
local notation "ev(" i ")" => evalRingHom (i : R)
local notation "f(" i ")" => Spec.map (CommRingCat.ofHom (ev(i))) ≫ f
local notation "e(" i ")" => coefficientGraph f (ev(i))
set_option quotPrecheck false in
local notation "unitPoint(" g "," a ")" =>
  SmoothSite.homMk (X := SmoothSite.mk g) (Y := Gₖ)
    (nativeAffineTorusPoint g a).left (affineUnitPoint_over g a)

/-- The zero endpoint of the actual quadratic pencil as an equation of graph correspondences. -/
theorem graph_zero_comp_unitProductPencilCycle
    [Smooth (f(0))] [IsSeparated (f(0))] [QuasiCompact (f(0))] (a b : Rˣ) :
    γ (e(0)) ≫ (unitProductPencilCycle f a b : Cor.mk (mk f) ⟶ Cor.mk Gₖ) =
      γ (unitPoint(f(0), a * b)) + γ (unitPoint(f(0), 1)) :=
  unitProductPencilCycle_graphRestriction_zero f a b
    (Cor.finite_genericPoints k (Cor.mk (mk (f(0)))))

/-- The one endpoint of the actual quadratic pencil as an equation of graph correspondences. -/
theorem graph_one_comp_unitProductPencilCycle
    [Smooth (f(1))] [IsSeparated (f(1))] [QuasiCompact (f(1))] (a b : Rˣ) :
    γ (e(1)) ≫ (unitProductPencilCycle f a b : Cor.mk (mk f) ⟶ Cor.mk Gₖ) =
      γ (unitPoint(f(1), a)) + γ (unitPoint(f(1), b)) :=
  unitProductPencilCycle_graphRestriction_one f a b
    (Cor.finite_genericPoints k (Cor.mk (mk (f(1)))))

end AlgebraicGeometry.NativeTorusPolynomial
