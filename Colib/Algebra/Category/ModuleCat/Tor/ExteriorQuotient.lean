/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.LocalMultiplicity

/-!
# Scalar extension of the actual exterior tensor product of two quotient modules

For distinct `k`-algebras `U` and `V`, the native exterior module
`(U / I) ⊗[k] (V / J)` is the quotient of `U ⊗[k] V` by the sum of the two
extended ideals. This follows directly from Mathlib's kernel and surjectivity
theorems for the tensor product of quotient maps.

After extension along `a ⊗ b : U ⊗[k] V → Q ⊗[k] Q`, the resulting module is
the native exterior module `(Q / I Q) ⊗[k] (Q / J Q)`. The final comparison
reuses `Stacks.Intersection.Diagonal.extObjExteriorIdealIso` at `Q`. In
particular, the statement supplies the actual module comparison required by
flat change of rings followed by the full-diagonal theorem; no comparison
isomorphism is an input hypothesis.

The exterior-action argument is the two-ring specialization of the native
`exteriorModule_smul_eq_mul` proof in Stacks' `LocalMultiplicity` module.
The scalar-extension argument reuses its `kerQuotIso` and the native
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`.

## References

* Stacks Project, Tag 0B0T: reduction to the diagonal, degree-zero module
  identification used in its affine proof.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TensorProduct

universe u

namespace ModuleCat.Tor

variable {k U V : Type u} [Field k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]

/-- The ideal of the product of the two affine closed subschemes. -/
def productIdeal (I : Ideal U) (J : Ideal V) : Ideal (U ⊗[k] V) :=
  I.map (Algebra.TensorProduct.includeLeft : U →ₐ[k] U ⊗[k] V).toRingHom ⊔
    J.map (Algebra.TensorProduct.includeRight : V →ₐ[k] U ⊗[k] V).toRingHom

/-- The actual tensor product of the two quotient maps. -/
def productQuotientMap (I : Ideal U) (J : Ideal V) :
    U ⊗[k] V →ₐ[k] (U ⧸ I) ⊗[k] (V ⧸ J) :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k J)

@[simp]
theorem productQuotientMap_tmul (I : Ideal U) (J : Ideal V) (u : U) (v : V) :
    productQuotientMap (k := k) I J (u ⊗ₜ[k] v) =
      Ideal.Quotient.mk I u ⊗ₜ[k] Ideal.Quotient.mk J v := rfl

theorem productQuotientMap_surjective (I : Ideal U) (J : Ideal V) :
    Function.Surjective (productQuotientMap (k := k) I J) :=
  Algebra.TensorProduct.map_surjective _ _
    (Ideal.Quotient.mkₐ_surjective k I) (Ideal.Quotient.mkₐ_surjective k J)

theorem productQuotientMap_ker (I : Ideal U) (J : Ideal V) :
    RingHom.ker (productQuotientMap (k := k) I J).toRingHom =
      productIdeal (k := k) I J := by
  have hI : RingHom.ker (Ideal.Quotient.mkₐ k I) = I := by
    rw [← RingHom.ker_coe_toRingHom]
    exact Ideal.Quotient.mkₐ_ker k I
  have hJ : RingHom.ker (Ideal.Quotient.mkₐ k J) = J := by
    rw [← RingHom.ker_coe_toRingHom]
    exact Ideal.Quotient.mkₐ_ker k J
  change RingHom.ker
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k J)) = _
  rw [Algebra.TensorProduct.map_ker _ _
    (Ideal.Quotient.mkₐ_surjective k I) (Ideal.Quotient.mkₐ_surjective k J), hI, hJ]
  rfl

/-- The exterior module structure on the tensor product of quotient factors.

Keep this instance restricted to quotient factors. Installing the general
exterior instance here would also compete with a tensor product ring's action
on itself, which is used by the native `kerQuotIso`. -/
local instance exteriorQuotientModule (I : Ideal U) (J : Ideal V) :
    Module (U ⊗[k] V) ((U ⧸ I) ⊗[k] (V ⧸ J)) :=
  Stacks.Intersection.Diagonal.exteriorModule (U ⧸ I) (V ⧸ J)

/-- The native exterior action is multiplication through the tensor quotient map. -/
theorem productQuotient_smul_eq_mul (I : Ideal U) (J : Ideal V)
    (r : U ⊗[k] V) (x : (U ⧸ I) ⊗[k] (V ⧸ J)) :
    r • x = productQuotientMap (k := k) I J r * x := by
  induction r using TensorProduct.inductionOn with
  | add r s hr hs => rw [add_smul, hr, hs, map_add, add_mul]
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [smul_add, hx, hy, mul_add]
    | tmul m n =>
      rw [Stacks.Intersection.Diagonal.exteriorModule_smul_tmul,
        productQuotientMap, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      congr 1

/-- The actual exterior action agrees with restriction of the ring action. -/
def exteriorQuotientRestrictIso (I : Ideal U) (J : Ideal V) :
    ModuleCat.of (U ⊗[k] V) ((U ⧸ I) ⊗[k] (V ⧸ J)) ≅
      (ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
        (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J))) :=
  LinearEquiv.toModuleIso
    (X₁ := ModuleCat.of (U ⊗[k] V) ((U ⧸ I) ⊗[k] (V ⧸ J)))
    (X₂ := (ModuleCat.restrictScalars
      (productQuotientMap (k := k) I J).toRingHom).obj
        (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J))))
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => productQuotient_smul_eq_mul I J r x }

theorem exteriorQuotientRestrictIso_hom_apply (I : Ideal U) (J : Ideal V)
    (x : (U ⧸ I) ⊗[k] (V ⧸ J)) :
    (exteriorQuotientRestrictIso (k := k) I J).hom x = x := rfl

theorem exteriorQuotientRestrictIso_inv_apply (I : Ideal U) (J : Ideal V)
    (x : (U ⧸ I) ⊗[k] (V ⧸ J)) :
    (exteriorQuotientRestrictIso (k := k) I J).inv x = x := rfl

/-- The native exterior tensor product of two quotient modules is the product quotient. -/
def productQuotientIso (I : Ideal U) (J : Ideal V) :
    ModuleCat.of (U ⊗[k] V) ((U ⧸ I) ⊗[k] (V ⧸ J)) ≅
      ModuleCat.of (U ⊗[k] V) ((U ⊗[k] V) ⧸ productIdeal (k := k) I J) :=
  exteriorQuotientRestrictIso I J ≪≫
    (Stacks.Intersection.Diagonal.kerQuotIso
      (productQuotientMap (k := k) I J).toRingHom
      (productQuotientMap_surjective I J)).symm ≪≫
    (Ideal.quotientEquivAlgOfEq (U ⊗[k] V)
      (productQuotientMap_ker I J)).toLinearEquiv.toModuleIso

/-- Extend the actual exterior module, retaining the scalar ring of the target. -/
def extendProductQuotientIso {B : Type u} [CommRing B]
    (φ : (U ⊗[k] V) →+* B) (I : Ideal U) (J : Ideal V) :
    (ModuleCat.extendScalars φ).obj
        (ModuleCat.of (U ⊗[k] V) ((U ⧸ I) ⊗[k] (V ⧸ J))) ≅
      ModuleCat.of B (B ⧸ (productIdeal (k := k) I J).map φ) :=
  letI := φ.toAlgebra
  (ModuleCat.extendScalars φ).mapIso (productQuotientIso I J) ≪≫
    (LinearEquiv.toModuleIso
      (X₁ := ModuleCat.of B (B ⧸ (productIdeal (k := k) I J).map φ))
      (X₂ := (ModuleCat.extendScalars φ).obj
        (ModuleCat.of (U ⊗[k] V) ((U ⊗[k] V) ⧸ productIdeal (k := k) I J)))
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
        (productIdeal (k := k) I J)).toLinearEquiv).symm

variable {Q : Type u} [CommRing Q] [Algebra k Q]

/-- The tensor product map extends the product ideal to the product of the extended ideals. -/
theorem map_productIdeal (a : U →ₐ[k] Q) (b : V →ₐ[k] Q)
    (I : Ideal U) (J : Ideal V) :
    (productIdeal (k := k) I J).map (Algebra.TensorProduct.map a b).toRingHom =
      Stacks.Intersection.Diagonal.exteriorIdeal (k := k)
        (I.map a.toRingHom) (J.map b.toRingHom) := by
  have hleft : (Algebra.TensorProduct.map a b).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : U →ₐ[k] U ⊗[k] V).toRingHom =
      (algebraMap Q (Q ⊗[k] Q)).comp a.toRingHom :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_comp_includeLeft a b)
  have hright : (Algebra.TensorProduct.map a b).toRingHom.comp
        (Algebra.TensorProduct.includeRight : V →ₐ[k] U ⊗[k] V).toRingHom =
      (Algebra.TensorProduct.includeRight : Q →ₐ[k] Q ⊗[k] Q).toRingHom.comp
        b.toRingHom :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_comp_includeRight a b)
  simp only [productIdeal, Stacks.Intersection.Diagonal.exteriorIdeal,
    Ideal.map_sup, Ideal.map_map, hleft, hright]

/-- The exterior quotient module after the two ring maps is the actual native
full-diagonal exterior module of the two extended quotients. -/
def extendExteriorQuotientIso (a : U →ₐ[k] Q) (b : V →ₐ[k] Q)
    (I : Ideal U) (J : Ideal V) :
    (ModuleCat.extendScalars (Algebra.TensorProduct.map a b).toRingHom).obj
        (ModuleCat.of (U ⊗[k] V) ((U ⧸ I) ⊗[k] (V ⧸ J))) ≅
      Stacks.Intersection.Diagonal.extObj (k := k)
        (Q ⧸ I.map a.toRingHom) (Q ⧸ J.map b.toRingHom) :=
  extendProductQuotientIso (Algebra.TensorProduct.map a b).toRingHom I J ≪≫
    (Ideal.quotientEquivAlgOfEq (Q ⊗[k] Q)
      (map_productIdeal a b I J)).toLinearEquiv.toModuleIso ≪≫
    (Stacks.Intersection.Diagonal.extObjExteriorIdealIso
      (I.map a.toRingHom) (J.map b.toRingHom)).symm

end ModuleCat.Tor
