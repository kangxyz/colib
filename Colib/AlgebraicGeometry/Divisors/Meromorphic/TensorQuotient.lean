/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TensorSection

/-!
# Dividing a meromorphic tensor section

For invertible modules `L` and `N` on an integral scheme, a regular meromorphic section
`t` of `N` gives an actual division operation from meromorphic sections of `L ⊗ N` to
those of `L`. Its defining equation is `quotient(s,t) ⊗ t = s`, not merely an equality
in the Picard group. On a locally Noetherian integral scheme the resulting Weil divisor
is literally `div(s) - div(t)`.

The integral hypothesis is essential to this use of native generic-stalk and Weil-divisor
APIs. This file does not assert this construction on a nonreduced base or prove the
full-boundary normalization needed in the relative moving-divisor application.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (L N : X.Modules)

/-- Tensoring with a specified stalk basis of the second factor is an isomorphism. -/
def tensorStalkRightBasisEquiv (x : X) (t : N.presheaf.stalk x)
    (ht : Stacks.Divisors.IsStalkBasis N x t) :
    L.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (Scheme.Modules.tensorObj L N).presheaf.stalk x :=
  (TensorProduct.rid (X.presheaf.stalk x) (L.presheaf.stalk x)).symm.trans
    ((TensorProduct.congr (LinearEquiv.refl _ _)
      (LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ t) ht)).trans
        (tensorStalkEquiv L N x).symm)

/-- The stalk isomorphism is the original pure-tensor map. -/
@[simp]
theorem tensorStalkRightBasisEquiv_apply (x : X) (t : N.presheaf.stalk x)
    (ht : Stacks.Divisors.IsStalkBasis N x t) (s : L.presheaf.stalk x) :
    tensorStalkRightBasisEquiv L N x t ht s = tensorStalkTmul L N x s t := by
  simp only [tensorStalkRightBasisEquiv, LinearEquiv.trans_apply,
    TensorProduct.rid_symm_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  congr 2
  exact (LinearEquiv.ofBijective_apply (LinearMap.toSpanSingleton _ _ t)
    (hf := ht) 1).trans (one_smul _ t)

variable (X) [IsIntegral X]

local instance quotientQuasicoherentOfIsInvertible (F : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F] : F.IsQuasicoherent :=
  isQuasicoherent_of_isInvertible F

local instance quotientInvertibleTensorObj
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj L N) := by
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N)
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    L N).toAlgebraicGeometry

/-- A meromorphic section of a quasi-coherent module on an integral scheme is determined
by its actual generic value. -/
theorem meromorphicGenericValue_injective (F : X.Modules) [F.IsQuasicoherent] :
    Function.Injective (meromorphicGenericValue X F) := by
  intro s t h
  have htop : s.val (op (⊤ : X.Opens)) = t.val (op (⊤ : X.Opens)) :=
    injective_iso_hom_val_app (meromorphicSectionSheafIsoConstant X F).val _
      ((constantGenericStalkModuleSection_meromorphicGenericValue X F s).trans
        ((congrArg (constantGenericStalkModuleSection X F ⊤) h).trans
          (constantGenericStalkModuleSection_meromorphicGenericValue X F t).symm))
  apply PresheafOfModules.sections_ext
  intro U
  rw [← PresheafOfModules.sections_property s (homOfLE (le_top (a := U.unop))).op,
    ← PresheafOfModules.sections_property t (homOfLE (le_top (a := U.unop))).op, htop]

/-- The generic value of a regular meromorphic section of an invertible module is a basis
of the generic stalk. -/
theorem isStalkBasis_meromorphicGenericValue
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s) :
    Stacks.Divisors.IsStalkBasis L (genericPoint X) (meromorphicGenericValue X L s) := by
  obtain ⟨e, he⟩ := exists_isStalkBasis_genericPoint X L
  obtain ⟨a, ha⟩ := he.surjective (meromorphicGenericValue X L s)
  change a • e = meromorphicGenericValue X L s at ha
  have ha0 : a ≠ 0 := fun h => meromorphicGenericValue_ne_zero X L s hs
    (by rw [← ha, h, zero_smul])
  rw [← ha]
  exact he.smul_of_isUnit (isUnit_iff_ne_zero.mpr ha0)

variable
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- Divide `s`, a meromorphic section of `L ⊗ N`, by a regular meromorphic section `t`
of `N`, using the inverse of tensoring with its generic basis. -/
def quotientTensorMeromorphicSection
    (s : MeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N))
    (t : MeromorphicSection X.sheaf N) (ht : IsRegularMeromorphicSection X.sheaf N t) :
    MeromorphicSection X.sheaf L :=
  meromorphicSectionOfConstantGenericStalk X L
    ((tensorStalkRightBasisEquiv L N (genericPoint X) (meromorphicGenericValue X N t)
      (isStalkBasis_meromorphicGenericValue X N t ht)).symm
        (meromorphicGenericValue X (Scheme.Modules.tensorObj L N) s))

/-- Multiplication by the original denominator recovers the original tensor section. -/
@[simp]
theorem tensorMeromorphicSection_quotientTensorMeromorphicSection
    (s : MeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N))
    (t : MeromorphicSection X.sheaf N) (ht : IsRegularMeromorphicSection X.sheaf N t) :
    tensorMeromorphicSection X L N (quotientTensorMeromorphicSection X L N s t ht) t = s := by
  apply meromorphicGenericValue_injective X (Scheme.Modules.tensorObj L N)
  rw [meromorphicGenericValue_tensorMeromorphicSection, quotientTensorMeromorphicSection,
    meromorphicGenericValue_meromorphicSectionOfConstantGenericStalk,
    ← tensorStalkRightBasisEquiv_apply L N (genericPoint X) _
      (isStalkBasis_meromorphicGenericValue X N t ht), LinearEquiv.apply_symm_apply]

/-- A regular numerator and denominator give a regular meromorphic tensor quotient. -/
theorem isRegularMeromorphicSection_quotientTensorMeromorphicSection
    (s : MeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N))
    (t : MeromorphicSection X.sheaf N)
    (hs : IsRegularMeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N) s)
    (ht : IsRegularMeromorphicSection X.sheaf N t) :
    IsRegularMeromorphicSection X.sheaf L (quotientTensorMeromorphicSection X L N s t ht) := by
  apply isRegularMeromorphicSection_meromorphicSectionOfConstantGenericStalk
  intro r r' h
  apply (isStalkBasis_meromorphicGenericValue X (Scheme.Modules.tensorObj L N) s hs).injective
  have heq := congrArg
    (tensorStalkRightBasisEquiv L N (genericPoint X) (meromorphicGenericValue X N t)
      (isStalkBasis_meromorphicGenericValue X N t ht)) h
  simpa only [map_smul, LinearEquiv.apply_symm_apply] using heq

/-- The divisor of the actual quotient is numerator minus denominator, with the original
native Weil coefficients. No divisor identity is an input. -/
@[colib_tag "COL-1047",
  stacks 02SL "Tensor quotient consequence of native meromorphic-section additivity",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/Meromorphic/TensorSection.lean:357-369"
    "ingredient" "Native Weil-divisor additivity for actual meromorphic tensor sections"]
theorem weilDivisorOfMeromorphicSection_quotientTensorMeromorphicSection
    [IsLocallyNoetherian X]
    (s : MeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N))
    (t : MeromorphicSection X.sheaf N)
    (hs : IsRegularMeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N) s)
    (ht : IsRegularMeromorphicSection X.sheaf N t) :
    weilDivisorOfMeromorphicSection X L (quotientTensorMeromorphicSection X L N s t ht)
        (isRegularMeromorphicSection_quotientTensorMeromorphicSection X L N s t hs ht) =
      weilDivisorOfMeromorphicSection X (Scheme.Modules.tensorObj L N) s hs -
        weilDivisorOfMeromorphicSection X N t ht := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [tensorMeromorphicSection_quotientTensorMeromorphicSection] using
    (weilDivisorOfMeromorphicSection_tensorMeromorphicSection X L N
      (quotientTensorMeromorphicSection X L N s t ht) t
      (isRegularMeromorphicSection_quotientTensorMeromorphicSection X L N s t hs ht) ht).symm

end AlgebraicGeometry
