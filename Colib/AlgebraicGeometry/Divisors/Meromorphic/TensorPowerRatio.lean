/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorQuotient
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower

/-!
# The principal correction for a positive tensor root

The native tensor-power comparisons construct the positive power of a regular meromorphic
section. Applying the native section ratio to `c / α(m^n)` gives a literal signed Weil-divisor
identity, with the plus-principal sign determined by this orientation of the quotient.

Here `c` is an actual regular meromorphic section, not a divisor-identity certificate. Identifying
its divisor with a difference of Cartier divisors, and constructing the regular representative
near the full possibly nonreduced boundary, remain separate obligations.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules (schemeTensorPower)

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X] (L : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]

local instance powerRatioInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  hL.toAlgebraicGeometry

local instance powerRatioTensorEquivalence :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).flip.obj L).IsEquivalence :=
  @Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    _ _ _ X.presheaf X.ringCatIsSheaf _ _ L hL

local instance powerRatioPowerInvertible (n : ℤ) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (schemeTensorPower X L hL n) :=
  (Stacks.SheafOfModules.isInvertible_schemeTensorPower X L hL n).toAlgebraicGeometry

local instance powerRatioPowerQuasicoherent (n : ℤ) :
    (schemeTensorPower X L hL n).IsQuasicoherent :=
  isQuasicoherent_of_isInvertible (show X.Modules from schemeTensorPower X L hL n)

local instance powerRatioQuasicoherent (F : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F] : F.IsQuasicoherent :=
  isQuasicoherent_of_isInvertible F

local instance powerRatioTensorInvertible (M N : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj M N) := by
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M)
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N)
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    M N).toAlgebraicGeometry

/-- The native first-power comparison, in the scheme tensor-power spelling. -/
def Scheme.Modules.schemeTensorPowerOneIso : schemeTensorPower X L hL 1 ≅ L :=
  Stacks.SheafOfModules.TensorPower.tensorPowerOneIso X.presheaf X.ringCatIsSheaf L

/-- The native successor comparison, in the scheme tensor-power spelling. -/
def Scheme.Modules.schemeTensorPowerSuccIso (n : ℕ) :
    Scheme.Modules.tensorObj (schemeTensorPower X L hL (n + 1)) L ≅
      schemeTensorPower X L hL (n + 1 + 1) :=
  Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso X.presheaf X.ringCatIsSheaf L (n + 1)

/-- Positive powers of an actual regular meromorphic section, constructed with the native
first-power and successor comparisons. The index `k` denotes the power `k + 1`. -/
def positiveTensorPowerMeromorphicSection (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) : (k : ℕ) →
    {t : MeromorphicSection X.sheaf (schemeTensorPower X L hL (k + 1)) //
      IsRegularMeromorphicSection X.sheaf (schemeTensorPower X L hL (k + 1)) t}
  | 0 => ⟨mapMeromorphicSection L _
      (Scheme.Modules.schemeTensorPowerOneIso X L).inv s,
    isRegularMeromorphicSection_mapMeromorphicSection L _
      (Scheme.Modules.schemeTensorPowerOneIso X L).symm s hs⟩
  | k + 1 => ⟨mapMeromorphicSection _ _ (Scheme.Modules.schemeTensorPowerSuccIso X L k).hom
      (tensorMeromorphicSection X (show X.Modules from schemeTensorPower X L hL (k + 1)) L
        (positiveTensorPowerMeromorphicSection s hs k).val s),
    isRegularMeromorphicSection_mapMeromorphicSection _ _
      (Scheme.Modules.schemeTensorPowerSuccIso X L k) _
      (isRegularMeromorphicSection_tensorMeromorphicSection X
        (show X.Modules from schemeTensorPower X L hL (k + 1)) L
        (positiveTensorPowerMeromorphicSection s hs k).val s
        (positiveTensorPowerMeromorphicSection s hs k).property hs)⟩

/-- Positive powers multiply the actual Weil divisor by the original exponent. -/
@[stacks 02SL "Induction on the native positive tensor power, retaining the actual section"]
theorem weilDivisorOfMeromorphicSection_positiveTensorPowerMeromorphicSection
    [IsLocallyNoetherian X] (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) (k : ℕ) :
    weilDivisorOfMeromorphicSection X _
        (positiveTensorPowerMeromorphicSection X L s hs k).val
        (positiveTensorPowerMeromorphicSection X L s hs k).property =
      (k + 1) • weilDivisorOfMeromorphicSection X L s hs := by
  induction k with
  | zero =>
      change weilDivisorOfMeromorphicSection X _
        (mapMeromorphicSection L _ (Scheme.Modules.schemeTensorPowerOneIso X L).inv s)
        _ = 1 • weilDivisorOfMeromorphicSection X L s hs
      rw [one_smul]
      exact (weilDivisorOfMeromorphicSection_mapMeromorphicSection L _
        (Scheme.Modules.schemeTensorPowerOneIso X L).symm s hs).symm
  | succ k ih =>
      have htransport := (weilDivisorOfMeromorphicSection_mapMeromorphicSection
        (Scheme.Modules.tensorObj (show X.Modules from schemeTensorPower X L hL (k + 1)) L)
        (show X.Modules from schemeTensorPower X L hL (k + 1 + 1))
        (Scheme.Modules.schemeTensorPowerSuccIso X L k) _
        (isRegularMeromorphicSection_tensorMeromorphicSection X
          (show X.Modules from schemeTensorPower X L hL (k + 1)) L
          (positiveTensorPowerMeromorphicSection X L s hs k).val s
          (positiveTensorPowerMeromorphicSection X L s hs k).property hs)).symm
      refine htransport.trans ?_
      rw [weilDivisorOfMeromorphicSection_tensorMeromorphicSection X
        (show X.Modules from schemeTensorPower X L hL (k + 1)) L
        (positiveTensorPowerMeromorphicSection X L s hs k).val s
        (positiveTensorPowerMeromorphicSection X L s hs k).property hs, ih]
      simp only [add_smul, one_smul]

variable (P : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property P]

/-- The actual correcting rational unit has numerator `c` and denominator `α(s^(k+1))`. -/
def tensorPowerCorrectionRatio (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) (k : ℕ)
    (α : schemeTensorPower X L hL (k + 1) ≅ P)
    (c : MeromorphicSection X.sheaf P) (hc : IsRegularMeromorphicSection X.sheaf P c) :
    (Stacks.Chow.rationalFunctions X)ˣ :=
  meromorphicSectionRatio X P c
    (mapMeromorphicSection _ P α.hom (positiveTensorPowerMeromorphicSection X L s hs k).val)
    hc (isRegularMeromorphicSection_mapMeromorphicSection _ P α _
      (positiveTensorPowerMeromorphicSection X L s hs k).property)

/-- The quotient orientation gives `div(c) = (k+1) div(s) + principal(c/α(s^(k+1)))`.
This is equality of native Weil divisors, not equality of divisor classes. -/
@[stacks 02SH "The actual ratio c/alpha(s^n) with the plus-principal sign"]
theorem weilDivisor_eq_smul_add_principal_tensorPowerCorrectionRatio
    [IsLocallyNoetherian X] (s : MeromorphicSection X.sheaf L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) (k : ℕ)
    (α : schemeTensorPower X L hL (k + 1) ≅ P)
    (c : MeromorphicSection X.sheaf P) (hc : IsRegularMeromorphicSection X.sheaf P c) :
    weilDivisorOfMeromorphicSection X P c hc =
      (k + 1) • weilDivisorOfMeromorphicSection X L s hs +
        principalDivisor X (tensorPowerCorrectionRatio X L P s hs k α c hc) := by
  unfold tensorPowerCorrectionRatio
  rw [meromorphicWeilDivisor_eq_add_principalDivisor X P c
    (mapMeromorphicSection _ P α.hom (positiveTensorPowerMeromorphicSection X L s hs k).val)
    hc (isRegularMeromorphicSection_mapMeromorphicSection _ P α _
      (positiveTensorPowerMeromorphicSection X L s hs k).property),
    ← weilDivisorOfMeromorphicSection_mapMeromorphicSection
      (show X.Modules from schemeTensorPower X L hL (k + 1)) P α
      (positiveTensorPowerMeromorphicSection X L s hs k).val
      (positiveTensorPowerMeromorphicSection X L s hs k).property,
    weilDivisorOfMeromorphicSection_positiveTensorPowerMeromorphicSection]

/-- An actual tensor quotient and a specified positive tensor root give the signed principal
correction. Both divisors on the right are computed from the original numerator and denominator;
the correcting function is the native ratio `c / α((a/b)^(k+1))`. -/
@[colib_tag "COL-1047",
  stacks 02SH "Actual tensor-quotient power with the numerator c and plus-principal sign",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/Meromorphic/SectionRatio.lean:242-252"
    "ingredient" "The literal native Weil-divisor equality for the actual correcting ratio"]
theorem weilDivisor_eq_smul_sub_add_principal_tensorQuotientPower
    [IsLocallyNoetherian X] (N : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (a : MeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N))
    (b : MeromorphicSection X.sheaf N)
    (ha : IsRegularMeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N) a)
    (hb : IsRegularMeromorphicSection X.sheaf N b) (k : ℕ)
    (α : schemeTensorPower X L hL (k + 1) ≅ P)
    (c : MeromorphicSection X.sheaf P) (hc : IsRegularMeromorphicSection X.sheaf P c) :
    let m := quotientTensorMeromorphicSection X L N a b hb
    let hm := isRegularMeromorphicSection_quotientTensorMeromorphicSection X L N a b ha hb
    weilDivisorOfMeromorphicSection X P c hc =
      (k + 1) • (weilDivisorOfMeromorphicSection X (Scheme.Modules.tensorObj L N) a ha -
        weilDivisorOfMeromorphicSection X N b hb) +
      principalDivisor X (tensorPowerCorrectionRatio X L P m hm k α c hc) := by
  dsimp only
  rw [← weilDivisorOfMeromorphicSection_quotientTensorMeromorphicSection X L N a b ha hb]
  exact weilDivisor_eq_smul_add_principal_tensorPowerCorrectionRatio X L P _ _ k α c hc

end AlgebraicGeometry
