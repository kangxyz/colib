/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection.FinsumIntersections
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TensorSection

/-!
# The literal divisor of a canonical Cartier section

The meromorphic image of a global section is defined by its original generic germ. Its
Weil coefficients are the lengths of the original zero-scheme stalk quotients. Applying
this to the canonical section of `𝒪(D)` gives the effective Cartier divisor itself, before
passing to a divisor class. All meromorphic constructions here require an integral scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

local instance canonicalQuasicoherentOfIsInvertible (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] : L.IsQuasicoherent :=
  isQuasicoherent_of_isInvertible L

/-- The meromorphic section determined by the original generic germ of a global section. -/
def meromorphicSectionOfGlobalSection (L : X.Modules) [L.IsQuasicoherent]
    (s : Γ(L, ⊤)) : MeromorphicSection X.sheaf L :=
  meromorphicSectionOfConstantGenericStalk X L (L.presheaf.germ ⊤ (genericPoint X) trivial s)

/-- Its generic value is the original germ, with no choice of a Picard representative. -/
@[simp]
theorem meromorphicGenericValue_meromorphicSectionOfGlobalSection (L : X.Modules)
    [L.IsQuasicoherent] (s : Γ(L, ⊤)) :
    meromorphicGenericValue X L (meromorphicSectionOfGlobalSection L s) =
      L.presheaf.germ ⊤ (genericPoint X) trivial s :=
  meromorphicGenericValue_meromorphicSectionOfConstantGenericStalk X L _

/-- A nonzero global section of an invertible module has a regular meromorphic image. -/
theorem isRegularMeromorphicSection_meromorphicSectionOfGlobalSection (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    IsRegularMeromorphicSection X.sheaf L (meromorphicSectionOfGlobalSection L s) := by
  apply isRegularMeromorphicSection_meromorphicSectionOfConstantGenericStalk
  obtain ⟨e, he⟩ := exists_isStalkBasis_genericPoint X L
  obtain ⟨a, ha⟩ := he.surjective (L.presheaf.germ ⊤ (genericPoint X) trivial s)
  change a • e = L.presheaf.germ ⊤ (genericPoint X) trivial s at ha
  have ha0 : a ≠ 0 := fun h => Stacks.ChernCap42.germ_ne_zero_of_ne_zero L s hs
    (genericPoint X) (by rw [← ha, h, zero_smul])
  rw [← ha]
  exact (he.smul_of_isUnit (isUnit_iff_ne_zero.mpr ha0)).injective

/-- A regular global section on an integral scheme is nonzero. -/
theorem globalSection_ne_zero_of_isRegularSection (L : X.Modules) (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    s.eval (op (⊤ : X.Opens)) ≠ 0 := by
  have hinj := Scheme.Modules.injective_unitHomEquiv_symm_app_of_isRegularSection L s hs ⊤
  intro h
  let t : Γ(L, ⊤) := s.eval (op ⊤)
  have ht : t = 0 := h
  have heq : (1 : Γ(X, ⊤)) • t = (0 : Γ(X, ⊤)) • t := by
    rw [ht, smul_zero, smul_zero]
  exact one_ne_zero (show (1 : Γ(X, ⊤)) = 0 from hinj heq)

variable [IsLocallyNoetherian X]

/-- The native order of a nonzero global section is its original zero-scheme colength.
Nilpotent structure in the zero scheme is retained. -/
theorem orderOfVanishingMeromorphic_globalSection_eq_length (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (Z : PrimeDivisor X) :
    orderOfVanishingMeromorphic X L (meromorphicSectionOfGlobalSection L s)
        (isRegularMeromorphicSection_meromorphicSectionOfGlobalSection L s hs) Z =
      effectiveCartierMultiplicity (Stacks.Divisors.zeroScheme X L s) Z := by
  obtain ⟨U, eU, -, hxU, -⟩ := Stacks.Chow.exists_affine_frame_subset X L Z.genericPoint ⊤ trivial
  have : Nonempty (U : X.Opens) := ⟨⟨Z.genericPoint, hxU⟩⟩
  let a := Stacks.Divisors.frameSections X L eU (L.presheaf.map (homOfLE le_top).op s)
  have hideal := Stacks.Divisors.zeroScheme_ideal_of_trivialization X L s U
    (Stacks.Divisors.frameSections X L eU) a rfl
  obtain ⟨m, hm, hcoord⟩ := Stacks.ChernCap42.isCoordinateAt_frameSections L s eU
    Z.genericPoint hxU
  have hord := (orderOfVanishingMeromorphicData X L (meromorphicSectionOfGlobalSection L s)
    (isRegularMeromorphicSection_meromorphicSectionOfGlobalSection L s hs) Z).property.2
      m ((Stacks.Divisors.isStalkBasis_iff_span_eq_top L Z.genericPoint m).mp hm)
      (X.germToFunctionField U.1 a)
      ((meromorphicSectionSheafIsoConstant_meromorphicSectionOfConstantGenericStalk X L _).trans
        (congrArg (constantGenericStalkModuleSection X L ⊤) hcoord))
  change AlgebraicGeometry.orderOfVanishingMeromorphic X L _ _ Z = _
  change (orderOfVanishingMeromorphicData X L _ _ Z).val.snd = _
  rw [hord, effectiveCartierMultiplicity,
    IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span (U := U) hxU hideal,
    ← Scheme.algebraMap_germ_eq_germToFunctionField X hxU]
  have ha : X.presheaf.germ U.1 Z.genericPoint hxU a ≠ 0 :=
    Stacks.ChernCap42.germ_frameSections_ne_zero L s hs eU Z.genericPoint hxU
  have hZ : Order.coheight Z.genericPoint = 1 := by
    rw [coheight_eq_codimension_closureSingleton]
    exact Z.codimension_closureSingleton_genericPoint
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Z.genericPoint) :=
    krullDimLE_of_coheight_le hZ.le
  have ha' := mem_nonZeroDivisors_iff_ne_zero.mpr ha
  rw [X.ord_eq_iff hZ
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha)]
  change Ring.ordFrac (X.presheaf.stalk Z.genericPoint) (algebraMap _ _ _) = _
  rw [Ring.ordFrac_eq_ord (X.presheaf.stalk Z.genericPoint) ha]
  exact Ring.ordMonoidWithZeroHom_eq_coe (X.presheaf.stalk Z.genericPoint) ha'
    (ENat.natCast_toNat (Ring.ord_ne_top ha')).symm

end AlgebraicGeometry

namespace Stacks.Divisors

variable {X : Scheme.{u}} [IsIntegral X] (D : X.IdealSheafData)
  [IsEffectiveCartierDivisor D]

local instance canonicalDivisorQuasicoherent : (divisorSheaf D).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherent_of_isInvertible _

/-- The canonical meromorphic section of the actual module `𝒪(D)`. -/
def canonicalMeromorphicSection : AlgebraicGeometry.MeromorphicSection X.sheaf
    (divisorSheaf D) :=
  AlgebraicGeometry.meromorphicSectionOfGlobalSection _ (divisorSheafGlobalSection D)

/-- The canonical meromorphic Cartier section is regular. -/
theorem isRegularMeromorphicSection_canonicalMeromorphicSection :
    AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf (divisorSheaf D)
      (canonicalMeromorphicSection D) :=
  AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfGlobalSection _ _
    (AlgebraicGeometry.globalSection_ne_zero_of_isRegularSection _ _
      (canonicalSection_isRegular D))

/-- Every coefficient of the canonical meromorphic divisor is the original Cartier
stalk quotient length, rather than the length of its reduction. -/
theorem orderOfVanishingMeromorphic_canonicalMeromorphicSection
    [AlgebraicGeometry.IsLocallyNoetherian X] (Z : AlgebraicGeometry.PrimeDivisor X) :
    AlgebraicGeometry.orderOfVanishingMeromorphic X (divisorSheaf D)
        (canonicalMeromorphicSection D)
        (isRegularMeromorphicSection_canonicalMeromorphicSection D) Z =
      AlgebraicGeometry.effectiveCartierMultiplicity D Z := by
  change AlgebraicGeometry.orderOfVanishingMeromorphic X (divisorSheaf D)
    (AlgebraicGeometry.meromorphicSectionOfGlobalSection _ (divisorSheafGlobalSection D)) _ Z = _
  simpa only [zeroScheme_canonicalSection] using
    AlgebraicGeometry.orderOfVanishingMeromorphic_globalSection_eq_length (divisorSheaf D)
      (divisorSheafGlobalSection D)
      (AlgebraicGeometry.globalSection_ne_zero_of_isRegularSection _ _
        (canonicalSection_isRegular D)) Z

/-- On a Noetherian integral scheme the literal native Weil divisor of the canonical
section equals the native effective Cartier divisor. -/
theorem weilDivisorOfMeromorphicSection_canonicalMeromorphicSection
    [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.weilDivisorOfMeromorphicSection X (divisorSheaf D)
        (canonicalMeromorphicSection D)
        (isRegularMeromorphicSection_canonicalMeromorphicSection D) =
      AlgebraicGeometry.effectiveCartierWeilDivisor D inferInstance := by
  apply Subtype.ext
  funext Z
  exact orderOfVanishingMeromorphic_canonicalMeromorphicSection D Z

end Stacks.Divisors
