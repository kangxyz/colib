/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Roofs
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedOpposite
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Actual triangle and short-exact closure of the restriction image

The displayed global-model roof input supplies a global mapping cone representing the third
vertex of each original open triangle. Rotation then gives extension and kernel closure, with
all three original short-exact endpoints retained. The geometric roof existence theorem is not
asserted here.

Adapted from Quillen's `OpenDerivedImage/Closure.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules]

local notation "R" => Functor.mapHomologicalComplex (restrictFunctor j) (ComplexShape.up ℤ)

instance : (derivedObjects j T).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩

instance : (derivedObjects j T).ContainsZero where
  exists_zero := ⟨(DerivedCategory.Q (C := U.Modules)).obj ((R).obj 0),
    (DerivedCategory.Q (C := U.Modules)).map_isZero ((R).map_isZero (isZero_zero _)),
    0, (perfectSupported T.ι).prop_zero, ⟨Iso.refl _⟩⟩

instance : (derivedObjects j T).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    rintro E ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P⟦n⟧, perfectSupported_shift_of_quasiIso_zero T.ι hP n,
      ⟨(DerivedCategory.Q (C := U.Modules)).mapIso (((R).commShiftIso n).app P) ≪≫
        ((DerivedCategory.Q (C := U.Modules)).commShiftIso n).app ((R).obj P) ≪≫
        (shiftFunctor _ n).mapIso eP⟩⟩⟩

/-- The actual cone of the supplied global numerator represents the third
vertex of the original open triangle, via the displayed locally weak denominator. -/
theorem triangulatedClosed₃ (hroof : HasDerivedRoofs j T) :
    (derivedObjects j T).IsTriangulatedClosed₃ := .mk' (by
  rintro Δ hΔ ⟨P, hP, ⟨eP⟩⟩ ⟨K, hK, ⟨eK⟩⟩
  let α := eP.hom ≫ Δ.mor₁ ≫ eK.inv
  obtain ⟨P', q, g, hP', hq, hg⟩ := hroof P K hP hK α
  let eP' := asIso ((DerivedCategory.Q (C := U.Modules)).map ((R).map q)) ≪≫ eP
  refine ⟨CochainComplex.mappingCone g, perfectSupported_coneClosed T.ι hP' hK g, ⟨?_⟩⟩
  refine (DerivedCategory.Q (C := U.Modules)).mapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso g
      (Scheme.Modules.restrictFunctor j)) ≪≫ ?_
  exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ Δ
    (DerivedCategory.mappingCone_triangle_distinguished ((R).map g)) hΔ eP' eK (by
      change (DerivedCategory.Q (C := U.Modules)).map ((R).map g) ≫ eK.hom = _
      rw [← hg]
      simp only [α, eP', Iso.trans_hom, asIso_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      )))

/-- Original distinguished extension closure, derived from the proved cone construction. -/
theorem triangulatedClosed₂ (hroof : HasDerivedRoofs j T) :
    (derivedObjects j T).IsTriangulatedClosed₂ := by
  let := triangulatedClosed₃ j T hroof
  exact .of_isTriangulatedClosed₃

/-- Original distinguished kernel closure, including the exact rotation shift. -/
theorem triangulatedClosed₁ (hroof : HasDerivedRoofs j T) :
    (derivedObjects j T).IsTriangulatedClosed₁ := by
  let := triangulatedClosed₂ j T hroof
  let : (derivedObjects j T).IsTriangulated := {}
  infer_instance

/-- The genuine original ambient short exact sequence supplies extension closure. -/
theorem complexObjects_of_shortExact (hroof : HasDerivedRoofs j T)
    {S : ShortComplex (CochainComplex U.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : complexObjects j T S.X₁) (h₃ : complexObjects j T S.X₃) :
    complexObjects j T S.X₂ := by
  let := triangulatedClosed₂ j T hroof
  exact (derivedObjects j T).ext_of_isTriangulatedClosed₂ (DerivedCategory.triangleOfSES hS)
    (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₃

/-- The actual cofiber, not a replacement object, belongs to the image. -/
theorem complexObjects_quotient_of_shortExact (hroof : HasDerivedRoofs j T)
    {S : ShortComplex (CochainComplex U.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : complexObjects j T S.X₁) (h₂ : complexObjects j T S.X₂) :
    complexObjects j T S.X₃ := by
  let := triangulatedClosed₃ j T hroof
  exact (derivedObjects j T).ext_of_isTriangulatedClosed₃ (DerivedCategory.triangleOfSES hS)
    (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₂

/-- The actual kernel endpoint belongs to the image when the other endpoints do. -/
theorem complexObjects_kernel_of_shortExact (hroof : HasDerivedRoofs j T)
    {S : ShortComplex (CochainComplex U.Modules ℤ)} (hS : S.ShortExact)
    (h₂ : complexObjects j T S.X₂) (h₃ : complexObjects j T S.X₃) :
    complexObjects j T S.X₁ := by
  let := triangulatedClosed₁ j T hroof
  exact (derivedObjects j T).ext_of_isTriangulatedClosed₁ (DerivedCategory.triangleOfSES hS)
    (DerivedCategory.triangleOfSES_distinguished hS) h₂ h₃

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
