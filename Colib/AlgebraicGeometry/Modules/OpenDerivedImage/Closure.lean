/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Roofs
public import Colib.AlgebraicGeometry.Modules.PerfectKernel
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

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

local notation "R" => Functor.mapHomologicalComplex (restrictFunctor j) (ComplexShape.up ℤ)

instance : (derivedObjects j).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩

instance : (derivedObjects j).ContainsZero where
  exists_zero := ⟨(DerivedCategory.Q (C := U.Modules)).obj ((R).obj 0),
    (DerivedCategory.Q (C := U.Modules)).map_isZero ((R).map_isZero (isZero_zero _)),
    0, RingedSpace.isPerfectComplex_of_forall_isZero (fun n =>
      (HomologicalComplex.eval _ _ n).map_isZero (isZero_zero _)), ⟨Iso.refl _⟩⟩

instance : (derivedObjects j).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    rintro E ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P⟦n⟧, RingedSpace.isPerfectComplex_shift X.toRingedSpace hP n,
      ⟨(DerivedCategory.Q (C := U.Modules)).mapIso (((R).commShiftIso n).app P) ≪≫
        ((DerivedCategory.Q (C := U.Modules)).commShiftIso n).app ((R).obj P) ≪≫
        (shiftFunctor _ n).mapIso eP⟩⟩⟩

/-- The actual cone of the supplied global numerator represents the third
vertex of the original open triangle, via the displayed locally weak denominator. -/
theorem triangulatedClosed₃ (hroof : HasDerivedRoofs j) :
    (derivedObjects j).IsTriangulatedClosed₃ := .mk' (by
  rintro T hT ⟨P, hP, ⟨eP⟩⟩ ⟨K, hK, ⟨eK⟩⟩
  let α := eP.hom ≫ T.mor₁ ≫ eK.inv
  obtain ⟨P', q, g, hP', hq, hg⟩ := hroof P K hP hK α
  let eP' := asIso ((DerivedCategory.Q (C := U.Modules)).map ((R).map q)) ≪≫ eP
  refine ⟨CochainComplex.mappingCone g, RingedSpace.isPerfectComplex_mappingCone g hP' hK, ⟨?_⟩⟩
  refine (DerivedCategory.Q (C := U.Modules)).mapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso g
      (Scheme.Modules.restrictFunctor j)) ≪≫ ?_
  exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ T
    (DerivedCategory.mappingCone_triangle_distinguished ((R).map g)) hT eP' eK (by
      change (DerivedCategory.Q (C := U.Modules)).map ((R).map g) ≫ eK.hom = _
      rw [← hg]
      simp only [α, eP', Iso.trans_hom, asIso_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      )))

/-- Original distinguished extension closure, derived from the proved cone construction. -/
theorem triangulatedClosed₂ (hroof : HasDerivedRoofs j) :
    (derivedObjects j).IsTriangulatedClosed₂ := by
  let := triangulatedClosed₃ j hroof
  exact .of_isTriangulatedClosed₃

/-- Original distinguished kernel closure, including the exact rotation shift. -/
theorem triangulatedClosed₁ (hroof : HasDerivedRoofs j) :
    (derivedObjects j).IsTriangulatedClosed₁ := by
  let := triangulatedClosed₂ j hroof
  let : (derivedObjects j).IsTriangulated := {}
  infer_instance

/-- The genuine original ambient short exact sequence supplies extension closure. -/
theorem complexObjects_of_shortExact (hroof : HasDerivedRoofs j)
    {S : ShortComplex (CochainComplex U.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : complexObjects j S.X₁) (h₃ : complexObjects j S.X₃) :
    complexObjects j S.X₂ := by
  let := triangulatedClosed₂ j hroof
  exact (derivedObjects j).ext_of_isTriangulatedClosed₂ (DerivedCategory.triangleOfSES hS)
    (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₃

/-- The actual cofiber, not a replacement object, belongs to the image. -/
theorem complexObjects_quotient_of_shortExact (hroof : HasDerivedRoofs j)
    {S : ShortComplex (CochainComplex U.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : complexObjects j S.X₁) (h₂ : complexObjects j S.X₂) :
    complexObjects j S.X₃ := by
  let := triangulatedClosed₃ j hroof
  exact (derivedObjects j).ext_of_isTriangulatedClosed₃ (DerivedCategory.triangleOfSES hS)
    (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₂

/-- The actual kernel endpoint belongs to the image when the other endpoints do. -/
theorem complexObjects_kernel_of_shortExact (hroof : HasDerivedRoofs j)
    {S : ShortComplex (CochainComplex U.Modules ℤ)} (hS : S.ShortExact)
    (h₂ : complexObjects j S.X₂) (h₃ : complexObjects j S.X₃) :
    complexObjects j S.X₁ := by
  let := triangulatedClosed₁ j hroof
  exact (derivedObjects j).ext_of_isTriangulatedClosed₁ (DerivedCategory.triangleOfSES hS)
    (DerivedCategory.triangleOfSES_distinguished hS) h₂ h₃

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_tag "COL-0312",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/Closure.lean"
    "adaptation"
    "Triangle and actual short-exact closure conditional on the displayed global-model roof input"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.triangulatedClosed₃
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.complexObjects_of_shortExact
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.complexObjects_quotient_of_shortExact
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.complexObjects_kernel_of_shortExact
