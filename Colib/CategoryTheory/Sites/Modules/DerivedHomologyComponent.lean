/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Exact-functor homology comparison at an actual complex

Native localization has a liftNatTrans_app formula even
though the upstream file currently states only naturality formulas. This junction
is needed to compare the actual beta1 map, not just abstract H0 isomorphism types.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace StacksDraft.DerivedCategoryHomology

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasDerivedCategory C] [HasDerivedCategory D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Explicit complex-level component of the native localized homology comparison. -/
theorem mapDerivedCategoryHomologyIso_hom_app_Q (K : CochainComplex C ℤ) (i : ℤ) :
    (mapDerivedCategoryHomologyIso F i).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors D i).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        ((K.sc i).mapHomologyIso F).hom ≫
        F.map ((DerivedCategory.homologyFunctorFactors C i).inv.app K) := by
  simp [mapDerivedCategoryHomologyIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Localization.Lifting.iso,
    mapHomologicalComplexHomologyIso]
  rfl

end StacksDraft.DerivedCategoryHomology
