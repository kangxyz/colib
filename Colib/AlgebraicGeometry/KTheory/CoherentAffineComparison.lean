/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Coherent.AffineEquivalence
public import Colib.AlgebraicGeometry.KTheory.Basic
public import Colib.KTheory.Quillen.Map.SmallModelUniverse
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.FractionLocalization

/-!
# The original affine coherent G-comparison on native categories

The literal affine global-sections exact functor induces the lower-universe
comparison with finite-module G-theory. The public scheme G-group is compared
through the canonical universe comparison of the same native coherent category.
No alternate sheaf category or finite-module model is introduced.

Implementation source: `Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/GTheory.lean`
and `UniverseComparison.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Actual global sections exhibit essential smallness in the base universe. -/
instance coherentSpec_essentiallySmall :
    EssentiallySmall.{u} (SheafOfModules.CoherentModules (Spec R).ringCatSheaf) :=
  essentiallySmall_of_fully_faithful (affineGlobalSections R)

/-- The canonical small models retain the actual global-sections equivalence. -/
def globalSectionsSmallEquivalence :
    SmallModel.{u} (SheafOfModules.CoherentModules (Spec R).ringCatSheaf) ≌
      SmallModel.{u} (FGModuleCat.{u} R) :=
  (equivSmallModel.{u} (SheafOfModules.CoherentModules (Spec R).ringCatSheaf)).symm.trans
    ((affineEquivalence R).symm.trans (equivSmallModel.{u} (FGModuleCat.{u} R)))

instance globalSectionsSmall_isEquivalence :
    (affineGlobalSectionsExact R).smallModel.{u}.toFunctor.IsEquivalence :=
  (globalSectionsSmallEquivalence R).isEquivalence_functor

/-- Reflection of the native admissible maps gives the actual Q-equivalence. -/
instance globalSectionsSmall_mapQ_isEquivalence :
    (affineGlobalSectionsExact R).smallModel.{u}.mapQ.IsEquivalence := by
  apply (affineGlobalSectionsExact R).smallModel.mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    change (abelianExactStructure
      (SheafOfModules.CoherentModules (Spec R).ringCatSheaf)).smallModel.inflation i
    rw [abelianExactStructure_smallModel]
    exact (abelianExactStructure_inflation_iff _ i).2
      ((affineGlobalSectionsExact R).smallModel.toFunctor.mono_of_mono_map
        ((abelianExactStructure (FGModuleCat.{u} R)).smallModel.mono_of_inflation hi))
  · intro X Y i hi
    change (abelianExactStructure
      (SheafOfModules.CoherentModules (Spec R).ringCatSheaf)).smallModel.deflation i
    rw [abelianExactStructure_smallModel]
    exact (abelianExactStructure_deflation_iff _ i).2
      ((affineGlobalSectionsExact R).smallModel.toFunctor.epi_of_epi_map
        ((abelianExactStructure (FGModuleCat.{u} R)).smallModel.epi_of_deflation hi))

/-- The original global-sections K-map is an equivalence in the base universe. -/
def specGRingEquiv (n : ℕ) :
    (coherentExactStructure (Spec R)).SmallK.{u} n ≃*
      FGModuleCat.FractionLocalization.G.{u, u} R n :=
  (affineGlobalSectionsExact R).smallModel.KEquivOfMapQIsEquivalence n

/-- The lower-universe equivalence has the original exact global-sections map forward. -/
theorem specGRingEquiv_eq_globalSectionsKMap (n : ℕ) :
    (specGRingEquiv R n).toMonoidHom = (affineGlobalSectionsExact R).smallKMap.{u} n := rfl

/-- Public coherent G-theory compares to finite-module G through the same native category. -/
def publicSpecGRingEquiv (n : ℕ) :
    Scheme.G (Spec R) n ≃* FGModuleCat.FractionLocalization.G.{u, u} R n :=
  ((coherentExactStructure (Spec R)).smallKUniverseEquiv.{u + 1, u} n).trans
    (specGRingEquiv R n)

/-- The public comparison retains both the canonical model map and actual global sections. -/
theorem publicSpecGRingEquiv_toMonoidHom (n : ℕ) :
    (publicSpecGRingEquiv R n).toMonoidHom =
      ((affineGlobalSectionsExact R).smallKMap.{u} n).comp
        ((ExactStructure.smallModelUniverseComparison.{u + 1, u}
          (coherentExactStructure (Spec R))).universalKMap n) := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent

attribute [colib_tag "COL-0611",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/GTheory.lean and UniverseComparison.lean"
    "adaptation" "Actual affine global sections and the same-category universe comparison"]
  AlgebraicGeometry.Scheme.Modules.Coherent.publicSpecGRingEquiv
  AlgebraicGeometry.Scheme.Modules.Coherent.publicSpecGRingEquiv_toMonoidHom
