/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectWaldhausen
public import Colib.AlgebraicGeometry.Modules.PerfectSupport

/-!
# Supported bounded-above-flat perfect complexes

Support is acyclicity after actual open restriction. The inherited exact category retains
admissible quotients in this same class, not arbitrary ambient monomorphisms.
Adapted from Quillen `BoundedFlat/Support.lean:39-62` and `SupportComparison.lean:45`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry.RingedSpace
open scoped ZeroObject
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
/-- The property of bounded-above, stalkwise-flat locally perfect complexes on `X` whose
restriction along `j` is acyclic. -/
def boundedAboveFlatPerfectSupported : ObjectProperty (CochainComplex X.Modules ℤ) := fun K =>
  boundedAboveFlatPerfectComplex X.toRingedSpace K ∧ (((restrictFunctor j).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K).Acyclic

instance boundedAboveFlatPerfectSupported_containsZero : (boundedAboveFlatPerfectSupported
  j).ContainsZero
  where
  exists_zero := ⟨0, isZero_zero _, boundedAboveFlatPerfectComplex_of_isZero (isZero_zero _),
    HomologicalComplex.acyclic_of_isZero _ (((restrictFunctor j).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_isZero (isZero_zero _))⟩

instance boundedAboveFlatPerfectSupported_closedUnderIsomorphisms :
    (boundedAboveFlatPerfectSupported j).IsClosedUnderIsomorphisms where
  of_iso e hK := ⟨boundedAboveFlatPerfectComplex_of_iso e hK.1,
    fun n => (hK.2 n).of_iso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      e)⟩

instance boundedAboveFlatPerfectSupported_extensionClosed :
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed
      (boundedAboveFlatPerfectSupported j) where
  prop_middle {_S} hS h₁ h₃ :=
    ⟨boundedAboveFlatPerfectComplex_of_shortExact hS h₁.1 h₃.1,
      (hS.map_of_exact ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ))).acyclic_X₂
        h₁.2 h₃.2⟩

instance boundedAboveFlatPerfectSupported_closedUnderFiniteProducts :
    (boundedAboveFlatPerfectSupported j).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts
    (boundedAboveFlatPerfectSupported j)

/-- The inherited supported exact chain structure with quasi-isomorphisms. -/
def boundedAboveFlatPerfectSupportedWaldhausen :
    Waldhausen.Structure (boundedAboveFlatPerfectSupported j).FullSubcategory :=
  Waldhausen.complexSubcategory (boundedAboveFlatPerfectSupported j)

/-- Cofibrations have a short exact quotient in the same actual supported class. -/
theorem boundedAboveFlatPerfectSupportedWaldhausen_cof_iff
    {K L : (boundedAboveFlatPerfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectSupportedWaldhausen j).cof f ↔
      ∃ (Q : CochainComplex X.Modules ℤ) (_hQ : boundedAboveFlatPerfectSupported j Q)
        (p : L.obj ⟶ Q) (h : f.hom ≫ p = 0),
        (ShortComplex.mk f.hom p h).ShortExact :=
  ExactSubcategory.inflation_iff (abelianExactStructure _) _ f

/-- Weak equivalences retain the original quasi-isomorphism condition. -/
theorem boundedAboveFlatPerfectSupportedWaldhausen_weq_iff
    {K L : (boundedAboveFlatPerfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectSupportedWaldhausen j).weq f ↔ QuasiIso f.hom := Iff.rfl

end AlgebraicGeometry.Scheme.Modules
