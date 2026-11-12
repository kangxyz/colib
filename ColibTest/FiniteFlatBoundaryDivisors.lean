/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.PrescribedBoundary
import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular

/-!
# Regression tests for actual finite flat boundary divisors

The arbitrary base and full boundary below have no reducedness, integrality, perfectness or
noetherianity assumptions. Regularity and flatness must be conclusions, not instance inputs.
-/

open CategoryTheory AlgebraicGeometry Opposite Stacks.Divisors

universe u

example {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (I : X.IdealSheafData) (hI : IsLocallyPrincipal I)
    [LocallyQuasiFinite (I.subschemeι ≫ f)] : Flat (I.subschemeι ≫ f) :=
  (isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_locallyQuasiFinite f I hI).2

example {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    [IsFinite ((Stacks.Divisors.zeroScheme X L (s.eval (op ⊤))).subschemeι ≫ f)] :
    IsRegularSection X.sheaf.obj X.ringCatSheaf.property s :=
  (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).mp
    (isRelativeEffectiveCartierDivisor_zeroScheme_of_locallyQuasiFinite f L _).1

example {X B U S : Scheme.{u}} [IsAffine S] [U.IsQuasiAffine]
    (q : X ⟶ S) [IsProper q] (i : B ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (e : (Scheme.Modules.pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (he : Scheme.Modules.Hom.app e.hom ⊤ (pullbackGlobalSections i L s) = (1 : Γ(B, ⊤))) :
    Flat ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ q) ∧
      IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme X L s) := by
  have h := Scheme.Modules.finiteLocallyFree_zeroScheme_of_boundary_frame
    q i j hcover L s e he
  exact ⟨h.1.2, h.1.1⟩

#print axioms isEffectiveCartierDivisor_comap_fiberι_of_locallyQuasiFinite
#print axioms isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_locallyQuasiFinite
#print axioms isFiniteLocallyFree_zeroScheme_of_isFinite
#print axioms Scheme.Modules.finiteLocallyFree_zeroScheme_on_smooth_open
#print axioms Scheme.Modules.finiteLocallyFree_zeroScheme_of_boundary_frame
#print axioms Scheme.Modules.isInvertible_pullbackTwistFunctor_obj
#print axioms Scheme.Modules.exists_boundary_framed_finiteLocallyFree_section_pair
