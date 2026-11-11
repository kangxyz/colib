/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundarySerre
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFibers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.PolynomialSectionPencil

universe u

noncomputable section

variable {R : Type u} [CommRing R] {X C : Scheme.{u}}
  (b : X ⟶ Spec (.of R)) (p : C ⟶ X) (L : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
  (a c : Γ(L, ⊤))

example : (familyZero (p ≫ b) L a c).comap (endpoint (p ≫ b) 0) =
    zeroScheme C L a := familyZero_comap_zero (p ≫ b) L a c

example : (familyZero (p ≫ b) L a c).comap (endpoint (p ≫ b) 1) =
    zeroScheme C L c := familyZero_comap_one (p ≫ b) L a c

example : pullback (endpoint b 0) (familySource b p L a c) ≅
    (zeroScheme C L a).subscheme := zeroFiberOverBaseIso b p L a c

example : pullback (endpoint b 1) (familySource b p L a c) ≅
    (zeroScheme C L c).subscheme := oneFiberOverBaseIso b p L a c

example : (zeroFiberOverBaseIso b p L a c).hom ≫
    (zeroScheme C L a).subschemeι ≫ p =
      pullback.fst (endpoint b 0) (familySource b p L a c) :=
  zeroFiberOverBaseIso_hom_base b p L a c

example : (oneFiberOverBaseIso b p L a c).hom ≫
    (zeroScheme C L c).subschemeι =
      pullback.snd (endpoint b 1) (familySource b p L a c) ≫
        (familyZero (p ≫ b) L a c).subschemeι ≫ projection (p ≫ b) :=
  oneFiberOverBaseIso_hom_original b p L a c

#check Scheme.RelativeCurvePencil.exists_eventually_surjective_twisted_quotient
#check Scheme.RelativeCurvePencil.exists_eventually_prescribed_twisted_pair
#check Scheme.RelativeCurvePencil.exists_eventually_surjective_boundary_sections
#check nativeSection_parameterIso
