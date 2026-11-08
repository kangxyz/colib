/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.Modules.PerfectScalarCone
open CategoryTheory AlgebraicGeometry Scheme.Modules
noncomputable section
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
example {K L : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : K ⟶ L) (hf : (perfectOpenWeakWaldhausen j).weq f) :
    perfectSupported j (CochainComplex.mappingCone f.hom) :=
  perfectOpenWeak_mappingCone_supported j f hf

example (r : Γ(X, ⊤))
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    ((perfectScalarConeFunctor X r).obj K).obj =
      CochainComplex.mappingCone ((complexGlobalScalar X r).app K.obj) := rfl

example (r : Γ(X, ⊤)) (q : (Γ(Y, ⊤))ˣ) (hq : j.appTop r = ↑q)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectSupported j ((perfectSupportedScalarConeFunctor j r q hq).obj K).obj :=
  ((perfectSupportedScalarConeFunctor j r q hq).obj K).property

example (r : Γ(X, ⊤)) (q : (Γ(Y, ⊤))ˣ) (hq : j.appTop r = ↑q)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    ((perfectSupportedScalarConeFunctor j r q hq).obj K).obj =
      CochainComplex.mappingCone ((complexGlobalScalar X r).app K.obj) := rfl
