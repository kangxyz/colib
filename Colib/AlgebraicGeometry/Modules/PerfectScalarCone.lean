/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectGlobalScalar
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedCone
public import Colib.Algebra.Homology.MappingCone.ShortExact

/-!
# The actual scalar cone on native perfect complexes

The functor retains Mathlib's signed cone and the literal cone map on the two coefficient
maps. A scalar that restricts to the specified unit gives the same cone with support on the
open complement. Neither regularity of the scalar nor a replacement exact-category model is
used. The short-exactness statements refer to actual ambient complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The literal cone of the native scalar transformation, with native Stacks perfectness. -/
def perfectScalarConeFunctor (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⥤
      ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  ObjectProperty.lift (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
    (mappingConeNatTransFunctor (Functor.whiskerRight (perfectGlobalScalar X r)
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
    (fun K => RingedSpace.isPerfectComplex_mappingCone _ K.property K.property)

/-- The underlying object is the original signed scalar mapping cone. -/
@[simp]
theorem perfectScalarConeFunctor_obj (X : Scheme.{u}) (r : Γ(X, ⊤))
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    ((perfectScalarConeFunctor X r).obj K).obj =
      mappingCone ((complexGlobalScalar X r).app K.obj) := rfl

/-- The cone map retains the original two coefficient maps and the signed cone convention. -/
@[simp]
theorem perfectScalarConeFunctor_map (X : Scheme.{u}) (r : Γ(X, ⊤))
    {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (g : K ⟶ L) :
    ((perfectScalarConeFunctor X r).map g).hom =
      mappingCone.map ((complexGlobalScalar X r).app K.obj)
        ((complexGlobalScalar X r).app L.obj) g.hom g.hom
        ((complexGlobalScalar X r).naturality g.hom).symm := rfl

instance perfectScalarConeFunctor_additive (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    (perfectScalarConeFunctor X r).Additive := by
  unfold perfectScalarConeFunctor
  infer_instance

/-- The original cone maps preserve every ambient short exact sequence of perfect complexes. -/
theorem perfectScalarConeFunctor_shortExact (X : Scheme.{u}) (r : Γ(X, ⊤))
    (S : ShortComplex
      (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))
    (hS : (S.map (ObjectProperty.ι
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))).ShortExact) :
    ((S.map (perfectScalarConeFunctor X r)).map (ObjectProperty.ι
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))).ShortExact :=
  mappingConeNatTransFunctor_shortExact
    (Functor.whiskerRight (perfectGlobalScalar X r)
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))) S hS hS

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(Y, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The same scalar cone, with its actual open-support certificate. -/
@[colib_tag "COL-0298"]
def perfectSupportedScalarConeFunctor :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⥤
      (perfectSupported j).FullSubcategory :=
  ObjectProperty.lift (perfectSupported j)
    (mappingConeNatTransFunctor (Functor.whiskerRight (perfectGlobalScalar X r)
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
    (fun K => perfectOpenWeak_mappingCone_supported j ((perfectGlobalScalar X r).app K)
      (quasiIso_restrict_complexGlobalScalar j r q hq K.obj))

/-- Adding the support proof does not change the original signed cone. -/
@[simp]
theorem perfectSupportedScalarConeFunctor_obj
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    ((perfectSupportedScalarConeFunctor j r q hq).obj K).obj =
      mappingCone ((complexGlobalScalar X r).app K.obj) := rfl

instance perfectSupportedScalarConeFunctor_additive :
    (perfectSupportedScalarConeFunctor j r q hq).Additive := by
  unfold perfectSupportedScalarConeFunctor
  infer_instance

/-- Support does not change preservation of the original ambient short exact sequences. -/
theorem perfectSupportedScalarConeFunctor_shortExact
    (S : ShortComplex
      (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))
    (hS : (S.map (ObjectProperty.ι
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))).ShortExact) :
    ((S.map (perfectSupportedScalarConeFunctor j r q hq)).map
      (ObjectProperty.ι (perfectSupported j))).ShortExact :=
  mappingConeNatTransFunctor_shortExact
    (Functor.whiskerRight (perfectGlobalScalar X r)
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))) S hS hS

end AlgebraicGeometry.Scheme.Modules
