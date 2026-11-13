/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Support
public import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph

/-!
# Projections of the reparametrized supports

The two supplied support isomorphisms identify their actual middle projections.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

/-- The left support retains the actual free parameter. -/
public theorem reparametrized_left_parameter {k : Type u} [Field k]
    (U X T : SmoothSite (Spec (.of k)))
    (z : pullback (C := Scheme) (SmoothSite.product U T).hom (SmoothSite.product X T).hom)
    {Q : Scheme.{u}} (p : Q ⟶ X.left)
    (eQ : pullback (C := Scheme) (p ≫ X.hom) T.hom ≅ (integralComponentAt z).subscheme)
    (_hQ : eQ.hom ≫ ((integralComponentAt z).subschemeι ≫
      pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom) =
        pullbackParameterExtensionMap p X.hom T.hom) :
    eQ.hom ≫ ((integralComponentAt z).subschemeι ≫
      pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom) ≫
        pullback.snd X.hom T.hom = pullback.snd (p ≫ X.hom) T.hom :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd X.hom T.hom) _hQ).trans
      (pullbackParameterExtensionMap_snd p X.hom T.hom))

/-- The first original middle coordinate of the left support is unchanged. -/
public theorem reparametrized_left_projection {k : Type u} [Field k]
    (U X T : SmoothSite (Spec (.of k)))
    (z : pullback (C := Scheme) (SmoothSite.product U T).hom (SmoothSite.product X T).hom)
    {Q : Scheme.{u}} (p : Q ⟶ X.left)
    (eQ : pullback (C := Scheme) (p ≫ X.hom) T.hom ≅ (integralComponentAt z).subscheme)
    (_hQ : eQ.hom ≫ ((integralComponentAt z).subschemeι ≫
      pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom) =
        pullbackParameterExtensionMap p X.hom T.hom) :
    eQ.hom ≫ ((integralComponentAt z).subschemeι ≫
      pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom) ≫
        pullback.fst X.hom T.hom = pullback.fst (p ≫ X.hom) T.hom ≫ p :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.fst X.hom T.hom) _hQ).trans
      (pullbackParameterExtensionMap_fst p X.hom T.hom))

/-- The right support retains its given graph parameter. -/
public theorem reparametrized_right_parameter {k : Type u} [Field k]
    (X Z T : SmoothSite (Spec (.of k)))
    (w : pullback (C := Scheme) (SmoothSite.product X T).hom (SmoothSite.product Z T).hom)
    {P : Scheme.{u}} (r : P ⟶ X.left) (l : P ⟶ T.left)
    (hl : r ≫ X.hom = l ≫ T.hom) (eP : P ≅ (integralComponentAt w).subscheme)
    (_hP : eP.hom ≫ ((integralComponentAt w).subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) =
        pullback.lift r l hl) :
    eP.hom ≫ ((integralComponentAt w).subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) ≫
        pullback.snd X.hom T.hom = l :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd X.hom T.hom) _hP).trans (pullback.lift_snd _ _ _))

/-- The first original middle coordinate of the right support is unchanged. -/
public theorem reparametrized_right_projection {k : Type u} [Field k]
    (X Z T : SmoothSite (Spec (.of k)))
    (w : pullback (C := Scheme) (SmoothSite.product X T).hom (SmoothSite.product Z T).hom)
    {P : Scheme.{u}} (r : P ⟶ X.left) (l : P ⟶ T.left)
    (hl : r ≫ X.hom = l ≫ T.hom) (eP : P ≅ (integralComponentAt w).subscheme)
    (_hP : eP.hom ≫ ((integralComponentAt w).subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) =
        pullback.lift r l hl) :
    eP.hom ≫ ((integralComponentAt w).subschemeι ≫
      pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) ≫
        pullback.fst X.hom T.hom = r :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.fst X.hom T.hom) _hP).trans (pullback.lift_fst _ _ _))

end Stacks.Chow
