/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor

/-!
# The section cut obtained at the unit parameter

On the original integral support, the unit equation of the power parameter
is the source coordinate to the specified power minus the chosen target unit.
Its finite cut retains the original maps to both base schemes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite AffineLineFiber

variable (k : Type u) [Field k] (X Y : SmoothSite (Spec (.of k)))

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "XG" => (product X T)
local notation "YG" => (product Y T)
set_option quotPrecheck false in
local notation "A" => pullback (C := Scheme) (XG).hom (YG).hom
set_option quotPrecheck false in
local notation "P(" w ")" => (integralComponentAt (X := A) w).subscheme
set_option quotPrecheck false in
local notation "j(" w ")" => (integralComponentAt (X := A) w).subschemeι
set_option quotPrecheck false in
local notation "p(" w ")" =>
  torusSupportBaseProjection k (X := X) (j(w) ≫ pullback.fst (XG).hom (YG).hom)
set_option quotPrecheck false in
local notation "q(" w ")" =>
  torusSupportBaseProjection k (X := Y) (j(w) ≫ pullback.snd (XG).hom (YG).hom)

/-- The literal section of the original support whose zero scheme is the unit fiber. -/
def torusPowerParameterSection (w : A) (n : ℕ) (u₀ : (Γ((YG).left, ⊤))ˣ) : Γ(P(w), ⊤) :=
  ((torusSupportCoordinate k (X := X) (j(w) ≫ pullback.fst (XG).hom (YG).hom)) ^ n).val -
    (Units.map ((j(w) ≫ pullback.snd (XG).hom (YG).hom).appTop.hom.toMonoidHom) u₀).val

/-- The two original support maps agree over the coefficient field. -/
theorem torusPowerParameterBase_eq (w : A) : p(w) ≫ X.hom = q(w) ≫ Y.hom := by
  let f := (XG).hom
  let g := (YG).hom
  let j := j(w)
  change ((j ≫ pullback.fst f g) ≫ (productFst X T).left) ≫ X.hom =
    ((j ≫ pullback.snd f g) ≫ (productFst Y T).left) ≫ Y.hom
  simp only [Category.assoc]
  change j ≫ pullback.fst f g ≫ f = j ≫ pullback.snd f g ≫ g
  exact congrArg (j ≫ ·) (pullback.condition (f := f) (g := g))

set_option quotPrecheck false in
local notation "F(" w ", " n ", " u₀ ")" =>
  sectionToAffineLine (p(w) ≫ X.hom) (torusPowerParameterSection k X Y w n u₀)

/-- The whole finite section cut on the original support as a native correspondence. -/
def torusPowerParameterSectionCut (w : A) (n : ℕ) (u₀ : (Γ((YG).left, ⊤))ˣ)
    [IsFinite (inclusion (F(w, n, u₀)) 0 ≫ p(w))]
    (_hgen : ∀ x : genericPoints (fiber (F(w, n, u₀)) 0),
      (inclusion (F(w, n, u₀)) 0 ≫ p(w)) x.val ∈ genericPoints X.left) :
    Cor.mk X ⟶ Cor.mk Y :=
  sectionCutCorrespondence (X := X) (Y := Y) (P := P(w))
    p(w) q(w) (torusPowerParameterBase_eq k X Y w) (torusPowerParameterSection k X Y w n u₀) _hgen

end AlgebraicGeometry.Cor
