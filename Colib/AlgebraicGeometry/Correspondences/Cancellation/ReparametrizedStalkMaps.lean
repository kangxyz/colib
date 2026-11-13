/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedIncidence
public import Colib.AlgebraicGeometry.Correspondences.Composition.AmbientTorPointTransport
public import Colib.AlgebraicGeometry.Scheme.StalkMapAtImage

/-!
# Actual stalk maps for the common parameter quotient

The actual ambient and coefficient quotient maps commute at the common
incidence point. The full native triple map is the composite of the
two ambient quotient maps with the indicated point transport.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

private theorem scheme_point_congr {A B : Scheme.{u}} {f g : A ⟶ B}
    (h : f = g) (x : A) : f x = g x :=
  congrArg (fun m : A ⟶ B => m x) h

private theorem stalkMapAtImage_comp_eq {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C) (g' : C ⟶ D)
    (h : f ≫ g = f' ≫ g') (x : A) :
    g.stalkMap (f x) ≫ f.stalkMap x =
      g'.stalkMapAtImage (f' x) (g (f x)) (scheme_point_congr h x) ≫ f'.stalkMap x := by
  calc
    _ = (f ≫ g).stalkMapAtImage x (g (f x)) rfl :=
      (Scheme.Hom.stalkMap_comp f g x).symm.trans
        (Scheme.Hom.stalkMapAtImage_rfl (f ≫ g) x).symm
    _ = (f' ≫ g').stalkMapAtImage x (g (f x)) (scheme_point_congr h x) :=
      Scheme.Hom.stalkMapAtImage_congr _ _ h _ _ _ _
    _ = _ := by
      simpa only [Scheme.Hom.stalkMapAtImage_rfl] using
        (Scheme.Hom.stalkMapAtImage_comp f' g' x (f' x) (g (f x)) rfl
          (scheme_point_congr h x)).symm

private theorem stalkMapAtImage_comp_factor {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (m : A ⟶ C) (h : f ≫ g = m) (x : A) :
    g.stalkMapAtImage (f x) (m x) (scheme_point_congr h.symm x) ≫ f.stalkMap x =
      m.stalkMap x := by
  calc
    _ = (f ≫ g).stalkMapAtImage x (m x) (scheme_point_congr h.symm x) := by
      simpa only [Scheme.Hom.stalkMapAtImage_rfl] using
        (Scheme.Hom.stalkMapAtImage_comp f g x (f x) (m x) rfl (scheme_point_congr h.symm x))
    _ = m.stalkMapAtImage x (m x) rfl :=
      Scheme.Hom.stalkMapAtImage_congr _ _ h _ _ _ _
    _ = _ := Scheme.Hom.stalkMapAtImage_rfl m x

private theorem stalkMap_comp_cast_factor {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (m : A ⟶ C) (h : f ≫ g = m)
    (x : A) (y : B) (z : C) (hy : y = f x) (hz : z = g y) (ht : m x = z) :
    m.stalkMap x = (C.presheaf.stalkCongr (.of_eq ht)).hom ≫
      g.stalkMapAtImage y z hz ≫ f.stalkMapAtImage x y hy := by
  rw [Scheme.Hom.stalkMapAtImage_comp]
  rw [Scheme.Hom.stalkMapAtImage_congr (f ≫ g) m h x z _ ht.symm]
  exact (Scheme.Hom.stalkMapAtImage_rfl m x).symm.trans
    (Scheme.Hom.stalkMapAtImage_precomp_cast m x z (m x) ht.symm ht).symm

variable {k : Type u} [Field k] (U X Z T : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme) (SmoothSite.product U T).hom (SmoothSite.product X T).hom)
  (w : pullback (C := Scheme) (SmoothSite.product X T).hom (SmoothSite.product Z T).hom)
  {Q P : Scheme.{u}} (p : Q ⟶ X.left) (r : P ⟶ X.left) (l : P ⟶ T.left)
  (hl : r ≫ X.hom = l ≫ T.hom)
  (eQ : pullback (C := Scheme) (p ≫ X.hom) T.hom ≅ (integralComponentAt z).subscheme)
  (eP : P ≅ (integralComponentAt w).subscheme)
  (hQ : eQ.hom ≫ ((integralComponentAt z).subschemeι ≫
    pullback.snd (SmoothSite.product U T).hom (SmoothSite.product X T).hom) =
      pullbackParameterExtensionMap p X.hom T.hom)
  (hP : eP.hom ≫ ((integralComponentAt w).subschemeι ≫
    pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom) =
      pullback.lift r l hl)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product U T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Z T).hom

local notation3 (prettyPrint := false) "D" => pullback (p ≫ X.hom) (r ≫ X.hom)
local notation3 (prettyPrint := false) "C" => correspondenceSupportProduct f g h z w
local notation3 (prettyPrint := false) "A" => correspondenceIntersectionAmbient f g h
local notation3 (prettyPrint := false) "B" => exteriorAmbientParameterQuotient U X Z T
local notation3 (prettyPrint := false) "L" => correspondenceTripleProduct f g h
local notation3 (prettyPrint := false) "i" => correspondenceSupportProductInclusion f g h z w
local notation3 (prettyPrint := false) "j" => exteriorAmbientParameterInclusion U X Z T
local notation3 (prettyPrint := false) "j'" => exteriorAmbientRemainingInclusion U X Z T
local notation3 (prettyPrint := false) "j₀" => correspondenceTripleInclusion f g h
local notation3 (prettyPrint := false) "c" =>
  reparametrizedCoefficientInclusion U X Z T z w p r l hl eQ eP hQ hP
local notation3 (prettyPrint := false) "d" =>
  reparametrizedCoefficientQuotientMap U X Z T z w p r l hl eQ eP hQ hP
local notation3 (prettyPrint := false) "v" => reparametrizedIncidenceToProduct X p r
local notation3 (prettyPrint := false) "m" => exteriorAmbientRemainingPair U X Z T
local notation3 (prettyPrint := false) "m₀" => reparametrizedRemainingMiddlePair X p r

variable (x : pullback («C» := Scheme) p r)

/-- The original point viewed on the actual native incidence. -/
abbrev reparametrizedStalkIncidencePoint : correspondenceIncidence f g h z w :=
  let e : pullback («C» := Scheme) p r ≅ correspondenceIncidence f g h z w :=
    @reparametrizedIncidenceIso k _ U X Z T z w Q P p r l hl eQ eP hQ hP
  e.hom x

local notation3 (prettyPrint := false) "y" => v x
local notation3 (prettyPrint := false) "xₙ" =>
  reparametrizedStalkIncidencePoint U X Z T z w p r l hl eQ eP hQ hP x
local notation3 (prettyPrint := false) "xₗ" => correspondenceIncidenceInclusion f g h z w xₙ
local notation3 (prettyPrint := false) "xₐ" => i (c y)
local notation3 (prettyPrint := false) "xᵦ" => d y

/-- The native incidence and the coefficient graph give the same support point. -/
theorem reparametrizedStalk_supportPoint :
    c y = correspondenceIncidenceToSupportProduct f g h z w xₙ :=
  scheme_point_congr
    (reparametrizedIncidenceIso_coefficient U X Z T z w p r l hl eQ eP hQ hP).symm x

/-- The parameter quotient has the actual displayed ambient image. -/
theorem reparametrizedStalk_parameterPoint : xₐ = j xᵦ :=
  scheme_point_congr
    (reparametrizedCoefficientQuotientMap_ambient U X Z T z w p r l hl eQ eP hQ hP).symm y

/-- The remaining quotient has the actual displayed parameter image. -/
theorem reparametrizedStalk_remainingPoint : xᵦ = j' xₗ :=
  scheme_point_congr
    (reparametrizedIncidenceIso_ambientQuotient U X Z T z w p r l hl eQ eP hQ hP) x

/-- The original diagonal point is the actual common coefficient image. -/
theorem reparametrizedStalk_middlePoint : m₀ y = m xᵦ :=
  scheme_point_congr
    (reparametrizedCoefficientQuotientMap_remainingPair U X Z T z w p r l hl eQ eP hQ hP).symm y

/-- The original ambient parameter quotient map at the common incidence. -/
def reparametrizedStalkParameterMap :
    (A).presheaf.stalk xₐ ⟶ (B).presheaf.stalk xᵦ :=
  let emb : B ⟶ A := j
  emb.stalkMapAtImage xᵦ xₐ
    (reparametrizedStalk_parameterPoint U X Z T z w p r l hl eQ eP hQ hP x)

/-- The remaining ambient quotient map at the common incidence. -/
def reparametrizedStalkRemainingMap :
    (B).presheaf.stalk xᵦ ⟶ (L).presheaf.stalk xₗ :=
  let emb : L ⟶ B := j'
  emb.stalkMapAtImage xₗ xᵦ
    (reparametrizedStalk_remainingPoint U X Z T z w p r l hl eQ eP hQ hP x)

/-- The original diagonal scalars in the ambient parameter quotient. -/
def reparametrizedStalkMiddleMap :
    (pullback X.hom X.hom).presheaf.stalk (m₀ y) ⟶ (B).presheaf.stalk xᵦ :=
  let middle : B ⟶ pullback X.hom X.hom := m
  middle.stalkMapAtImage xᵦ (m₀ y)
    (reparametrizedStalk_middlePoint U X Z T z w p r l hl eQ eP hQ hP x)

local notation3 (prettyPrint := false) "α" =>
  reparametrizedStalkParameterMap U X Z T z w p r l hl eQ eP hQ hP x
local notation3 (prettyPrint := false) "β" =>
  reparametrizedStalkRemainingMap U X Z T z w p r l hl eQ eP hQ hP x
local notation3 (prettyPrint := false) "σ" =>
  reparametrizedStalkMiddleMap U X Z T z w p r l hl eQ eP hQ hP x

/-- The two quotient routes into the common coefficient stalk agree literally. -/
theorem reparametrizedStalk_parameterSquare :
    (i).stalkMap (c y) ≫ (c).stalkMap y = α ≫ (d).stalkMap y := by
  let coeff : D ⟶ C := c
  let incl : C ⟶ A := i
  let quot : D ⟶ B := d
  let emb : B ⟶ A := j
  exact stalkMapAtImage_comp_eq coeff incl quot emb
    (reparametrizedCoefficientQuotientMap_ambient U X Z T z w p r l hl eQ eP hQ hP).symm y

/-- The remaining scalar map is independent of the parameter map. -/
theorem reparametrizedStalk_middleCoefficient :
    σ ≫ (d).stalkMap y = (m₀).stalkMap y := by
  let middle : B ⟶ pullback X.hom X.hom := m
  let quot : D ⟶ B := d
  let original : D ⟶ pullback X.hom X.hom := m₀
  exact stalkMapAtImage_comp_factor quot middle original
    (reparametrizedCoefficientQuotientMap_remainingPair U X Z T z w p r l hl eQ eP hQ hP) y

/-- The two successive actual quotients compose to the native triple stalk
map with its actual ambient point transport. -/
theorem reparametrizedStalk_tripleMap :
    let eA : correspondenceIncidenceAmbientStalk f g h z w xₙ ≅ (A).presheaf.stalk xₐ :=
      correspondenceIncidenceAmbientStalkIsoOfSupportPoint f g h z w xₙ (c y)
        (reparametrizedStalk_supportPoint U X Z T z w p r l hl eQ eP hQ hP x)
    (j₀).stalkMap xₗ = eA.hom ≫ α ≫ β := by
  let u₀ : L ⟶ B := j'
  let v₀ : B ⟶ A := j
  let w₀ : L ⟶ A := j₀
  let hC := reparametrizedStalk_supportPoint U X Z T z w p r l hl eQ eP hQ hP x
  let hA : xₐ = v₀ xᵦ := reparametrizedStalk_parameterPoint U X Z T z w p r l hl eQ eP hQ hP x
  let hB : xᵦ = u₀ xₗ := reparametrizedStalk_remainingPoint U X Z T z w p r l hl eQ eP hQ hP x
  let hV : w₀ xₗ = xₐ :=
    (correspondenceIncidence_ambient_point_eq f g h z w xₙ).trans (congrArg i hC.symm)
  exact stalkMap_comp_cast_factor u₀ v₀ w₀
    (exteriorAmbientRemainingInclusion_parameterInclusion U X Z T) xₗ xᵦ xₐ hB hA hV

end Stacks.Chow
