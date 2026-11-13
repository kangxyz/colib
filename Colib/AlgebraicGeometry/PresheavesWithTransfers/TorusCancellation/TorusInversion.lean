/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NativeChart
public import Colib.AlgebraicGeometry.Sites.Smooth.Torus

/-!
# The native torus inverse

The inverse is the morphism representing the inverse of the original
global torus coordinate. Pullback of that coordinate proves involutivity
and preservation of the literal unit section.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory NativeTorusPolynomial
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u})

local notation "G" => multiplicativeGroupObject S
local notation "t" => multiplicativeGroupBaseChangeCoordinate S

/-- Inversion on the existing multiplicative group over the original base. -/
def torusInversion : G ⟶ G :=
  homMk (nativeTorusPoint (G).hom t⁻¹).left (nativeTorusPoint_over (G).hom t⁻¹)

/-- The actual pullback of the torus coordinate is its inverse unit. -/
theorem torusInversion_coordinate :
    Units.map (torusInversion S).left.appTop.hom.toMonoidHom t = t⁻¹ :=
  nativeTorusPoint_coordinate (G).hom t⁻¹

private theorem torusPoint_ext {X : SmoothSite S} (f g : X ⟶ G)
    (h : Units.map f.left.appTop.hom.toMonoidHom t =
      Units.map g.left.appTop.hom.toMonoidHom t) : f = g := by
  let f' : Over.mk X.hom ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S :=
    Over.homMk f.left (MorphismProperty.Over.w f)
  let g' : Over.mk X.hom ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S :=
    Over.homMk g.left (MorphismProperty.Over.w g)
  have he : f' = g' := by
    rw [← nativeTorusPoint_recover X.hom f', ← nativeTorusPoint_recover X.hom g']
    exact congrArg (nativeTorusPoint X.hom) h
  apply MorphismProperty.Over.Hom.ext
  exact congrArg (fun a => a.left) he

private theorem torusPoint_coordinate_comp {X Y : SmoothSite S} (f : X ⟶ Y) (g : Y ⟶ G) :
    Units.map (f ≫ g).left.appTop.hom.toMonoidHom t =
      Units.map f.left.appTop.hom.toMonoidHom (Units.map g.left.appTop.hom.toMonoidHom t) := by
  apply Units.ext
  change (f.left ≫ g.left).appTop (t).val = f.left.appTop (g.left.appTop (t).val)
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Inversion twice is the identity on the actual torus. -/
@[reassoc (attr := simp)]
theorem torusInversion_comp_self : torusInversion S ≫ torusInversion S = 𝟙 G := by
  apply torusPoint_ext S
  rw [torusPoint_coordinate_comp, torusInversion_coordinate, map_inv,
    torusInversion_coordinate, inv_inv]
  apply Units.ext
  change (t).val = (𝟙 (G).left : (G).left ⟶ (G).left).appTop (t).val
  simp only [Scheme.Hom.id_appTop, CommRingCat.id_apply]

/-- Inversion preserves the actual unit section of the torus. -/
@[reassoc (attr := simp)]
theorem torusOne_comp_torusInversion : torusOne S ≫ torusInversion S = torusOne S := by
  apply torusPoint_ext S
  have h : Units.map (torusOne S).left.appTop.hom.toMonoidHom t = 1 :=
    nativeTorusPoint_coordinate (𝟙 S) 1
  rw [torusPoint_coordinate_comp, torusInversion_coordinate, map_inv, h, inv_one]

end AlgebraicGeometry.Scheme.SmoothSite
