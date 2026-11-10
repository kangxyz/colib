/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenPullbackCoherence

/-! Identity and composition for the actual coarse supported geometric K-pullback. -/

noncomputable section
open CategoryTheory CategoryTheory.Waldhausen
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)

example (T : X.Opens) (n : ℕ) :
    boundedAboveFlatPerfectSupportedOpenKPullback j j (𝟙 (supportOpenPair T)) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) n = MonoidHom.id _ :=
  boundedAboveFlatPerfectSupportedOpenKPullback_id j T n

variable {U'' X'' : Scheme.{u}} (j'' : U'' ⟶ X'') [IsOpenImmersion j'']
  {R : X''.Opens} (f₀ : supportOpenPair R ⟶ supportOpenPair S)
  (g₀ : U'' ⟶ U') (w₀ : j'' ≫ f₀.right = g₀ ≫ j')

example (n : ℕ) :
    boundedAboveFlatPerfectSupportedOpenKPullback j'' j (f₀ ≫ f) (g₀ ≫ g)
      (supportedOpenSquare_comp j' j f g w j'' f₀ g₀ w₀) n =
    (boundedAboveFlatPerfectSupportedOpenKPullback j'' j' f₀ g₀ w₀ n).comp
      (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n) :=
  boundedAboveFlatPerfectSupportedOpenKPullback_comp j' j f g w j'' f₀ g₀ w₀ n

end AlgebraicGeometry.Scheme.Modules
