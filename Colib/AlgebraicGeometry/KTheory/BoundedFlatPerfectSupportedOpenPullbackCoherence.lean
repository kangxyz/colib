/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenPullback

/-! Identity and composition for the actual coarse supported geometric K-pullback. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Waldhausen
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)

@[simp]
theorem boundedAboveFlatPerfectSupportedOpenKPullback_id (T : X.Opens) (n : ℕ) :
    boundedAboveFlatPerfectSupportedOpenKPullback j j (𝟙 (supportOpenPair T)) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp) n = MonoidHom.id _ :=
  (KMap_eq_of_iso
    (boundedAboveFlatPerfectSupportedOpenPullback_isExact j j (𝟙 (supportOpenPair T)) (𝟙 U)
      (by change j ≫ 𝟙 X = 𝟙 U ≫ j; simp))
    (IsExact.id (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).weq)
    (boundedAboveFlatPerfectSupportedPullbackIdIso (supportOpenPair T)) n).trans
      (KMap_id _ n)

variable {U'' X'' : Scheme.{u}} (j'' : U'' ⟶ X'') [IsOpenImmersion j'']
  {R : X''.Opens} (f₀ : supportOpenPair R ⟶ supportOpenPair S)
  (g₀ : U'' ⟶ U') (w₀ : j'' ≫ f₀.right = g₀ ≫ j')

include w w₀ in
omit [IsOpenImmersion j'] [IsOpenImmersion j] [IsOpenImmersion j''] in
/-- Composition of the original commuting squares retains the literal ambient composites. -/
theorem supportedOpenSquare_comp :
    j'' ≫ (f₀ ≫ f).right = (g₀ ≫ g) ≫ j := by
  let a : X'' ⟶ X' := f₀.right
  let b : X' ⟶ X := f.right
  have h₀ : j'' ≫ a = g₀ ≫ j' := w₀
  have h : j' ≫ b = g ≫ j := w
  exact (Category.assoc j'' a b).symm.trans
    ((congrArg (fun k : U'' ⟶ X' => k ≫ b) h₀).trans
      ((Category.assoc g₀ j' b).trans
        ((congrArg (fun k : U' ⟶ X => g₀ ≫ k) h).trans
          (Category.assoc g₀ g j).symm)))

/-- Contravariant composition uses the original supported functor composition isomorphism. -/
@[colib_tag "COL-0507",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/PairPullback.lean:167-184"
    "adaptation" "Actual coarse supported K-pullback composition without compactness"]
theorem boundedAboveFlatPerfectSupportedOpenKPullback_comp (n : ℕ) :
    boundedAboveFlatPerfectSupportedOpenKPullback j'' j (f₀ ≫ f) (g₀ ≫ g)
      (supportedOpenSquare_comp j' j f g w j'' f₀ g₀ w₀) n =
    (boundedAboveFlatPerfectSupportedOpenKPullback j'' j' f₀ g₀ w₀ n).comp
      (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n) :=
  (KMap_eq_of_iso
    (boundedAboveFlatPerfectSupportedOpenPullback_isExact j'' j (f₀ ≫ f) (g₀ ≫ g)
      (supportedOpenSquare_comp j' j f g w j'' f₀ g₀ w₀))
    ((boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w).comp
      (boundedAboveFlatPerfectSupportedOpenPullback_isExact j'' j' f₀ g₀ w₀))
    (boundedAboveFlatPerfectSupportedPullbackCompIso f₀ f) n).trans
      (KMap_comp_KMap _ _ n).symm

end AlgebraicGeometry.Scheme.Modules
