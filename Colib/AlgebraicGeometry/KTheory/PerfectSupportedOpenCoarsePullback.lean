/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenPullback

/-!
# Original geometric perfect K-pullback

Selected literal inclusion transports of the original geometric bounded-flat pullback.
Only the declarations below are included; no new K-zero model or localization result is defined.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)
variable [CompactSpace X'] [CompactSpace X]

/-- Original supported relative K-pullback through the literal bounded-flat inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/PairPullback.lean:73"
  "adaptation" "Original geometric pullback through the literal inclusion comparison."]
def perfectSupportedOpenKPullback (n : ℕ) :
    PerfectSupportedOpenCoarseK j T n →* PerfectSupportedOpenCoarseK j' S n :=
  (boundedAboveFlatPerfectSupportedOpenKEquiv j' S n).toMonoidHom.comp
    ((boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n).comp
      (boundedAboveFlatPerfectSupportedOpenKEquiv j T n).symm.toMonoidHom)

/-- The relative pullback retains the original bounded-flat comparison square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/PairPullback.lean:79"
  "adaptation" "Original geometric pullback through the literal inclusion comparison."]
lemma perfectSupportedOpenKPullback_comp_boundedFlat (n : ℕ) :
    (perfectSupportedOpenKPullback j' j f g w n).comp
        (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j T n) =
      (boundedAboveFlatPerfectSupportedOpenToPerfectKMap j' S n).comp
        (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n) := by
  ext x
  change boundedAboveFlatPerfectSupportedOpenKEquiv j' S n
    (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n
      ((boundedAboveFlatPerfectSupportedOpenKEquiv j T n).symm
        (boundedAboveFlatPerfectSupportedOpenKEquiv j T n x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end AlgebraicGeometry.Scheme.Modules
