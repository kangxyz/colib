/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenPullback
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenFibration
public import Colib.KTheory.Waldhausen.Fibration.ConnectingNaturality

/-!
# Original supported bounded-flat boundary naturality

The induced acyclic functor is identified with the actual union-support geometric
pullback, and the original canonical connecting map commutes in every natural degree.
Independently chosen zeros are handled by the native exact-functor rebasing theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)

/-- The original acyclic flattening identifies the induced functor with union-support pullback. -/
theorem boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_pullback (n : ℕ) :
    (boundedAboveFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) n).comp
        (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j' S n).toMonoidHom.comp
        (KMap (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
          (boundedAboveFlatPerfectSupportedOpenNested j' S)
          (boundedAboveFlatPerfectSupportedPullback_isExact f)
          (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w)) n) := by
  exact (KMap_comp_KMap (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_exact j T)
    (boundedAboveFlatPerfectSupportedPullback_isExact (supportedPairUnionSquare j' j f g w))
    n).trans
    (KMap_comp_KMap
      (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
        (boundedAboveFlatPerfectSupportedOpenNested j' S)
        (boundedAboveFlatPerfectSupportedPullback_isExact f)
        (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w))
      (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_exact j' S) n).symm

/-- The actual supported boundary is natural, including the original K-one to K-zero map. -/
@[colib_tag "COL-0385",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenNaturality.lean:75-99"
    "adaptation"
    "Original union-support pullback and canonical boundary under arbitrary open squares"]
theorem boundedAboveFlatPerfectSupportedOpenConnectingHom_pullback (n : ℕ) :
    (boundedAboveFlatPerfectSupportedKPullback (supportedPairUnionSquare j' j f g w) n).comp
        (boundedAboveFlatPerfectSupportedOpenConnectingHom j T n) =
      (boundedAboveFlatPerfectSupportedOpenConnectingHom j' S n).comp
        (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w (n + 1)) := by
  refine MonoidHom.ext fun a => ?_
  have h := DFunLike.congr_fun
    (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_pullback j' j f g w n)
    (changeWeakConnectingHom (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n a)
  have hdelta := DFunLike.congr_fun
    (changeWeakConnectingHom_natural
      (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpenNested j' S)
      (boundedAboveFlatPerfectSupportedPullback_isExact f)
      (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T)
      (boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j' S) n) a
  exact h.trans (congrArg (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j' S n)
    hdelta)

end AlgebraicGeometry.Scheme.Modules
