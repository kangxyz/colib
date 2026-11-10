/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedPullback
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Support
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenComparison

/-!
# Actual supported relative-open pullback and restriction

Two original commuting open squares preserve the fine and coarse weak structures.
Restriction agrees with geometric pullback through its specified natural isomorphism.
No compactness, flatness or cartesian-square assumption is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)

include g w in
/-- The actual supported pullback is also exact for open-detected weak equivalences. -/
@[colib_tag "COL-0507",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/PairPullback.lean:35-54"
    "adaptation" "Actual fine-and-coarse pullback without compactness or flatness hypotheses"]
theorem boundedAboveFlatPerfectSupportedOpenPullback_isExact :
    IsExact (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).weq
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j' S).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j' S).weq
      (boundedAboveFlatPerfectSupportedPullback f) where
  zero := (boundedAboveFlatPerfectSupportedPullback_isExact f).zero
  cofibration := (boundedAboveFlatPerfectSupportedPullback_isExact f).cofibration
  pushout := (boundedAboveFlatPerfectSupportedPullback_isExact f).pushout
  weak {K L} p hp := by
    exact @boundedAboveFlatPerfect_pairPullback_quasiIso _ _
      (supportedOpenRestrictionSquare j' j f g w) K.obj L.obj K.property.1 L.property.1 p.hom hp

/-- The relative K-map retains the actual supported geometric pullback. -/
def boundedAboveFlatPerfectSupportedOpenKPullback (n : ℕ) :
    BoundedAboveFlatPerfectSupportedOpenK j T n →*
      BoundedAboveFlatPerfectSupportedOpenK j' S n :=
  KMap (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w) n

/-- The original identity change-of-weak map commutes with the actual pair pullback. -/
theorem boundedAboveFlatPerfectSupportedOpenKPullback_changeWeak (n : ℕ) :
    (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n).comp
        (boundedAboveFlatPerfectSupportedOpenKMap j T n) =
      (boundedAboveFlatPerfectSupportedOpenKMap j' S n).comp
        (boundedAboveFlatPerfectSupportedKPullback f n) := by
  exact (KMap_comp_KMap (changeWeak_exact (boundedAboveFlatPerfectSupportedOpenNested j T))
    (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w) n).trans
    (KMap_comp_KMap (boundedAboveFlatPerfectSupportedPullback_isExact f)
      (changeWeak_exact (boundedAboveFlatPerfectSupportedOpenNested j' S)) n).symm

/-- The original open restriction is exact for the source relative weak structure. -/
theorem boundedAboveFlatPerfectSupportedOpenRestriction_isExact :
    IsExact (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).cof
      (boundedAboveFlatPerfectSupportedOpenWaldhausen j T).weq
      (boundedAboveFlatPerfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof
      (boundedAboveFlatPerfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq
      (boundedAboveFlatPerfectSupportedPullback (supportRestrictionPair j T)) where
  zero := (boundedAboveFlatPerfectSupportedPullback_isExact (supportRestrictionPair j T)).zero
  cofibration :=
    (boundedAboveFlatPerfectSupportedPullback_isExact (supportRestrictionPair j T)).cofibration
  pushout := (boundedAboveFlatPerfectSupportedPullback_isExact (supportRestrictionPair j T)).pushout
  weak {K L} p hp := by
    let : QuasiIso (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map p.hom) := hp
    let e := NatIso.mapHomologicalComplex (restrictFunctorIsoPullback j) (.up ℤ)
    change QuasiIso (((pullback j).mapHomologicalComplex (.up ℤ)).map p.hom)
    exact quasiIso_of_arrow_mk_iso
      (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map p.hom)
      (((pullback j).mapHomologicalComplex (.up ℤ)).map p.hom)
      (Arrow.isoMk (e.app K.obj) (e.app L.obj) (e.hom.naturality p.hom).symm)

/-- The original relative restriction map on the supported bounded-flat K-groups. -/
def boundedAboveFlatPerfectSupportedOpenKRestrict (n : ℕ) :
    BoundedAboveFlatPerfectSupportedOpenK j T n →*
      BoundedAboveFlatPerfectSupportedK (j ⁻¹ᵁ T).ι n :=
  KMap (boundedAboveFlatPerfectSupportedOpenRestriction_isExact j) n

/-- The two original geometric restriction-pullback routes retain their specified isomorphism. -/
def boundedAboveFlatPerfectSupportedOpenPairIso :
    boundedAboveFlatPerfectSupportedPullback f ⋙
        boundedAboveFlatPerfectSupportedPullback (supportRestrictionPair j' S) ≅
      boundedAboveFlatPerfectSupportedPullback (supportRestrictionPair j T) ⋙
        boundedAboveFlatPerfectSupportedPullback (supportedPairTargetSquare j' j f g w) :=
  Functor.fullyFaithfulCancelRight
    (boundedAboveFlatPerfectSupported (supportOpenPair (j' ⁻¹ᵁ S)).hom).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectSupported (supportOpenPair T).hom).ι
      (Functor.mapHomologicalComplexCompIso (pullbackComp j' (show X' ⟶ X from f.right)) (.up ℤ) ≪≫
        eqToIso (congrArg (fun h => (pullback h).mapHomologicalComplex (.up ℤ)) w) ≪≫
        (Functor.mapHomologicalComplexCompIso (pullbackComp g j) (.up ℤ)).symm))

/-- The actual original restriction K-map commutes with the supplied pair square. -/
@[colib_tag "COL-0507",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenNaturality.lean:151-172"
    "adaptation" "Original restriction-pullback square through the specified geometric isomorphism"]
theorem boundedAboveFlatPerfectSupportedOpenKRestrict_pullback (n : ℕ) :
    (boundedAboveFlatPerfectSupportedKPullback (supportedPairTargetSquare j' j f g w) n).comp
        (boundedAboveFlatPerfectSupportedOpenKRestrict j n) =
      (boundedAboveFlatPerfectSupportedOpenKRestrict j' n).comp
        (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n) := by
  exact (KMap_comp_KMap (boundedAboveFlatPerfectSupportedOpenRestriction_isExact j)
    (boundedAboveFlatPerfectSupportedPullback_isExact (supportedPairTargetSquare j' j f g w))
    n).trans
    ((KMap_eq_of_iso
      ((boundedAboveFlatPerfectSupportedOpenRestriction_isExact j).comp
        (boundedAboveFlatPerfectSupportedPullback_isExact (supportedPairTargetSquare j' j f g w)))
      ((boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w).comp
        (boundedAboveFlatPerfectSupportedOpenRestriction_isExact j'))
      (boundedAboveFlatPerfectSupportedOpenPairIso j' j f g w).symm n).trans
      (KMap_comp_KMap (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w)
        (boundedAboveFlatPerfectSupportedOpenRestriction_isExact j') n).symm)

end AlgebraicGeometry.Scheme.Modules
