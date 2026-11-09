/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.SupportedOpenFineForget

/-! # Full-signature consumers for auxiliary-support forgetting -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Waldhausen Fibration
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

example : IsExact (perfectSupportedOpenWeakWaldhausen j T).cof
    (perfectSupportedOpenWeakWaldhausen j T).weq (perfectOpenWeakWaldhausen j).cof
    (perfectOpenWeakWaldhausen j).weq (perfectSupportedInclusion T.ι) :=
  perfectSupportedInclusion_open_isExact j T

example (n : ℕ) : perfectSupportedOpenKForget j T n =
    KMap (perfectSupportedInclusion_open_isExact j T) n := rfl

example (K : (perfectSupported (T ⊔ j.opensRange).ι).FullSubcategory) :
    ((perfectSupportedUnionForget j T).obj K).obj = K.obj := rfl

example {K L : (perfectSupported (T ⊔ j.opensRange).ι).FullSubcategory} (f : K ⟶ L) :
    ((perfectSupportedUnionForget j T).map f).hom = f.hom := rfl

example : IsExact (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
    (perfectSupportedWaldhausen (T ⊔ j.opensRange).ι).weq
    (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
    (perfectSupportedUnionForget j T) :=
  perfectSupportedUnionForget_isExact j T

example (n : ℕ) : perfectSupportedUnionForgetKMap j T n =
    KMap (perfectSupportedUnionForget_isExact j T) n := rfl

example (n : ℕ) :
    (perfectSupportedOpenKForget j T n).comp (perfectSupportedOpenKMap j T n) =
      (perfectOpenKMap j n).comp (perfectSupportedKMap T.ι n) :=
  perfectSupportedOpenKForget_comp_changeWeak j T n

example (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectSupportedOpenKForget j T n) =
      (perfectSupportedKMap (j ⁻¹ᵁ T).ι n).comp (perfectSupportedOpenKRestrict j T n) :=
  perfectSupportedOpenKForget_comp_restrict j T n

example (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp
        (perfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (KMap (acyclicFunctor_exact (perfectSupportedOpenNested j T) (perfectOpenNested j)
          (perfectSupportedInclusion_isExact T.ι)
          (perfectSupportedInclusion_open_isExact j T)) n) :=
  perfectSupportedOpenAcyclicSupportedKEquiv_forget j T n

example (n : ℕ) :
    (perfectSupportedKMap T.ι n).comp (perfectSupportedUnionKMap j T n) =
      (perfectSupportedKMap j n).comp (perfectSupportedUnionForgetKMap j T n) :=
  perfectSupportedUnionKMap_comp_forget j T n

example (n : ℕ) :
    (perfectSupportedKMap (j ⁻¹ᵁ T).ι n).comp (perfectSupportedKRestrict j T n) =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).comp
        (perfectSupportedKMap T.ι n) :=
  perfectSupportedKRestrict_comp_forget j T n

example (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp (perfectSupportedOpenConnectingHom j T n) =
      (perfectOpenConnectingHom j n).comp (perfectSupportedOpenKForget j T (n + 1)) :=
  perfectSupportedOpenConnectingHom_forget j T n

example :
    (perfectSupportedUnionForgetKMap j T 0).comp
        (perfectSupportedOpenConnectingHom j T 0 : PerfectSupportedOpenCoarseK j T 1 →*
          PerfectSupportedK (T ⊔ j.opensRange).ι 0) =
      (perfectOpenConnectingHom j 0 : PerfectOpenK j 1 →* PerfectSupportedK j 0).comp
        (perfectSupportedOpenKForget j T 1) :=
  perfectSupportedOpenConnectingHom_forget j T 0

section Fine

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))

example (n : ℕ) (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1)) :
    perfectSupportedOpenKForget j T (n + 1)
        ((perfectSupportedOpenKEquivOfUnionCompact j T hW n).symm x) =
      (letI : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
        ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
       (OpenDerivedImage.relativeKRestrictEquiv j
         (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n).symm
         (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1) x)) :=
  perfectSupportedOpenKEquivOfUnionCompact_symm_forget j T hW n x

example (x : PerfectSupportedK (j ⁻¹ᵁ T).ι 1) :
    perfectSupportedOpenKForget j T 1
        ((perfectSupportedOpenKEquivOfUnionCompact j T hW 0).symm x) =
      (letI : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
        ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
       (OpenDerivedImage.relativeKRestrictEquiv j
         (OpenDerivedImage.hasPerfectComplements_of_qcqs j) 0).symm
         (perfectSupportedKMap (j ⁻¹ᵁ T).ι 1 x)) :=
  perfectSupportedOpenKEquivOfUnionCompact_symm_forget j T hW 0 x

example (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp
        (perfectSupportedConnectingHomOfUnionCompact j T hW n) =
      (perfectQcqsConnectingHom j n).comp
        (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1)) :=
  perfectSupportedConnectingHomOfUnionCompact_forget j T hW n

example :
    (perfectSupportedUnionForgetKMap j T 0).comp
        (perfectSupportedConnectingHomOfUnionCompact j T hW 0 :
          PerfectSupportedK (j ⁻¹ᵁ T).ι 1 →* PerfectSupportedK (T ⊔ j.opensRange).ι 0) =
      (perfectQcqsConnectingHom j 0 :
        (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 1 →*
          PerfectSupportedK j 0).comp (perfectSupportedKMap (j ⁻¹ᵁ T).ι 1) :=
  perfectSupportedConnectingHomOfUnionCompact_forget j T hW 0

example : (perfectSupportedKRestrict j T 1).range =
      (perfectSupportedConnectingHomOfUnionCompact j T hW 0).ker ∧
    (perfectSupportedConnectingHomOfUnionCompact j T hW 0).range =
      (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range = (perfectSupportedKRestrict j T 0).ker :=
  perfectSupported_zeroTail_of_union_compact j T hW

variable (hT : IsCompact (T : Set X))

example (n : ℕ) (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1)) :
    perfectSupportedOpenKForget j T (n + 1)
        ((perfectSupportedOpenKEquivOfUnionCompact j T
          (isCompact_supportedUnion j T hT) n).symm x) =
      (letI : Fact (OpenDerivedImage.HasDerivedRoofs j) :=
        ⟨OpenDerivedImage.hasDerivedRoofs_of_qcqs j⟩
       (OpenDerivedImage.relativeKRestrictEquiv j
         (OpenDerivedImage.hasPerfectComplements_of_qcqs j) n).symm
         (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1) x)) :=
  qcqsPerfectSupportedOpenKEquiv_symm_forget j T hT n x

example (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp
        (perfectSupportedConnectingHomOfUnionCompact j T (isCompact_supportedUnion j T hT) n) =
      (perfectQcqsConnectingHom j n).comp
        (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1)) :=
  qcqsPerfectSupportedConnectingHom_forget j T hT n

example :
    (perfectSupportedUnionForgetKMap j T 0).comp
        (perfectSupportedConnectingHomOfUnionCompact j T (isCompact_supportedUnion j T hT) 0 :
          PerfectSupportedK (j ⁻¹ᵁ T).ι 1 →* PerfectSupportedK (T ⊔ j.opensRange).ι 0) =
      (perfectQcqsConnectingHom j 0 :
        (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K 1 →*
          PerfectSupportedK j 0).comp (perfectSupportedKMap (j ⁻¹ᵁ T).ι 1) :=
  qcqsPerfectSupportedConnectingHom_forget j T hT 0

end Fine
