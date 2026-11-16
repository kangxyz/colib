/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectOpenLongExactSequence
public import Colib.AlgebraicGeometry.Modules.PerfectOpenExactSquare
public import Colib.KTheory.Waldhausen.Fibration.ConnectingNaturality

/-! # Naturality of the relative perfect-complex boundary

The acyclic flattening is literal: the same perfect complex with acyclic
restriction is viewed in the supported full subcategory.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X V Y : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]

local notation:max "W[" Z "]" =>
  RingedSpace.perfectComplexesWaldhausen
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Z))

local notation:max "Perf[" Z "]" =>
  ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
    (X := LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Z)))

variable {F : Perf[X] ⥤ Perf[Y]}
  (hf : IsExact (W[X]).cof (W[X]).weq (W[Y]).cof (W[Y]).weq F)
  (hc : IsExact (perfectOpenNested j).coarse.cof (perfectOpenNested j).coarse.weq
    (perfectOpenNested k).coarse.cof (perfectOpenNested k).coarse.weq F)
  {S : (perfectSupported j).FullSubcategory ⥤ (perfectSupported k).FullSubcategory}
  (hs : IsExact (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
    (perfectSupportedWaldhausen k).cof (perfectSupportedWaldhausen k).weq S)

include hf in
/-- Compatibility with the actual acyclic flattening gives naturality of the
original relative boundary, including its K-one to K-zero component. -/
theorem perfectOpenConnectingHom_natural (n : ℕ)
    (e : perfectAcyclicToSupported j ⋙ S ≅
      acyclicFunctor (perfectOpenNested j) (perfectOpenNested k) hc ⋙
        perfectAcyclicToSupported k) :
    (KMap hs n).comp (perfectOpenConnectingHom j n) =
      (perfectOpenConnectingHom k n).comp (KMap hc (n + 1)) := by
  have hflat : (KMap hs n).comp (perfectAcyclicSupportedKEquiv j n).toMonoidHom =
      (perfectAcyclicSupportedKEquiv k n).toMonoidHom.comp
        (KMap (acyclicFunctor_exact (perfectOpenNested j) (perfectOpenNested k) hf hc) n) := by
    change (KMap hs n).comp (KMap (perfectAcyclicToSupported_exact j) n) =
      (KMap (perfectAcyclicToSupported_exact k) n).comp _
    rw [KMap_comp_KMap, KMap_comp_KMap]
    exact KMap_eq_of_iso _ _ e n
  ext x
  let δj := changeWeakConnectingHom (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) n
  let δk := changeWeakConnectingHom (perfectOpenNested k)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence k) n
  change KMap hs n (perfectAcyclicSupportedKEquiv j n (δj x)) =
    perfectAcyclicSupportedKEquiv k n (δk (KMap hc (n + 1) x))
  exact (DFunLike.congr_fun hflat (δj x)).trans
    (congrArg (perfectAcyclicSupportedKEquiv k n)
      (DFunLike.congr_fun
        (changeWeakConnectingHom_natural (perfectOpenNested j) (perfectOpenNested k) hf hc
          (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j)
          (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence k) n) x))

variable {G : Perf[U] ⥤ Perf[V]}
  (hg : IsExact (W[U]).cof (W[U]).weq (W[V]).cof (W[V]).weq G)

/-- Restricting the coarse map to the fine open is computed by the actual open functor. -/
theorem perfectOpenKRestrict_natural (n : ℕ)
    (e : F ⋙ perfectComplexesRestrictOpenImmersion k ≅
      perfectComplexesRestrictOpenImmersion j ⋙ G) :
    (perfectOpenKRestrict k n).comp (KMap hc n) =
      (KMap hg n).comp (perfectOpenKRestrict j n) := by
  change (KMap (perfectOpenRestrict_isExact k) n).comp (KMap hc n) =
    (KMap hg n).comp (KMap (perfectOpenRestrict_isExact j) n)
  erw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ e n

end AlgebraicGeometry.Scheme.Modules
