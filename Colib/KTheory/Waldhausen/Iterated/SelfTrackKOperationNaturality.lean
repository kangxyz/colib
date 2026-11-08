/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperation
public import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality
public import Colib.Topology.Prespectrum.SelfTrackStableNaturality

/-!
# Exact-functor naturality of the original K-group self-track operation

The existing original K-group comparisons intertwine the actual exact-functor
prespectrum maps. The proved stable naturality equations therefore retain
those same original K-maps in every nonnegative degree, including K-zero.
No scalar object value or localization boundary formula is asserted here.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/SelfTrackKOperationNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology SSet
variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  (W : Structure C) (V : Structure D) (U : Structure T)
  {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- Every original target K-map commutes with the self-track operation on each original class. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperationNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem originalKSelfTrackOperation_postcomp_apply (H : Homotopy f f)
    {J : D ⥤ T} (hJ : IsExact V.cof V.weq U.cof U.weq J) (n : ℕ) (a : W.K n) :
    originalKSelfTrackOperation W U (H.postcomp (exactOriginalPrespectrumMap V U hJ)) n a =
      KMap hJ (n + 1) (originalKSelfTrackOperation W V H n a) := by
  apply (originalKStableEquiv U (n + 1)).injective
  calc
    originalKStableEquiv U (n + 1)
        (Additive.ofMul
          (originalKSelfTrackOperation W U (H.postcomp (exactOriginalPrespectrumMap V U hJ)) n a)) =
      (H.postcomp (exactOriginalPrespectrumMap V U hJ)).stableOperation (n : ℤ)
        (originalKStableEquiv W n (Additive.ofMul a)) :=
      originalKSelfTrackOperation_stable W U _ n a
    _ = exactStableKMap V U hJ ((n + 1 : ℕ) : ℤ)
        (H.stableOperation (n : ℤ) (originalKStableEquiv W n (Additive.ofMul a))) :=
      ConcreteCategory.congr_hom
        (H.stableOperation_postcomp (exactOriginalPrespectrumMap V U hJ) (n : ℤ))
        (originalKStableEquiv W n (Additive.ofMul a))
    _ = exactStableKMap V U hJ ((n + 1 : ℕ) : ℤ)
        (originalKStableEquiv V (n + 1)
          (Additive.ofMul (originalKSelfTrackOperation W V H n a))) :=
      congrArg (fun b : stableHomotopyGroup (originalPrespectrum V) ((n + 1 : ℕ) : ℤ) ↦
        exactStableKMap V U hJ ((n + 1 : ℕ) : ℤ) b)
          (originalKSelfTrackOperation_stable W V H n a).symm
    _ = _ := (originalKStableEquiv_exact_naturality V U hJ (n + 1) _).symm

/-- Every original source K-map commutes with the self-track operation on each original class. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperationNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem originalKSelfTrackOperation_precomp_apply (H : Homotopy f f)
    {J : T ⥤ C} (hJ : IsExact U.cof U.weq W.cof W.weq J) (n : ℕ) (a : U.K n) :
    originalKSelfTrackOperation U V (H.precomp (exactOriginalPrespectrumMap U W hJ)) n a =
      originalKSelfTrackOperation W V H n (KMap hJ n a) := by
  apply (originalKStableEquiv V (n + 1)).injective
  calc
    originalKStableEquiv V (n + 1)
        (Additive.ofMul
          (originalKSelfTrackOperation U V (H.precomp (exactOriginalPrespectrumMap U W hJ)) n a)) =
      (H.precomp (exactOriginalPrespectrumMap U W hJ)).stableOperation (n : ℤ)
        (originalKStableEquiv U n (Additive.ofMul a)) :=
      originalKSelfTrackOperation_stable U V _ n a
    _ = H.stableOperation (n : ℤ)
        (exactStableKMap U W hJ (n : ℤ) (originalKStableEquiv U n (Additive.ofMul a))) :=
      ConcreteCategory.congr_hom
        (H.stableOperation_precomp (exactOriginalPrespectrumMap U W hJ) (n : ℤ))
        (originalKStableEquiv U n (Additive.ofMul a))
    _ = H.stableOperation (n : ℤ)
        (originalKStableEquiv W n (Additive.ofMul (KMap hJ n a))) :=
      congrArg (fun b : stableHomotopyGroup (originalPrespectrum W) (n : ℤ) ↦
        H.stableOperation (n : ℤ) b)
          (originalKStableEquiv_exact_naturality U W hJ n a).symm
    _ = _ := (originalKSelfTrackOperation_stable W V H n (KMap hJ n a)).symm

/-- The complete original target K-homomorphism equation, including input K-zero. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperationNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem originalKSelfTrackOperation_postcomp (H : Homotopy f f)
    {J : D ⥤ T} (hJ : IsExact V.cof V.weq U.cof U.weq J) (n : ℕ) :
    originalKSelfTrackOperation W U (H.postcomp (exactOriginalPrespectrumMap V U hJ)) n =
      (KMap hJ (n + 1)).comp (originalKSelfTrackOperation W V H n) := by
  ext a
  exact originalKSelfTrackOperation_postcomp_apply W V U H hJ n a

/-- The complete original source K-homomorphism equation, including input K-zero. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/SelfTrackKOperationNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem originalKSelfTrackOperation_precomp (H : Homotopy f f)
    {J : T ⥤ C} (hJ : IsExact U.cof U.weq W.cof W.weq J) (n : ℕ) :
    originalKSelfTrackOperation U V (H.precomp (exactOriginalPrespectrumMap U W hJ)) n =
      (originalKSelfTrackOperation W V H n).comp (KMap hJ n) := by
  ext a
  exact originalKSelfTrackOperation_precomp_apply W V U H hJ n a

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0321"]
  CategoryTheory.Waldhausen.IteratedS.originalKSelfTrackOperation_precomp
  CategoryTheory.Waldhausen.IteratedS.originalKSelfTrackOperation_postcomp
