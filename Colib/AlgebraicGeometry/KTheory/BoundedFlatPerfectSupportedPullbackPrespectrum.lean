/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedBoundaryNaturality
public import Colib.KTheory.Waldhausen.Fibration.PrespectrumNaturality
public import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality

/-!
# The actual supported pullback on the whole relative fiber

One canonical rebasing of the original geometric functor is used for both fine and
coarse structures. Its original K-map is unchanged by the displayed natural isomorphism.
The entire canonical acyclic null path and fiber projection are retained. No equality
between independently chosen zeros or independently normalized functors is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open scoped unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U' X' U X : Scheme.{u}} (j' : U' ⟶ X') (j : U ⟶ X)
  [IsOpenImmersion j'] [IsOpenImmersion j] {S : X'.Opens} {T : X.Opens}
  (f : supportOpenPair S ⟶ supportOpenPair T) (g : U' ⟶ U)
  (w : j' ≫ f.right = g ≫ j)


/-- The single canonical normalization of the original supported geometric functor. -/
def boundedAboveFlatPerfectSupportedPullbackNormalized :
    (boundedAboveFlatPerfectSupported T.ι).FullSubcategory ⥤
      (boundedAboveFlatPerfectSupported S.ι).FullSubcategory :=
  CategoryTheory.rebaseFunctor (boundedAboveFlatPerfectSupportedPullback f)
    (boundedAboveFlatPerfectSupportedWaldhausen T.ι).zero
      (boundedAboveFlatPerfectSupportedWaldhausen S.ι).zero
      (((boundedAboveFlatPerfectSupportedPullback_isExact f).zero
      (boundedAboveFlatPerfectSupportedWaldhausen T.ι).isZero).iso
      (boundedAboveFlatPerfectSupportedWaldhausen S.ι).isZero)

/-- The displayed original-to-normalized isomorphism controls the unchanged K-map. -/
def boundedAboveFlatPerfectSupportedPullbackNormalizationIso :
    boundedAboveFlatPerfectSupportedPullback f ≅
      boundedAboveFlatPerfectSupportedPullbackNormalized f :=
  CategoryTheory.rebaseFunctorIso (boundedAboveFlatPerfectSupportedPullback f)
    (boundedAboveFlatPerfectSupportedWaldhausen T.ι).zero
      (boundedAboveFlatPerfectSupportedWaldhausen S.ι).zero
      (((boundedAboveFlatPerfectSupportedPullback_isExact f).zero
      (boundedAboveFlatPerfectSupportedWaldhausen T.ι).isZero).iso
      (boundedAboveFlatPerfectSupportedWaldhausen S.ι).isZero)

include g w in
/-- The same normalized functor is exact for the actual coarse structures. -/
theorem boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact :
    IsExact (boundedAboveFlatPerfectSupportedOpenNested j T).coarse.cof
      (boundedAboveFlatPerfectSupportedOpenNested j T).coarse.weq
      (boundedAboveFlatPerfectSupportedOpenNested j' S).coarse.cof
        (boundedAboveFlatPerfectSupportedOpenNested j' S).coarse.weq
      (boundedAboveFlatPerfectSupportedPullbackNormalized f) :=
  (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w).of_iso
    (boundedAboveFlatPerfectSupportedPullbackNormalizationIso f)

/-- Only the explicitly normalized functor preserves the independent chosen zeros strictly. -/
theorem boundedAboveFlatPerfectSupportedPullbackNormalized_zero :
    (boundedAboveFlatPerfectSupportedPullbackNormalized f).obj
      (boundedAboveFlatPerfectSupportedWaldhausen T.ι).zero =
      (boundedAboveFlatPerfectSupportedWaldhausen S.ι).zero :=
  CategoryTheory.rebaseFunctor_obj_base _ _ _ _


/-- Canonical normalization preserves the original coarse K-pullback in every natural degree. -/
theorem boundedAboveFlatPerfectSupportedOpenKPullback_normalized (n : ℕ) :
    boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n =
      KMap (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w) n :=
  KMap_eq_of_iso (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w)
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
    (boundedAboveFlatPerfectSupportedPullbackNormalizationIso f) n

/-- The acyclic K-map also remains the original one after the same canonical normalization. -/
theorem boundedAboveFlatPerfectSupportedAcyclicKPullback_normalized (n : ℕ) :
    KMap (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpenNested j' S)
      (boundedAboveFlatPerfectSupportedPullback_isExact f)
      (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w)) n =
      KMap (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
        (boundedAboveFlatPerfectSupportedOpenNested j' S)
        (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
        (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)) n :=
  KMap_eq_of_iso (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenNested j' S)
    (boundedAboveFlatPerfectSupportedPullback_isExact f)
    (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w))
    (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpenNested j' S)
      (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
      (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w))
    (acyclicFunctorIso (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpenNested j' S)
      (boundedAboveFlatPerfectSupportedOpenPullback_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedPullbackNormalizationIso f)) n

/-- The actual coarse prespectrum arrow induced by this one normalized geometric functor. -/
def boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap :
    originalPrespectrum (boundedAboveFlatPerfectSupportedOpenNested j T).coarse ⟶
      originalPrespectrum (boundedAboveFlatPerfectSupportedOpenNested j' S).coarse :=
  originalPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T).coarse
    (boundedAboveFlatPerfectSupportedOpenNested j' S).coarse
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
    (coarse_zero_eq (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpenNested j' S)
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f))

/-- The original acyclic-to-fiber comparison is functorial for the specified normalized pullback. -/
def boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap :
    homotopyFiber (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T)) ⟶
      homotopyFiber (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j' S)) :=
  fiberFunctorPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenNested j' S)
    (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f)

/-- Projection keeps the original fine geometric pullback with its canonical normalization. -/
theorem boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap_projection :
    boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w ≫
        homotopyFiberProjection (changeWeakPrespectrumMap
          (boundedAboveFlatPerfectSupportedOpenNested j' S)) =
      homotopyFiberProjection (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested
        j T)) ≫
        exactOriginalPrespectrumMap (boundedAboveFlatPerfectSupportedWaldhausen T.ι)
          (boundedAboveFlatPerfectSupportedWaldhausen S.ι)
          (boundedAboveFlatPerfectSupportedPullback_isExact f) :=
  fiberFunctorPrespectrumMap_projection (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenNested j' S)
    (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f)

/-- Every original path coordinate is transported by the specified coarse map at every time. -/
theorem boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap_path (n : ℕ)
    (x : (homotopyFiber (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j
      T))).space n) (s : unitInterval) :
    ((boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w).map n x).1.2 s =
      (boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap j' j f g w).map n (x.1.2 s) :=
  fiberFunctorPrespectrumMap_path (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenNested j' S)
    (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f) n x s

/-- The entire canonical acyclic null path is natural, not just its endpoint or stable class. -/
@[colib_tag "COL-0507",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenNaturality.lean:75-99"
    "ingredient" "Actual boundary naturality; native chosen-zero and whole-null-path extension"]
theorem boundedAboveFlatPerfectSupportedOpenNullhomotopy_pullback (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j
      T))).space n) :
    (boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap j' j f g w).map n
        ((acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectSupportedOpenNested j T)).level n
          (s, x)) =
      (acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectSupportedOpenNested j' S)).level n
        (s, (originalPrespectrumMap (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j
          T)) (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j' S))
          (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
            (boundedAboveFlatPerfectSupportedOpenNested j' S)
            (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
            (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w))
          (acyclicFunctor_zero (boundedAboveFlatPerfectSupportedOpenNested j T)
            (boundedAboveFlatPerfectSupportedOpenNested j' S)
            (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
            (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f))).map
            n x) :=
  acyclicPrespectrumNullhomotopy_natural (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenNested j' S)
    (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f) n s x

/-- The full canonical fiber maps commute for this explicitly chosen rebasing. -/
theorem boundedAboveFlatPerfectSupportedCanonicalFiberPrespectrumMap_pullback :
    canonicalFiberPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j T) ≫
        boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w =
      originalPrespectrumMap (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T))
        (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j' S))
        (acyclicFunctor_exact (boundedAboveFlatPerfectSupportedOpenNested j T)
          (boundedAboveFlatPerfectSupportedOpenNested j' S)
          (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
          (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w))
        (acyclicFunctor_zero (boundedAboveFlatPerfectSupportedOpenNested j T)
          (boundedAboveFlatPerfectSupportedOpenNested j' S)
          (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
          (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f)) ≫
          canonicalFiberPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j' S) :=
  canonicalFiberPrespectrumMap_natural (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenNested j' S)
    (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f)

/-- The actual coarse spectrum map induces the original geometric K-pullback. -/
theorem boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap_K_naturality
    (n : ℕ) (a : BoundedAboveFlatPerfectSupportedOpenK j T n) :
    originalKStableEquiv (boundedAboveFlatPerfectSupportedOpenNested j' S).coarse n
        (Additive.ofMul (boundedAboveFlatPerfectSupportedOpenKPullback j' j f g w n a)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap j' j f g w)
        (originalKStableEquiv (boundedAboveFlatPerfectSupportedOpenNested j T).coarse n
          (Additive.ofMul a)) := by
  rw [boundedAboveFlatPerfectSupportedOpenKPullback_normalized]
  exact originalKStableEquiv_naturality (boundedAboveFlatPerfectSupportedOpenNested j T).coarse
    (boundedAboveFlatPerfectSupportedOpenNested j' S).coarse
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w) (coarse_zero_eq
      (boundedAboveFlatPerfectSupportedOpenNested j T) (boundedAboveFlatPerfectSupportedOpenNested
      j' S) (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f)) n a

/-- Every signed stable connecting degree uses the same actual coarse and fiber maps. -/
theorem boundedAboveFlatPerfectSupportedStableConnecting_pullback (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        (boundedAboveFlatPerfectSupportedOpenPullbackPrespectrumMap j' j f g w) ≫
        stableFiberConnecting (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested
          j' S)) d =
      stableFiberConnecting (changeWeakPrespectrumMap (boundedAboveFlatPerfectSupportedOpenNested j
        T)) d ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatPerfectSupportedFiberPullbackPrespectrumMap j' j f g w) :=
  stableFiberConnecting_natural (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenNested j' S)
    (boundedAboveFlatPerfectSupportedPullback_isExact f).rebase
    (boundedAboveFlatPerfectSupportedOpenPullbackNormalized_isExact j' j f g w)
      (boundedAboveFlatPerfectSupportedPullbackNormalized_zero f) d

end AlgebraicGeometry.Scheme.Modules
