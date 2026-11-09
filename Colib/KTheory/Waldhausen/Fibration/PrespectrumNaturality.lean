/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Fibration.Prespectrum
public import Colib.KTheory.Waldhausen.Fibration.Functoriality
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality
public import Colib.CategoryTheory.NaturalTransformation.HExt
public import Colib.Topology.Prespectrum.FiberLiftNaturality

/-!
# Naturality of the entire original canonical fiber prespectrum

Exact functors on nested weak equivalences preserve the actual specified acyclic null at every
stage and time, and hence the original path-space fiber lift. The independent structure parameter
is retained by these genuine prespectrum maps and homotopies. No stability of a comparison map
is assumed.

Implementation provenance: the constructions of `Quillen/Waldhausen/Fibration/Prespectrum.lean`
and `CanonicalFiberNaturality.lean`, and the whole transformation naturality in
`Quillen/Waldhausen/SConstruction/Iterated/PrespectrumHomotopyNaturality.lean`, at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Topology
open scoped Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.Fibration
open IteratedS

private lemma transformation_level_congr
    {A B : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {f f' g g' : A ⟶ B}
    (η : f.hom.toFunctor ⟶ g.hom.toFunctor)
    (η' : f'.hom.toFunctor ⟶ g'.hom.toFunctor)
    (hη : ∀ a, B.obj.waldhausen.weq (η.app a))
    (hη' : ∀ a, B.obj.waldhausen.weq (η'.app a))
    (hf : f = f') (hg : g = g') (he : HEq η η') (n : ℕ) :
    (prespectrumTransformationHomotopy η hη).level n =
      (prespectrumTransformationHomotopy η' hη').level n := by
  subst f'
  subst g'
  have hh := eq_of_heq he
  subst η'
  rfl

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

/-- Strict change of weaknesses commutes on the entire original prespectrum. -/
lemma changeWeakPrespectrumMap_natural (h0 : F.obj V.zero = W.zero) :
    changeWeakPrespectrumMap N ≫
        originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0) =
      originalPrespectrumMap V W hF h0 ≫ changeWeakPrespectrumMap M := by
  unfold changeWeakPrespectrumMap
  rw [← originalPrespectrumMap_comp, ← originalPrespectrumMap_comp]

/-- Strict acyclic inclusion commutes on the entire original prespectrum. -/
lemma acyclicInclusionPrespectrumMap_natural (h0 : F.obj V.zero = W.zero) :
    acyclicInclusionPrespectrumMap N ≫ originalPrespectrumMap V W hF h0 =
      originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
        (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0) ≫
        acyclicInclusionPrespectrumMap M := by
  unfold acyclicInclusionPrespectrumMap
  rw [← originalPrespectrumMap_comp, ← originalPrespectrumMap_comp]

/-- The full original reversed acyclic null is natural at every stage and every null time. -/
lemma acyclicPrespectrumNullhomotopy_natural (h0 : F.obj V.zero = W.zero)
    (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (acyclicStructure N)).space n) :
    (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0)).map n
        ((acyclicPrespectrumNullhomotopy N).level n (s, x)) =
      (acyclicPrespectrumNullhomotopy M).level n
        (s, (originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
          (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0)).map n x) := by
  let a := asSmallCategoryMap (acyclicStructure N) (acyclicStructure M)
    (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0)
  let c := asSmallCategoryMap N.coarse M.coarse hFc (coarse_zero_eq N M h0)
  let zN := asSmallCategoryMap (acyclicStructure N) N.coarse (zeroFunctor_isExact _ _) rfl
  let zM := asSmallCategoryMap (acyclicStructure M) M.coarse (zeroFunctor_isExact _ _) rfl
  let iN := asSmallCategoryMap (acyclicStructure N) N.coarse
    (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  let iM := asSmallCategoryMap (acyclicStructure M) M.coarse
    (acyclicInclusion_coarse_exact M)
    (by simpa only [acyclicInclusion_zero] using M.coarse_zero.symm)
  let ηN : zN.hom.toFunctor ⟶ iN.hom.toFunctor :=
    whiskerLeft AsSmall.down (whiskerRight (zeroToAcyclicInclusion N) AsSmall.up)
  let ηM : zM.hom.toFunctor ⟶ iM.hom.toFunctor :=
    whiskerLeft AsSmall.down (whiskerRight (zeroToAcyclicInclusion M) AsSmall.up)
  have hz : zN ≫ c = a ≫ zM := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ ↦ congrArg AsSmall.up.obj
      (coarse_zero_eq N M h0)) ?_
    intro i j f
    exact (hFc.asSmall.zero (N.coarse.asSmall.isZero)).eq_of_src _ _
  have hi : iN ≫ c = a ≫ iM := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    rfl
  have he : HEq (whiskerRight ηN c.hom.toFunctor) (whiskerLeft a.hom.toFunctor ηM) := by
    apply natTrans_heq_of_app_heq _ _
      (congrArg (fun k ↦ k.hom.toFunctor) hz) (congrArg (fun k ↦ k.hom.toFunctor) hi)
    intro y
    have h := (hFc.asSmall.zero N.coarse.asSmall.isZero).eq_of_src
      ((whiskerRight ηN c.hom.toFunctor).app y)
      (eqToHom (congrArg AsSmall.up.obj (coarse_zero_eq N M h0)) ≫
        (whiskerLeft a.hom.toFunctor ηM).app y)
    exact (heq_of_eq h).trans (eqToHom_comp_heq _ _)
  have hηN : ∀ A, (asSmallCategory N.coarse).obj.waldhausen.weq (ηN.app A) :=
    fun A ↦ zeroToAcyclicInclusion_weak N (AsSmall.down.obj A)
  have hηM : ∀ A, (asSmallCategory M.coarse).obj.waldhausen.weq (ηM.app A) :=
    fun A ↦ zeroToAcyclicInclusion_weak M (AsSmall.down.obj A)
  have hn := transformation_level_congr
    (whiskerRight ηN c.hom.toFunctor) (whiskerLeft a.hom.toFunctor ηM)
    (fun A ↦ c.hom.isExact.weak _ (hηN A))
    (fun A ↦ hηM (a.hom.toFunctor.obj A)) hz hi he n
  have hp := prespectrumTransformationHomotopy_postcomp_level ηN hηN c n
  have hq := prespectrumTransformationHomotopy_precomp_level ηM hηM a n
  exact congrArg (fun k ↦ k (unitInterval.symm s, x)) (hp.symm.trans (hn.trans hq))

/-- Naturality also retains the independent null time and structure-map time. -/
lemma acyclicPrespectrumNullhomotopy_natural_structure (h0 : F.obj V.zero = W.zero)
    (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (acyclicStructure N)).space n) :
    (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0)).map (n + 1)
        ((acyclicPrespectrumNullhomotopy N).level (n + 1)
          (s, (originalPrespectrum (acyclicStructure N)).structureMap n x t)) =
      (originalPrespectrum M.coarse).structureMap n
        ((acyclicPrespectrumNullhomotopy M).level n
          (s, (originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
            (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0)).map n x)) t := by
  rw [acyclicPrespectrumNullhomotopy_natural N M hF hFc h0]
  have hc := congrArg (fun p ↦ p t)
    ((originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
      (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0)).comm n x)
  change (originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
    (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0)).map (n + 1)
      ((originalPrespectrum (acyclicStructure N)).structureMap n x t) = _ at hc
  rw [hc]
  exact (acyclicPrespectrumNullhomotopy M).comm n s _ t

/-- The actual strict arrow square induces the original map of path-space fiber prespectra. -/
def fiberFunctorPrespectrumMap (h0 : F.obj V.zero = W.zero) :
    LoopPrespectrum.homotopyFiber (changeWeakPrespectrumMap N) ⟶
      LoopPrespectrum.homotopyFiber (changeWeakPrespectrumMap M) :=
  LoopPrespectrum.homotopyFiberMap
    (Arrow.homMk (f := Arrow.mk (changeWeakPrespectrumMap N))
      (g := Arrow.mk (changeWeakPrespectrumMap M))
      (originalPrespectrumMap V W hF h0)
      (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0))
      (changeWeakPrespectrumMap_natural N M hF hFc h0).symm)

/-- The original whole canonical fiber lift is natural, including its complete path coordinate. -/
lemma canonicalFiberPrespectrumMap_natural (h0 : F.obj V.zero = W.zero) :
    canonicalFiberPrespectrumMap N ≫ fiberFunctorPrespectrumMap N M hF hFc h0 =
      originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
        (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0) ≫
        canonicalFiberPrespectrumMap M :=
  LoopPrespectrum.homotopyFiberLift_naturality
    (acyclicInclusionPrespectrumMap N) (changeWeakPrespectrumMap N)
    (acyclicInclusionPrespectrumMap M) (changeWeakPrespectrumMap M)
    (acyclicPrespectrumNullhomotopy N) (acyclicPrespectrumNullhomotopy M)
    (originalPrespectrumMap (acyclicStructure N) (acyclicStructure M)
      (acyclicFunctor_exact N M hF hFc) (acyclicFunctor_zero N M hFc h0))
    (originalPrespectrumMap V W hF h0)
    (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0))
    (acyclicInclusionPrespectrumMap_natural N M hF hFc h0)
    (changeWeakPrespectrumMap_natural N M hF hFc h0).symm
    (acyclicPrespectrumNullhomotopy_natural N M hF hFc h0)

/-- Projection retains the original fine exact-functor map. -/
@[simp] lemma fiberFunctorPrespectrumMap_projection (h0 : F.obj V.zero = W.zero) :
    fiberFunctorPrespectrumMap N M hF hFc h0 ≫
        LoopPrespectrum.homotopyFiberProjection (changeWeakPrespectrumMap M) =
      LoopPrespectrum.homotopyFiberProjection (changeWeakPrespectrumMap N) ≫
        originalPrespectrumMap V W hF h0 :=
  LoopPrespectrum.homotopyFiberProjection_naturality _

/-- The fiber comparison applies the actual fine map to the source coordinate. -/
@[simp] lemma fiberFunctorPrespectrumMap_source (h0 : F.obj V.zero = W.zero) (n : ℕ)
    (x : (LoopPrespectrum.homotopyFiber (changeWeakPrespectrumMap N)).space n) :
    ((fiberFunctorPrespectrumMap N M hF hFc h0).map n x).1.1 =
      (originalPrespectrumMap V W hF h0).map n x.1.1 := rfl

/-- The fiber comparison applies the actual coarse map to the entire original path. -/
@[simp] lemma fiberFunctorPrespectrumMap_path (h0 : F.obj V.zero = W.zero) (n : ℕ)
    (x : (LoopPrespectrum.homotopyFiber (changeWeakPrespectrumMap N)).space n)
    (s : unitInterval) :
    ((fiberFunctorPrespectrumMap N M hF hFc h0).map n x).1.2 s =
      (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0)).map n
        (x.1.2 s) := rfl

/-- The signed stable connecting map is natural with the same original fiber comparison. -/
lemma stableFiberConnecting_natural (h0 : F.obj V.zero = W.zero) (d : ℤ) :
    (LoopPrespectrum.stableHomotopyFunctor (d + 1)).map
        (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0)) ≫
        LoopPrespectrum.stableFiberConnecting (changeWeakPrespectrumMap M) d =
      LoopPrespectrum.stableFiberConnecting (changeWeakPrespectrumMap N) d ≫
        (LoopPrespectrum.stableHomotopyFunctor d).map
          (fiberFunctorPrespectrumMap N M hF hFc h0) :=
  LoopPrespectrum.stableFiberConnecting_naturality
    (Arrow.homMk (f := Arrow.mk (changeWeakPrespectrumMap N))
      (g := Arrow.mk (changeWeakPrespectrumMap M))
      (originalPrespectrumMap V W hF h0)
      (originalPrespectrumMap N.coarse M.coarse hFc (coarse_zero_eq N M h0))
      (changeWeakPrespectrumMap_natural N M hF hFc h0).symm) d

end CategoryTheory.Waldhausen.Fibration

attribute [colib_tag "COL-0337",
  colib_ref "quillen" "Waldhausen/Fibration/Prespectrum.lean and CanonicalFiberNaturality.lean"
    "adaptation" "Naturality of the actual whole canonical null and path-space fiber lift"]
  CategoryTheory.Waldhausen.Fibration.acyclicPrespectrumNullhomotopy_natural
  CategoryTheory.Waldhausen.Fibration.canonicalFiberPrespectrumMap_natural

attribute [colib_tag "COL-0337",
  colib_ref "quillen" "Topology/Prespectrum/FiberNaturality.lean"
    "specialization" "The original signed stable connecting square for nested exact functors"]
  CategoryTheory.Waldhausen.Fibration.stableFiberConnecting_natural
