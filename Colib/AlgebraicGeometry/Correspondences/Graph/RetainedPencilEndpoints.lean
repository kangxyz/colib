/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.NativePencilFibers
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism

/-!
# Genuine zero and one endpoints of the retained-product polynomial family

The producer is exactly the retained product, not arbitrary source and target
maps. Its actual paired map is closed by the existing separated-base theorem.
The whole finite-flat hypothesis is transported through the actual cylinder
isomorphism. Graph precomposition then gives the full literal zero schemes of
the two original sections, with the actual source and target projections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open Scheme Scheme.PolynomialSectionPencil Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] {S X V : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t] (q : X ⟶ S) (r : V ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  (L : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L] (a c : Γ(L, ⊤))

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "F" => familySource (q ≫ t) (pullback.fst q r) L a c ≫
  (nativeParameterIso (.of k) U).inv
local notation "G" => retainedFamilyTarget t q r L a c

/-- The original actual native-family legs satisfy the ground-field equation. -/
theorem nativeRetainedFamily_base : F ≫ (affineLineCylinder.obj U).hom = G ≫ (r ≫ t) := by
  rw [← nativeRetainedFamilyPair_fst t q r L a c,
    ← nativeRetainedFamilyPair_snd t q r L a c]
  simp only [Category.assoc, pullback.condition]

/-- The actual Cartesian endpoint legs satisfy the same ground-field equation. -/
theorem nativeRetainedEndpoint_base (s : k) :
    pullback.fst (nativeAffineSection (.of k) U s).left F ≫ (q ≫ t) =
      (pullback.snd (nativeAffineSection (.of k) U s).left F ≫ G) ≫ (r ≫ t) := by
  rw [← MorphismProperty.Over.w (nativeAffineSection (.of k) U s),
    ← Category.assoc, pullback.condition]
  simp only [Category.assoc, nativeRetainedFamily_base]

/-- The original literal zero-scheme source and target maps commute over the field. -/
theorem retainedZero_base (s : Γ(L, ⊤)) :
    ((zeroScheme (pullback q r) L s).subschemeι ≫ pullback.fst q r) ≫ (q ≫ t) =
      ((zeroScheme (pullback q r) L s).subschemeι ≫ pullback.snd q r) ≫ (r ≫ t) := by
  simp only [Category.assoc, pullback.condition_assoc]

variable [IsFinite F] [Flat F]

/-- Whole-family specialization to its actual Cartesian section fiber. -/
theorem nativeRetainedFamily_whole_endpoint (s : k) :
    (graphFunctor k).map (nativeAffineSection (.of k) U s) ≫
      ofFiniteFlatSpan F G (nativeRetainedFamily_base t q r L a c) =
      ofFiniteFlatSpan (pullback.fst (nativeAffineSection (.of k) U s).left F)
        (pullback.snd (nativeAffineSection (.of k) U s).left F ≫ G)
        (nativeRetainedEndpoint_base t q r L a c s) := by
  haveI : IsFinite (nativeRetainedFamilyPair t q r L a c ≫ pullback.fst _ _) := by
    simpa only [nativeRetainedFamilyPair_fst] using (inferInstance : IsFinite F)
  haveI : Flat (nativeRetainedFamilyPair t q r L a c ≫ pullback.fst _ _) := by
    simpa only [nativeRetainedFamilyPair_fst] using (inferInstance : Flat F)
  simpa only [nativeRetainedFamilyPair_fst, nativeRetainedFamilyPair_snd] using
    nativeSection_comp_ofFiniteFlatSpan_pair U W s (nativeRetainedFamilyPair t q r L a c)

/-- Literal zero specialization, retaining the whole original zero scheme and both legs. -/
theorem nativeRetainedFamily_zero :
    letI := nativeZeroSource_isFinite U (pullback.fst q r) L a c
    letI := nativeZeroSource_flat U (pullback.fst q r) L a c
    (graphFunctor k).map (nativeAffineSection (.of k) U 0) ≫
      ofFiniteFlatSpan F G (nativeRetainedFamily_base t q r L a c) =
      ofFiniteFlatSpan ((zeroScheme (pullback q r) L a).subschemeι ≫ pullback.fst q r)
        ((zeroScheme (pullback q r) L a).subschemeι ≫ pullback.snd q r)
        (retainedZero_base t q r L a) := by
  haveI := nativeZeroSource_isFinite U (pullback.fst q r) L a c
  haveI := nativeZeroSource_flat U (pullback.fst q r) L a c
  rw [nativeRetainedFamily_whole_endpoint]
  apply ofFiniteFlatSpan_eq_of_iso (nativeZeroFiberIso U (pullback.fst q r) L a c)
  · simpa only [Category.assoc] using nativeZeroFiberIso_hom_base U (pullback.fst q r) L a c
  · simpa only [Category.assoc, retainedFamilyTarget] using
      nativeZeroFiberIso_hom_original_assoc U (pullback.fst q r) L a c (pullback.snd q r)

/-- Literal one specialization, retaining the whole original zero scheme and both legs. -/
theorem nativeRetainedFamily_one :
    letI := nativeOneSource_isFinite U (pullback.fst q r) L a c
    letI := nativeOneSource_flat U (pullback.fst q r) L a c
    (graphFunctor k).map (nativeAffineSection (.of k) U 1) ≫
      ofFiniteFlatSpan F G (nativeRetainedFamily_base t q r L a c) =
      ofFiniteFlatSpan ((zeroScheme (pullback q r) L c).subschemeι ≫ pullback.fst q r)
        ((zeroScheme (pullback q r) L c).subschemeι ≫ pullback.snd q r)
        (retainedZero_base t q r L c) := by
  haveI := nativeOneSource_isFinite U (pullback.fst q r) L a c
  haveI := nativeOneSource_flat U (pullback.fst q r) L a c
  rw [nativeRetainedFamily_whole_endpoint]
  apply ofFiniteFlatSpan_eq_of_iso (nativeOneFiberIso U (pullback.fst q r) L a c)
  · simpa only [Category.assoc] using nativeOneFiberIso_hom_base U (pullback.fst q r) L a c
  · simpa only [Category.assoc, retainedFamilyTarget] using
      nativeOneFiberIso_hom_original_assoc U (pullback.fst q r) L a c (pullback.snd q r)

end AlgebraicGeometry.Cor
