/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceTorCoefficient
public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceMap

/-!
# The actual matched mixed contribution is the exterior support pushforward

The selected actual incidence is identified with the actual exterior prime
support. Its literal source-target morphism is the graph postcomposition map
under that isomorphism. Native finite pushforward functoriality therefore sends
the actual Tor cycle to the same degree-weighted cycle as right composition.
Only the intermediate isomorphism has degree one. The finite postcomposition
map retains its actual residue-field degrees without an extra hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Function.locallyFinsuppWithin

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom] [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Y U).hom
local notation3 (prettyPrint := false) "t" => nativeMixedMatchingComponent X Y T z hz
local notation3 (prettyPrint := false) "a" => nativeParameterGraphPoint X T U ψ t
local notation3 (prettyPrint := false) "b" => nativeExteriorPoint X Y U z hz

open Classical in
/-- The actual mixed contribution is the native finite pushforward of the exterior support prime.
The conclusion retains all residue degrees of the graph postcomposition map. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/\
    GraphInterchangeIncidence.lean:319-334"
  "adaptation" "Application of the literal mixed-incidence map comparison to the actual \
    native Tor cycle",
  stacks 02R5 "application: proper pushforward functoriality for the actual finite \
    support maps along the support isomorphism; no properness of the parameter morphism \
    is asserted"]
theorem nativeMixedMatchingIncidenceTor_val :
    (incidenceTorCorrespondence f g h a b
      (isFiniteCorrespondencePoint_graphMap f g (SmoothSite.productMap (𝟙 X) ψ).left
        (MorphismProperty.Over.w _) t)
      (nativeExteriorPoint_admissible X Y U z hz)).val =
      letI := isFinite_correspondenceGraphPostcompositionMap f (SmoothSite.product Y T).hom h
        (SmoothSite.productMap (𝟙 Y) ψ).left (MorphismProperty.Over.w _)
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint_admissible X Y T z hz)
      finiteCyclePushforward
        (correspondenceGraphPostcompositionMap f (SmoothSite.product Y T).hom h
          (SmoothSite.productMap (𝟙 Y) ψ).left (MorphismProperty.Over.w _)
          (nativeExteriorPoint X Y T z hz))
        (single (genericPoint (integralComponentAt (nativeExteriorPoint X Y T z hz)).subscheme)
          1) := by
  classical
  let ha : IsFiniteCorrespondencePoint f g a :=
    isFiniteCorrespondencePoint_graphMap f g (SmoothSite.productMap (𝟙 X) ψ).left
      (MorphismProperty.Over.w _) t
  let hb := nativeExteriorPoint_admissible X Y U z hz
  let W := nativeMixedGraphIncidence X Y T U ψ z hz t
  let E := (integralComponentAt (nativeExteriorPoint X Y T z hz)).subscheme
  let e := nativeMixedMatchingComponentIncidenceIso X Y T z hz U ψ
  let s := nativeExteriorSupportIso X Y T z hz
  let p : W ⟶ E := e.inv ≫ s.hom
  let q := correspondenceGraphPostcompositionMap f (SmoothSite.product Y T).hom h
    (SmoothSite.productMap (𝟙 Y) ψ).left (MorphismProperty.Over.w _)
    (nativeExteriorPoint X Y T z hz)
  let : IsIntegral W := isIntegral_nativeMixedMatchingIncidence X Y T U ψ z hz
  let : IsIso p := inferInstanceAs (IsIso (e.inv ≫ s.hom))
  let : IsFinite q := isFinite_correspondenceGraphPostcompositionMap f
    (SmoothSite.product Y T).hom h (SmoothSite.productMap (𝟙 Y) ψ).left
    (MorphismProperty.Over.w _) (nativeExteriorPoint X Y T z hz)
    (nativeExteriorPoint_admissible X Y T z hz)
  have hmap : correspondenceIncidenceMap f g h a b = p ≫ q := by
    apply (cancel_epi e.hom).mp
    change e.hom ≫ correspondenceIncidenceMap f g h a b = e.hom ≫ (e.inv ≫ s.hom) ≫ q
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, e, s, q,
      nativeMixedMatchingComponentIncidenceIso] using
      nativeMixedGraphIncidenceIso_hom_map X Y T U ψ z hz t
        (nativeMixedMatchingComponent_range_subset X Y T z hz U ψ)
  have hpush (r s : W ⟶ pullback (C := Scheme) f h)
      (hr : IsFinite r) (hs : IsFinite s) (hrs : r = s) :
      @finiteCyclePushforward W (pullback f h) r hr =
        @finiteCyclePushforward W (pullback f h) s hs := by
    cases hrs
    rfl
  rw [incidenceTorCorrespondence_val,
    nativeMixedMatchingIncidenceTorCycle_eq_single X Y T U ψ z hz,
    hpush _ _ (isFinite_correspondenceIncidenceMap f g h a b ha hb)
      (inferInstance : IsFinite (p ≫ q)) hmap,
    ← finiteCyclePushforward_comp_apply,
    finiteCyclePushforward_single_of_isClosedImmersion, genericPoint_eq_of_isOpenImmersion p]

end Stacks.Chow
