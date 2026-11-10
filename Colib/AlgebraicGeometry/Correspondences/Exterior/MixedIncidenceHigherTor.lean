/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceRegularList

/-!
# Positive native Tor vanishes at actual mixed incidence points

The actual common original-middle family is regular after the literal original
ambient-to-support scalar map. Native regular-sequence Koszul exactness therefore
annihilates its positive support Koszul homology. The existing original-pair
Tor/Koszul isomorphism transfers this to the actual ambient Tor of the full
support and triple-product stalk modules.

No Tor equality, independent regular-list provider, or length-one hypothesis is
an input. This result holds at every actual incidence point. Degree zero and
length-one coefficients have their separate actual-module and geometry owners.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace RingTheory.Sequence
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Y U).hom
local notation3 (prettyPrint := false) "a" => nativeParameterGraphPoint X T U ψ t
local notation3 (prettyPrint := false) "b" => nativeExteriorPoint X Y U z hz

/-- All positive degrees of the actual original-pair Tor vanish for a native
graph component against a native exterior component. The parameter morphism
is arbitrary and is not assumed flat. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/GraphInterchangeStalks.lean:196-237"
  "adaptation" "Positive actual ambient Tor vanishing from the constructed common regular \
    list and native original-pair Koszul resolution, before coefficient-cycle assembly"]
theorem isZero_nativeMixedIncidenceAmbientTor_succ
    (x : nativeMixedGraphIncidence X Y T U ψ z hz t) (n : ℕ) :
    IsZero (correspondenceIncidenceAmbientTor f g h a b x (n + 1)) := by
  let p := correspondenceIncidenceAmbientInclusion f g h a b x
  let d := correspondenceIncidenceToSupportProduct f g h a b x
  let D := (correspondenceSupportProduct f g h a b).presheaf.stalk d
  let β := ((correspondenceMiddlePair f g h).stalkMap p).hom
  let ρ := correspondenceIncidenceSupportStalkMap f g h a b x
  obtain ⟨r, s, hs, hk, hD⟩ :=
    exists_nativeMixedIncidence_common_regular_list X Y T U ψ z hz t x
  have hkoszul : Koszul.IsKoszulRegularOn (fun i => ρ (β (s i))) D :=
    (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := D)).2.1 hD
  exact IsZero.of_iso
    ((ModuleCat.restrictScalars ρ).map_isZero (hkoszul (n + 1) (Nat.succ_ne_zero n)))
    (correspondenceIncidenceTorIsoOriginalSupportKoszul f g h a b x s hs hk (n + 1))

end Stacks.Chow
