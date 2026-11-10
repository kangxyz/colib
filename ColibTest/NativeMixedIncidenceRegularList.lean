/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceRegularList

/-! # Direct consumer of the literal original-middle/support common family -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace RingTheory.Sequence
open AlgebraicGeometry.Scheme Stacks.Chow

universe u

variable {k : Type u} [Field k] (X Y T U : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral U.hom] (ψ : T ⟶ U)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (t : genericPoints (SmoothSite.product X T).left)
  (x : nativeMixedGraphIncidence X Y T U ψ z hz t)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product X U).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Y U).hom
local notation3 (prettyPrint := false) "a" => nativeParameterGraphPoint X T U ψ t
local notation3 (prettyPrint := false) "b" => nativeExteriorPoint X Y U z hz
local notation3 (prettyPrint := false) "p" => correspondenceIncidenceAmbientInclusion f g h a b x
local notation3 (prettyPrint := false) "d" => correspondenceIncidenceToSupportProduct f g h a b x
local notation3 (prettyPrint := false) "R" => (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h p)
local notation3 (prettyPrint := false) "D" => (correspondenceSupportProduct f g h a b).presheaf.stalk d
local notation3 (prettyPrint := false) "β" => ((correspondenceMiddlePair f g h).stalkMap p).hom
local notation3 (prettyPrint := false) "ρ" => correspondenceIncidenceSupportStalkMap f g h a b x

example : ∃ (r : ℕ) (s : Fin r → R), IsRegular R (List.ofFn s) ∧
    IdealSheafData.stalk (pullback.diagonal g).ker (correspondenceMiddlePair f g h p) =
      Ideal.span (Set.range s) ∧
    IsRegular D (List.ofFn (fun i => ρ (β (s i)))) :=
  exists_nativeMixedIncidence_common_regular_list X Y T U ψ z hz t x
