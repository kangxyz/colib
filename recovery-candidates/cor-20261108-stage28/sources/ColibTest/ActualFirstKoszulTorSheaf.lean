/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstTorSheaf

/-!
# Consumers of the actual first Koszul homology and exterior Tor-sheaf comparison

These examples instantiate the full comparison at an actual triple-incidence point.
They retain the canonical quotient-induced action of the full first-stage stalk,
the original diagonal regular list, and every homological degree. No comparison
or module action is supplied as a hypothesis. The raw-length and scalar-action
consumers supplement, rather than replace, the actual linear-equivalence consumer.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence Stacks.Chow
open AlgebraicGeometry.TorFormula
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceTripleIncidence f g h i z w v)
  [Flat f] [Flat h] [Flat i] [IsSeparated g]
  [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]

local notation3 (prettyPrint := false) "q" =>
  correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" =>
  correspondenceLeftExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "P" =>
  (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk q
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion f g h z w (π q)
local notation3 (prettyPrint := false) "R₀" =>
  (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h p₀)
local notation3 (prettyPrint := false) "β" =>
  ((correspondenceMiddlePair f g h).stalkMap p₀).hom
local notation3 (prettyPrint := false) "α" =>
  correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x

-- The actual canonical P-linear equivalence, not just a signature check or length equality.
example {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x t ht hkt
    letI := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      ((correspondenceLeftExteriorTorSheaf f g h i z w v n).presheaf.stalk q) :=
  correspondenceTripleIncidenceFirstKoszulIsoTorSheaf f g h i z w v x t ht hkt n

-- Both sides use the full first-stage ring and raw extended lengths, before conversion to ℤ.
example {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x t ht hkt
    letI := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    Module.length P ((Koszul.seqComplexTensor l.get M).homology n) =
      Module.length P
        ((correspondenceLeftExteriorTorSheaf f g h i z w v n).presheaf.stalk q) :=
  length_correspondenceTripleIncidenceFirstKoszul_eq_torSheaf f g h i z w v x t ht hkt n

-- A literal P-scalar acts through the same quotient-induced module on homology.
example {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x t ht hkt
    letI := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    let e := correspondenceTripleIncidenceFirstKoszulIsoTorSheaf
      f g h i z w v x t ht hkt n
    ∀ (a : P) (m : (Koszul.seqComplexTensor l.get M).homology n),
      e (a • m) = a • e m :=
  fun a m =>
    (correspondenceTripleIncidenceFirstKoszulIsoTorSheaf
      f g h i z w v x t ht hkt n).map_smul a m
