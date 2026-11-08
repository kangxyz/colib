/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RightFirstKoszulTorSheaf

/-!
# Consumers of the actual Z-first Koszul homology and exterior Tor-sheaf comparison

These examples instantiate the full comparison at an actual triple-incidence point.
They retain the canonical quotient-induced action of the full right-stage stalk,
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
  [Flat f] [Flat g] [Flat i] [IsSeparated h]
  [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]

local notation3 (prettyPrint := false) "q" =>
  correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" =>
  correspondenceRightExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "P" =>
  (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion g h i w v (π q)
local notation3 (prettyPrint := false) "R₀" =>
  (pullback h h).presheaf.stalk (correspondenceMiddlePair g h i p₀)
local notation3 (prettyPrint := false) "β" =>
  ((correspondenceMiddlePair g h i).stalkMap p₀).hom
local notation3 (prettyPrint := false) "α" =>
  correspondenceTripleIncidenceRightPairAmbientStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x

-- The actual canonical P-linear equivalence, not just a signature check or length equality.
example {r : ℕ} (s : Fin r → R₀) (hs : IsRegular R₀ (List.ofFn s))
    (hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (s j)))
    let hreg := correspondenceOriginalLastPairList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) :=
  correspondenceTripleIncidenceRightFirstKoszulIsoTorSheaf f g h i z w v x s hs hks n

-- Both sides use the full right-stage ring and raw extended lengths, before conversion to ℤ.
example {r : ℕ} (s : Fin r → R₀) (hs : IsRegular R₀ (List.ofFn s))
    (hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (s j)))
    let hreg := correspondenceOriginalLastPairList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    Module.length P ((Koszul.seqComplexTensor l.get M).homology n) =
      Module.length P
        ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) :=
  length_correspondenceTripleIncidenceRightFirstKoszul_eq_torSheaf f g h i z w v x s hs hks n

-- A literal P-scalar acts through the same quotient-induced module on homology.
example {r : ℕ} (s : Fin r → R₀) (hs : IsRegular R₀ (List.ofFn s))
    (hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (s j)))
    let hreg := correspondenceOriginalLastPairList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    let e := correspondenceTripleIncidenceRightFirstKoszulIsoTorSheaf
      f g h i z w v x s hs hks n
    ∀ (a : P) (m : (Koszul.seqComplexTensor l.get M).homology n),
      e (a • m) = a • e m :=
  fun a m =>
    (correspondenceTripleIncidenceRightFirstKoszulIsoTorSheaf
      f g h i z w v x s hs hks n).map_smul a m
