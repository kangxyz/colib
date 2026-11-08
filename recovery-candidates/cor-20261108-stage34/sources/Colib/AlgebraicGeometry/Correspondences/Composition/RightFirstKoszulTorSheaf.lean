/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightFirstTorSheaf
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageOriginalPairTor

/-!
# The exterior Tor sheaf realizes actual Z-first Koszul homology

The exterior sheaf is not just a family with the correct generic lengths. At
every exterior point its stalk is linearly isomorphic to the tensor extension
of the original pair Tor, with the actual incidence action. At an actual triple
incidence point the proved first-stage comparison identifies this same module
with the Z-first Koszul homology over the sixfold ambient, carrying its canonical
quotient-induced action of the full right-stage stalk.

Both comparisons retain nilpotents and every Tor degree. The original Z-stalk
list supplies the actual Z-first diagonal equations; no isomorphism, scalar
comparison, or coefficient equality is supplied by the caller. Flatness is
used only for the ambient/exterior maps already required by the first-stage
comparison, not for the finite intermediate-image morphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open AlgebraicGeometry.TorFormula
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

section ActualFirstStage

variable (x : correspondenceTripleIncidence f g h i z w v)
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

/-- The actual Z-first Koszul homology is the actual global exterior Tor-sheaf stalk,
linearly over the full right-stage local ring with its canonical quotient action. -/
def correspondenceTripleIncidenceRightFirstKoszulIsoTorSheaf
    {r : ℕ} (s : Fin r → R₀) (hs : IsRegular R₀ (List.ofFn s))
    (hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (s j)))
    let hreg := correspondenceOriginalLastPairList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) := by
  let l := List.ofFn (fun j => α (β (s j)))
  let hreg := correspondenceOriginalLastPairList_rightFirst_regular f g h i z w v x s hs hks
  letI := correspondenceTripleIncidenceRightFirstKoszulModule
    f g h i z w v x l hreg.1 hreg.2 n
  exact (correspondenceTripleIncidenceRightFirstKoszulIsoOriginalPairTor
    f g h i z w v x s hs hks n).trans
      (correspondenceRightExteriorTorSheafStalkIso f g h i z w v q n).toLinearEquiv.symm

/-- Raw lengths agree over the actual right-stage ring before taking integer multiplicities. -/
theorem length_correspondenceTripleIncidenceRightFirstKoszul_eq_torSheaf
    {r : ℕ} (s : Fin r → R₀) (hs : IsRegular R₀ (List.ofFn s))
    (hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (s j)))
    let hreg := correspondenceOriginalLastPairList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    Module.length P ((Koszul.seqComplexTensor l.get M).homology n) =
      Module.length P
        ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) :=
  (correspondenceTripleIncidenceRightFirstKoszulIsoTorSheaf f g h i z w v x s hs hks n).length_eq

end ActualFirstStage

end Stacks.Chow
