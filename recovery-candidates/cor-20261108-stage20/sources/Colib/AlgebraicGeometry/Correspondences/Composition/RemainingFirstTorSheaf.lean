/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorModule
public import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStageOriginalPairTor

/-!
# The exterior Tor sheaf realizes actual first Koszul homology

The exterior sheaf is not just a family with the correct generic lengths. At
every exterior point its stalk is linearly isomorphic to the tensor extension
of the original pair Tor, with the actual incidence action. At an actual triple
incidence point the proved first-stage comparison identifies this same module
with the first Koszul homology over the sixfold ambient, carrying its canonical
quotient-induced action of the full first-stage stalk.

Both comparisons retain nilpotents and every Tor degree. The original Y-stalk
list supplies the actual first diagonal equations; no isomorphism, scalar
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

/-- The actual exterior sheaf stalk is the tensor pullback of the original pair Tor with
its canonical incidence action. This stalk comparison itself needs no flatness assumption. -/
def correspondenceLeftExteriorTorSheafStalkIso [IsSeparated g]
    (q : correspondenceLeftIntermediateSupportProduct f g h i z w v) (n : ℕ) :
    let π := correspondenceLeftExteriorProjection f g h i z w v
    let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence f g h z w).presheaf.stalk (π q)
    letI := correspondenceIncidenceTorModule f g h z w (π q) n
    letI : Algebra P₀ P := (π.stalkMap q).hom.toAlgebra
    stalkModuleCat (correspondenceLeftIntermediateSupportProduct f g h i z w v)
        (correspondenceLeftExteriorTorSheaf f g h i z w v n) q ≅
      ModuleCat.of P (P ⊗[P₀] correspondenceIncidenceAmbientTor f g h z w (π q) n) := by
  let π := correspondenceLeftExteriorProjection f g h i z w v
  let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk q
  let P₀ := (correspondenceIncidence f g h z w).presheaf.stalk (π q)
  letI := correspondenceIncidenceTorModule f g h z w (π q) n
  letI : Algebra P₀ P := (π.stalkMap q).hom.toAlgebra
  obtain ⟨ePB, _⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    π.toLRSHom.toShHom (correspondencePairTorSheaf f g h z w n) q
  exact ePB.toModuleIso ≪≫
    (ModuleCat.extendScalars (π.stalkMap q).hom).mapIso
      (correspondencePairTorSheafStalkIso f g h z w (π q) n)

section ActualFirstStage

variable (x : correspondenceTripleIncidence f g h i z w v)
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

/-- The actual first Koszul homology is the actual global exterior Tor-sheaf stalk,
linearly over the full first-stage local ring with its canonical quotient action. -/
def correspondenceTripleIncidenceFirstKoszulIsoTorSheaf
    {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x t ht hkt
    letI := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      ((correspondenceLeftExteriorTorSheaf f g h i z w v n).presheaf.stalk q) := by
  let l := List.ofFn (fun j => α (β (t j)))
  let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x t ht hkt
  letI := correspondenceTripleIncidenceFirstKoszulModule
    f g h i z w v x l hreg.1 hreg.2 n
  exact (correspondenceTripleIncidenceFirstKoszulIsoOriginalPairTor
    f g h i z w v x t ht hkt n).trans
      (correspondenceLeftExteriorTorSheafStalkIso f g h i z w v q n).toLinearEquiv.symm

/-- Raw lengths agree over the actual first-stage ring before taking integer multiplicities. -/
theorem length_correspondenceTripleIncidenceFirstKoszul_eq_torSheaf
    {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x t ht hkt
    letI := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    Module.length P ((Koszul.seqComplexTensor l.get M).homology n) =
      Module.length P
        ((correspondenceLeftExteriorTorSheaf f g h i z w v n).presheaf.stalk q) :=
  (correspondenceTripleIncidenceFirstKoszulIsoTorSheaf f g h i z w v x t ht hkt n).length_eq

end ActualFirstStage

end Stacks.Chow
