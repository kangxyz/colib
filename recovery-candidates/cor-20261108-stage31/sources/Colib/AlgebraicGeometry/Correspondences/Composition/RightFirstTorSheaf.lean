/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImage
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorSheaf
public import Mathlib.RingTheory.LocalRing.Length

/-!
# The actual last-pair Tor family on the full right exterior

Pull the actual incidence Tor sheaf of the last two supports to the full right
exterior. Its incidence quotient action is established before this pullback by
the existing PairTorSheaf supplier. The stalk comparison is linear over the
actual full exterior stalk, in every Tor degree, without a flatness hypothesis.

When the first support is flat over the base, native flat-local length retains
the complete closed-fibre factor as an extended length. This hypothesis is
automatic over any field and is not flatness of the first support over Y.
No finiteness or value one is asserted for this factor at arbitrary points.

This is the genuine right exterior family, not yet its comparison with the
first Koszul homology for imposing the Z diagonal first in the common sixfold
ambient. That scalar/permutation comparison and the global weighted remaining
cycle identity remain separate obligations. The source target is
motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean;
no theorem of that weighted comparison is assumed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.TorFormula
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- Every actual last-pair Tor sheaf is pulled to the whole right exterior. -/
abbrev correspondenceRightExteriorTorSheaf (n : ℕ) :
    (correspondenceRightIntermediateSupportProduct f g h i z w v).Modules :=
  (Scheme.Modules.pullback (correspondenceRightExteriorProjection f g h i z w v)).obj
    (correspondencePairTorSheaf g h i w v n)

/-- The canonical original incidence action survives ordinary exterior pullback. -/
def correspondenceRightExteriorTorSheafStalkIso [IsSeparated h]
    (q : correspondenceRightIntermediateSupportProduct f g h i z w v) (n : ℕ) :
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
    letI := correspondenceIncidenceTorModule g h i w v (π q) n
    letI : Algebra P₀ P := (π.stalkMap q).hom.toAlgebra
    stalkModuleCat (correspondenceRightIntermediateSupportProduct f g h i z w v)
        (correspondenceRightExteriorTorSheaf f g h i z w v n) q ≅
      ModuleCat.of P (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n) := by
  let π := correspondenceRightExteriorProjection f g h i z w v
  let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
  let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
  letI := correspondenceIncidenceTorModule g h i w v (π q) n
  letI : Algebra P₀ P := (π.stalkMap q).hom.toAlgebra
  obtain ⟨ePB, _⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    π.toLRSHom.toShHom (correspondencePairTorSheaf g h i w v n) q
  exact ePB.toModuleIso ≪≫
    (ModuleCat.extendScalars (π.stalkMap q).hom).mapIso
      (correspondencePairTorSheafStalkIso g h i w v (π q) n)

/-- Quasi-coherence and finite type come from the actual last-pair Tor sheaf. -/
theorem isQuasicoherent_isFiniteType_correspondenceRightExteriorTorSheaf [IsSeparated h]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)] (n : ℕ) :
    (correspondenceRightExteriorTorSheaf f g h i z w v n).IsQuasicoherent ∧
      (correspondenceRightExteriorTorSheaf f g h i z w v n).IsFiniteType := by
  obtain ⟨hqc, hft⟩ := isQuasicoherent_isFiniteType_correspondencePairTorSheaf g h i w v n
  let := hft
  exact ⟨Stacks.Modules.isQuasicoherent_pullback
      (correspondenceRightExteriorProjection f g h i z w v) _ hqc,
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      (correspondenceRightExteriorProjection f g h i z w v).toLRSHom.toShHom _⟩

/-- Flatness is only over the original base, never over the remaining middle scheme. -/
instance flat_correspondenceRightExteriorProjection
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)] :
    Flat (correspondenceRightExteriorProjection f g h i z w v) := by
  dsimp only [correspondenceRightExteriorProjection]
  infer_instance

/-- The actual exterior Tor length retains the full closed-fibre multiplicity.
This equality is in extended naturals, so no infinite length is truncated. -/
theorem length_correspondenceRightExteriorTorSheaf_eq_mul [IsSeparated h]
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (q : correspondenceRightIntermediateSupportProduct f g h i z w v) (n : ℕ) :
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
    letI := correspondenceIncidenceTorModule g h i w v (π q) n
    Module.length P ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) =
      Module.length P₀ (correspondenceIncidenceAmbientTor g h i w v (π q) n) *
        Module.length P (P ⧸ (IsLocalRing.maximalIdeal P₀).map (π.stalkMap q).hom) := by
  let π := correspondenceRightExteriorProjection f g h i z w v
  let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
  let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
  letI := correspondenceIncidenceTorModule g h i w v (π q) n
  letI : Algebra P₀ P := (π.stalkMap q).hom.toAlgebra
  letI : IsLocalHom (algebraMap P₀ P) :=
    LocallyRingedSpace.isLocalHomStalkMap π.toLRSHom q
  letI : Module.Flat P₀ P := Flat.stalkMap π q
  exact
    (correspondenceRightExteriorTorSheafStalkIso f g h i z w v q n).toLinearEquiv.length_eq.trans
    (IsLocalRing.length_baseChange P₀ P (correspondenceIncidenceAmbientTor g h i w v (π q) n))

end Stacks.Chow
