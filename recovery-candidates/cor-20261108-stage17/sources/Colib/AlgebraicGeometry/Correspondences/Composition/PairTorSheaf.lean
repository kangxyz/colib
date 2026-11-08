/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorAction
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsAlongSurjection

/-!
# The original pair Tor family on the whole incidence scheme

The native ambient Tor sheaf is pulled back to the full original incidence.
At every incidence point its stalk is the original ambient Tor module with the
canonical quotient-induced incidence action. The comparison uses native Tor
stalk comparison (Stacks 0AZT), the actual closed-immersion structure stalks,
and the counit for extension/restriction along the surjective incidence stalk map.
It does not assume a descent isomorphism or replace the Tor module by a quotient ring.

Coherence of ambient Tor uses Stacks 0AZS on the actual locally Noetherian
ambient. Quasi-coherence and finite type survive the actual incidence pullback
by Stacks 01BG and 01B6. No regular list, field perfection, reduction, or
flatness of the incidence inclusion is required.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.TorFormula

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

private def torSheafStalkCommRingIso (T : Scheme.{u}) (F G : T.Modules) (n : ℕ) (x : T) :
    stalkModuleCat T (torSheaf T F G n) x ≅
      ((Tor (ModuleCat (T.presheaf.stalk x)) n).obj (stalkModuleCat T F x)).obj
        (stalkModuleCat T G x) := by
  let _ := StacksDraft.StalkTensor.commRing_stalk_ringSheaf T.sheaf x
  let e := (stalkRingEquiv T x).symm
  let Q := ModuleCat.restrictScalars e.toRingHom
  exact (stalkRestrictIso T (torSheaf T F G n) x).symm ≪≫
    Q.mapIso (torSheafStalkIso T F G n x) ≪≫
    (RingTheory.TorIndependence.torRestrictIso e
      ((Scheme.Modules.stalkFunctor T x).obj F)
      ((Scheme.Modules.stalkFunctor T x).obj G) n).symm ≪≫
    (((Tor (ModuleCat (T.presheaf.stalk x)) n).mapIso (stalkRestrictIso T F x)).app
      (Q.obj ((Scheme.Modules.stalkFunctor T x).obj G))) ≪≫
    ((Tor (ModuleCat (T.presheaf.stalk x)) n).obj (stalkModuleCat T F x)).mapIso
      (stalkRestrictIso T G x)

private def pushforwardUnitStalkIsoAt {T U : Scheme.{u}} (j : U ⟶ T)
    [IsClosedImmersion j] (q : U) (x : T) (hx : x = j q) :
    stalkModuleCat T
        ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit U.ringCatSheaf)) x ≅
      (ModuleCat.restrictScalars
        (((T.presheaf.stalkCongr (Inseparable.of_eq hx)).hom ≫ j.stalkMap q).hom)).obj
          (ModuleCat.of (U.presheaf.stalk q) (U.presheaf.stalk q)) := by
  subst x
  simpa [TopCat.Presheaf.stalkCongr] using
    (stalkPushforwardStructureSheafLinearEquiv j q
      (IsClosedImmersion.isClosedEmbedding j).isInducing).toModuleIso

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The full original support structure module on the four-factor ambient. -/
abbrev correspondencePairSupportSheaf : (correspondenceIntersectionAmbient f g h).Modules :=
  (Scheme.Modules.pushforward (correspondenceSupportProductInclusion f g h z w)).obj
    (SheafOfModules.unit (correspondenceSupportProduct f g h z w).ringCatSheaf)

/-- The original middle diagonal structure module on the same ambient. -/
abbrev correspondencePairDiagonalSheaf : (correspondenceIntersectionAmbient f g h).Modules :=
  (Scheme.Modules.pushforward (correspondenceTripleInclusion f g h)).obj
    (SheafOfModules.unit (correspondenceTripleProduct f g h).ringCatSheaf)

/-- Every original Tor degree is retained as its native ambient Tor sheaf. -/
abbrev correspondencePairAmbientTorSheaf (n : ℕ) :
    (correspondenceIntersectionAmbient f g h).Modules :=
  torSheaf (correspondenceIntersectionAmbient f g h)
    (correspondencePairSupportSheaf f g h z w) (correspondencePairDiagonalSheaf f g h) n

/-- The original Tor family on the full incidence, with its scheme-theoretic action. -/
abbrev correspondencePairTorSheaf (n : ℕ) : (correspondenceIncidence f g h z w).Modules :=
  (Scheme.Modules.pullback (correspondenceIncidenceAmbientInclusion f g h z w)).obj
    (correspondencePairAmbientTorSheaf f g h z w n)

/-- Coherence uses the actual ambient, not a reduced or integral replacement. -/
theorem isCoherent_correspondencePairAmbientTorSheaf [IsSeparated g]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)] (n : ℕ) :
    (correspondencePairAmbientTorSheaf f g h z w n).IsCoherent :=
  isCoherent_torSheaf _ _ _
    (ClosedImmersionCoherentImage.isCoherent_pushforward_unit
      (correspondenceSupportProductInclusion f g h z w))
    (ClosedImmersionCoherentImage.isCoherent_pushforward_unit
      (correspondenceTripleInclusion f g h)) n

/-- Both finiteness properties descend to the actual incidence by ordinary pullback. -/
theorem isQuasicoherent_isFiniteType_correspondencePairTorSheaf [IsSeparated g]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)] (n : ℕ) :
    (correspondencePairTorSheaf f g h z w n).IsQuasicoherent ∧
      (correspondencePairTorSheaf f g h z w n).IsFiniteType := by
  let F := correspondencePairAmbientTorSheaf f g h z w n
  let : F.IsCoherent := isCoherent_correspondencePairAmbientTorSheaf f g h z w n
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  let := hft
  exact ⟨Stacks.Modules.isQuasicoherent_pullback
      (correspondenceIncidenceAmbientInclusion f g h z w) F hqc,
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      (correspondenceIncidenceAmbientInclusion f g h z w).toLRSHom.toShHom F⟩

/-- Native Tor stalk comparison has the literal original two structure-ring modules. -/
def correspondencePairAmbientTorSheafStalkIso [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    stalkModuleCat (correspondenceIntersectionAmbient f g h)
        (correspondencePairAmbientTorSheaf f g h z w n)
        (correspondenceIncidenceAmbientInclusion f g h z w x) ≅
      correspondenceIncidenceAmbientTor f g h z w x n := by
  let e₁ := pushforwardUnitStalkIsoAt (correspondenceSupportProductInclusion f g h z w)
    (correspondenceIncidenceToSupportProduct f g h z w x)
    (correspondenceIncidenceAmbientInclusion f g h z w x)
    (correspondenceIncidence_ambient_point_eq f g h z w x)
  let e₂ := LinearEquiv.toModuleIso (stalkPushforwardStructureSheafLinearEquiv (correspondenceTripleInclusion f g h)
    (correspondenceIncidenceInclusion f g h z w x)
    (IsClosedImmersion.isClosedEmbedding (correspondenceTripleInclusion f g h)).isInducing)
  exact torSheafStalkCommRingIso _ _ _ n _ ≪≫
    (((Tor (ModuleCat (correspondenceIncidenceAmbientStalk f g h z w x)) n).mapIso e₁).app
      (stalkModuleCat _ (correspondencePairDiagonalSheaf f g h) _)) ≪≫
    ((Tor (ModuleCat (correspondenceIncidenceAmbientStalk f g h z w x)) n).obj
      (correspondenceIncidenceSupportStalkModule f g h z w x)).mapIso e₂

/-- The actual incidence kernel annihilates the ambient Tor sheaf stalk before pullback.
This records the scheme-theoretic, rather than merely set-theoretic, descent condition. -/
theorem correspondencePairAmbientTorSheafStalk_ker_le_annihilator [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    RingHom.ker ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom ≤
      Module.annihilator (correspondenceIncidenceAmbientStalk f g h z w x)
        ((correspondencePairAmbientTorSheaf f g h z w n).presheaf.stalk
          (correspondenceIncidenceAmbientInclusion f g h z w x)) := by
  intro a ha
  apply mem_annihilator_of_moduleCat_iso
    (correspondencePairAmbientTorSheafStalkIso f g h z w x n).symm
  exact correspondenceIncidence_ker_le_annihilator_tor f g h z w x n ha

/-- The incidence stalk of the sheaf is the original Tor with its canonical incidence action.
No caller-supplied scalar or descent comparison is used. -/
def correspondencePairTorSheafStalkIso [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    letI := correspondenceIncidenceTorModule f g h z w x n
    stalkModuleCat (correspondenceIncidence f g h z w)
        (correspondencePairTorSheaf f g h z w n) x ≅
      ModuleCat.of ((correspondenceIncidence f g h z w).presheaf.stalk x)
        (correspondenceIncidenceAmbientTor f g h z w x n) := by
  let ι := correspondenceIncidenceAmbientInclusion f g h z w
  let κ := (ι.stalkMap x).hom
  let A := correspondenceIncidenceAmbientStalk f g h z w x
  let P := (correspondenceIncidence f g h z w).presheaf.stalk x
  letI := correspondenceIncidenceTorModule f g h z w x n
  let N : ModuleCat P := ModuleCat.of P (correspondenceIncidenceAmbientTor f g h z w x n)
  let e : correspondenceIncidenceAmbientTor f g h z w x n ≃ₗ[A]
      (ModuleCat.restrictScalars κ).obj N :=
    { toAddEquiv := AddEquiv.refl _
      map_smul' := fun a m =>
        (correspondenceIncidenceTorModule_stalkMap_smul f g h z w x n a m).symm }
  let := Stacks.ModuleCat.isIso_extendRestrictScalarsAdj_counit_app κ
    (SurjectiveOnStalks.stalkMap_surjective ι x) N
  let := κ.toAlgebra
  obtain ⟨ePB, _⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    ι.toLRSHom.toShHom (correspondencePairAmbientTorSheaf f g h z w n) x
  exact ePB.toModuleIso ≪≫
    (ModuleCat.extendScalars κ).mapIso
      (correspondencePairAmbientTorSheafStalkIso f g h z w x n ≪≫ e.toModuleIso) ≪≫
    asIso ((ModuleCat.extendRestrictScalarsAdj κ).counit.app N)

/-- In particular, the global sheaf preserves the original ambient Tor lengths in every degree. -/
theorem length_correspondencePairTorSheaf_stalk [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x)
        ((correspondencePairTorSheaf f g h z w n).presheaf.stalk x) =
      Module.length (correspondenceIncidenceAmbientStalk f g h z w x)
        (correspondenceIncidenceAmbientTor f g h z w x n) := by
  letI := correspondenceIncidenceTorModule f g h z w x n
  exact (correspondencePairTorSheafStalkIso f g h z w x n).toLinearEquiv.length_eq.trans
    (correspondenceIncidenceTor_length_eq_incidence f g h z w x n).symm

end Stacks.Chow
