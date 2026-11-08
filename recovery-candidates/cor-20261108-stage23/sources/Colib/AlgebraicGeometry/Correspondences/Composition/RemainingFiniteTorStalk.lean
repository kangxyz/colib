/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorModule
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedAffineSystem
import all StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle

/-!
# Localizations of the actual full finite Tor coefficient

The module of global sections is localized at the literal affine prime of a
model point. Native affine germ localization identifies its length with the
sheaf stalk length. The localization projection is an isomorphism on local
rings, so it contributes fibre length one. The actual exterior projection still
contributes its full closed-fibre length.

The final equality is in extended natural numbers before any truncation. Thus
it can prove actual module vanishing, rather than only vanishing of an integer
multiplicity. The original pair Tor degree and scalar maps are unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The localization projection preserves the raw sheaf-stalk length: its local ring map
is an isomorphism. This does not assert length preservation for the exterior projection. -/
theorem length_correspondenceRemainingFiniteTorSheaf_stalk
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) (n : ℕ) :
    Module.length ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
        ((correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) =
      Module.length ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q))
        ((correspondenceLeftExteriorTorSheaf f g h i z w v n).presheaf.stalk
          (correspondenceRemainingFiniteModelProjection f g h i z w v x q)) := by
  let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
  let := flat_correspondenceRemainingFiniteModelProjection f g h i z w v x
  let := isIso_correspondenceRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  have hlen := length_stalk_pullback_eq_mul ρ
    (correspondenceLeftExteriorTorSheaf f g h i z w v n) q
  change Module.length _ _ = Module.length _ _ *
    Module.length ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
      (((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q) ⧸
        Ideal.map (ρ.stalkMap q).hom
          (IsLocalRing.maximalIdeal
            ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
              (ρ q)))) at hlen
  rw [IsLocalRing.map_maximalIdeal_of_surjective (ρ.stalkMap q).hom
    (ConcreteCategory.bijective_of_isIso _).surjective, Module.length_eq_one, mul_one] at hlen
  exact hlen

/-- The raw exterior stalk length is original Tor length times the full exterior fibre length. -/
theorem length_correspondenceLeftExteriorTorSheaf_stalk [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (q : correspondenceLeftIntermediateSupportProduct f g h i z w v) (n : ℕ) :
    Module.length ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk q)
        ((correspondenceLeftExteriorTorSheaf f g h i z w v n).presheaf.stalk q) =
      Module.length (correspondenceIncidenceAmbientStalk f g h z w
          (correspondenceLeftExteriorProjection f g h i z w v q))
        (correspondenceIncidenceAmbientTor f g h z w
          (correspondenceLeftExteriorProjection f g h i z w v q) n) *
      Module.length ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk q)
        (((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk q) ⧸
          Ideal.map ((correspondenceLeftExteriorProjection f g h i z w v).stalkMap q).hom
            (IsLocalRing.maximalIdeal ((correspondenceIncidence f g h z w).presheaf.stalk
              (correspondenceLeftExteriorProjection f g h i z w v q)))) := by
  have hlen := length_stalk_pullback_eq_mul
    (correspondenceLeftExteriorProjection f g h i z w v)
    (correspondencePairTorSheaf f g h z w n) q
  change Module.length _ _ = Module.length _ _ * _ at hlen
  rw [length_correspondencePairTorSheaf_stalk] at hlen
  exact hlen

/-- Native affine localization identifies the actual full finite module with its actual stalk
at the level of raw lengths. The affine prime is fixed by the section-germ map. -/
theorem length_localized_correspondenceRemainingFiniteTorModule [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) (n : ℕ) :
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top
      (correspondenceRemainingFiniteModel f g h i z w v x)).primeIdealOf ⟨q, trivial⟩
    Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl
          (correspondenceRemainingFiniteTorModule f g h i z w v x n)) =
      Module.length ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
        ((correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) := by
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  let := (isQuasicoherent_isFiniteType_correspondenceRemainingFiniteTorSheaf
    f g h i z w v x n).1
  exact (Stacks.ModuleStalkSpecialization.length_stalk_eq_length_localizedModule
    (correspondenceRemainingFiniteTorSheaf f g h i z w v x n)
    (isAffineOpen_top _) (show q ∈ (⊤ : (correspondenceRemainingFiniteModel
      f g h i z w v x).Opens) from trivial)).symm

end Stacks.Chow
