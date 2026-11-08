/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorModule
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedAffineSystem
import all StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle

/-!
# Localizations of the actual full right finite Tor coefficient

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
theorem length_correspondenceRightRemainingFiniteTorSheaf_stalk
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) (n : ℕ) :
    Module.length ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
        ((correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) =
      Module.length ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q))
        ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk
          (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q)) := by
  let ρ := correspondenceRightRemainingFiniteModelProjection f g h i z w v x
  let := flat_correspondenceRightRemainingFiniteModelProjection f g h i z w v x
  let := isIso_correspondenceRightRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  have hlen := length_stalk_pullback_eq_mul ρ
    (correspondenceRightExteriorTorSheaf f g h i z w v n) q
  change Module.length _ _ = Module.length _ _ *
    Module.length ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
      (((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q) ⧸
        Ideal.map (ρ.stalkMap q).hom
          (IsLocalRing.maximalIdeal
            ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
              (ρ q)))) at hlen
  rw [IsLocalRing.map_maximalIdeal_of_surjective (ρ.stalkMap q).hom
    (ConcreteCategory.bijective_of_isIso _).surjective, Module.length_eq_one, mul_one] at hlen
  exact hlen

/-- The raw exterior stalk length is original Tor length times the full exterior fibre length. -/
theorem length_correspondenceRightExteriorTorSheaf_stalk [IsSeparated h]
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (q : correspondenceRightIntermediateSupportProduct f g h i z w v) (n : ℕ) :
    Module.length ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q)
        ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) =
      Module.length (correspondenceIncidenceAmbientStalk g h i w v
          (correspondenceRightExteriorProjection f g h i z w v q))
        (correspondenceIncidenceAmbientTor g h i w v
          (correspondenceRightExteriorProjection f g h i z w v q) n) *
      Module.length ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q)
        (((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q) ⧸
          Ideal.map ((correspondenceRightExteriorProjection f g h i z w v).stalkMap q).hom
            (IsLocalRing.maximalIdeal ((correspondenceIncidence g h i w v).presheaf.stalk
              (correspondenceRightExteriorProjection f g h i z w v q)))) := by
  have hlen := length_stalk_pullback_eq_mul
    (correspondenceRightExteriorProjection f g h i z w v)
    (correspondencePairTorSheaf g h i w v n) q
  change Module.length _ _ = Module.length _ _ * _ at hlen
  rw [length_correspondencePairTorSheaf_stalk] at hlen
  exact hlen

/-- Native affine localization identifies the actual full finite module with its actual stalk
at the level of raw lengths. The affine prime is fixed by the section-germ map. -/
theorem length_localized_correspondenceRightRemainingFiniteTorModule [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) (n : ℕ) :
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top
      (correspondenceRightRemainingFiniteModel f g h i z w v x)).primeIdealOf ⟨q, trivial⟩
    Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl
          (correspondenceRightRemainingFiniteTorModule f g h i z w v x n)) =
      Module.length ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
        ((correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) := by
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  let := (isQuasicoherent_isFiniteType_correspondenceRightRemainingFiniteTorSheaf
    f g h i z w v x n).1
  exact (Stacks.ModuleStalkSpecialization.length_stalk_eq_length_localizedModule
    (correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n)
    (isAffineOpen_top _) (show q ∈ (⊤ : (correspondenceRightRemainingFiniteModel
      f g h i z w v x).Opens) from trivial)).symm

end Stacks.Chow
