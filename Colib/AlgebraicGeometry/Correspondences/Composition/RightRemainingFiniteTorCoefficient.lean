/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteGenericLabels
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingExteriorMultiplicity

/-!
# The actual generic coefficient of the whole finite Tor family

At each generic point of the full finite model, the affine minimal prime is
literally the section-germ prime. Native localization and the isomorphism on
local rings of the localization projection identify the length of every
canonical coefficient module with the exterior sheaf multiplicity. Applying
native flat-local multiplicity degree by degree gives the original pair Tor
length multiplied by the full exterior fibre length.

Taking the integer alternating sum retains all higher Tor degrees and gives
the original pair Tor coefficient times that same fibre length. The original
pair generic label is the actual projection of the original exterior label.
Neither split labels nor nilpotents are discarded, and the fibre length is not
replaced by one over an arbitrary field. No coefficient comparison is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

section GeneralBase

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The selected minimal prime is literally the native affine prime of the same point. -/
theorem correspondenceRightRemainingFiniteGenericEquivMinPrime_eq_primeIdealOf [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x)) :
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    (correspondenceRightRemainingFiniteGenericEquivMinPrime f g h i z w v hw hv x q).1 =
      (isAffineOpen_top
        (correspondenceRightRemainingFiniteModel f g h i z w v x)).primeIdealOf ⟨q.1, trivial⟩ := by
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  apply PrimeSpectrum.ext
  rw [correspondenceRightRemainingFiniteGenericEquivMinPrime_asIdeal,
    IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  rfl

/-- Each actual localized Tor degree has the original pair multiplicity times the full
exterior fibre multiplicity. The finite map is not required to be flat. -/
theorem natCast_length_localized_correspondenceRightRemainingFiniteTorModule
    [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x)) (n : ℕ) :
    let p := (correspondenceRightRemainingFiniteGenericEquivMinPrime
      f g h i z w v hw hv x q).1
    ((Module.length (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl
        (correspondenceRightRemainingFiniteTorModule f g h i z w v x n))).toNat : ℤ) =
      ((Module.length
        (correspondenceIncidenceAmbientStalk g h i w v
          (correspondenceRightExteriorProjection f g h i z w v
            (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1)))
        (correspondenceIncidenceAmbientTor g h i w v
          (correspondenceRightExteriorProjection f g h i z w v
            (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1)) n)).toNat :
              ℤ) *
          (correspondenceRightExteriorFiberLength f g h i z w v
            (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1) : ℤ) := by
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  dsimp only
  rw [correspondenceRightRemainingFiniteGenericEquivMinPrime_eq_primeIdealOf
      f g h i z w v hw hv x q,
    length_localized_correspondenceRightRemainingFiniteTorModule f g h i z w v hw hv x q.1 n,
    length_correspondenceRightRemainingFiniteTorSheaf_stalk f g h i z w v x q.1 n]
  rw [length_correspondenceRightExteriorTorSheaf_stalk f g h i z w v _ n]
  simp only [ENat.toNat_mul, Nat.cast_mul, correspondenceRightExteriorFiberLength]

end GeneralBase

section Field

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth g] [Smooth h] [Smooth i] [IsSeparated h] [IsSeparated i]
  (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)

/-- The signed generic coefficient of the actual whole finite module family is the original
pair Tor coefficient times the full exterior fibre length. All original degrees remain. -/
theorem finsum_signed_length_localized_correspondenceRightRemainingFiniteTorModule
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x)) :
    let p := (correspondenceRightRemainingFiniteGenericEquivMinPrime
      f g h i z w v hw hv x q).1
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      ((Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl
          (correspondenceRightRemainingFiniteTorModule f g h i z w v x n))).toNat : ℤ)) =
      correspondenceIncidenceTorCoefficient k g h i w v
        (correspondenceRightExteriorGenericLabel f g h i z w v
          (correspondenceRightRemainingFiniteGenericLabel f g h i z w v x q)) *
            (correspondenceRightExteriorFiberLength f g h i z w v
              (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1) : ℤ) := by
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient g h i) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceIntersectionAmbientToField k g h i)
  dsimp only
  simp_rw [natCast_length_localized_correspondenceRightRemainingFiniteTorModule
    f g h i z w v hw hv x q]
  change (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (_ * _)) =
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * _) * _
  rw [finsum_mul]
  apply finsum_congr
  intro n
  exact (mul_assoc _ _ _).symm

end Field

end Stacks.Chow
