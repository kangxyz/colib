/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorSheaf
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorMultiplicity
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic

/-!
# The original Tor coefficients over the whole remaining finite algebra

For every original Tor degree, pull the actual incidence Tor sheaf to the full
first-stage exterior and then to the entire local finite model. Its global
sections form a finite module over that model's actual coordinate ring.
The signed generic Euler formula is applied to this canonical family, rather
than a caller-supplied family of finite modules. Higher Tor signs and all
minimal source labels are retained.

The original pair stalk comparison is supplied by `PairTorSheaf`. At every
exterior point the multiplicity is the original native Tor length times the
full exterior fibre length (Stacks 02M1). That factor is not set to one over
an arbitrary field. This file does not yet reindex affine minimal primes as
original scheme labels or identify remaining component cycles globally.

Finiteness of the global sections uses native Stacks 01PB on the proved
whole affine finite model. No affine neighbourhood containing all the original
finite-source points, reduction of the source, or flatness of the finite map
is assumed.
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

/-- Every original Tor sheaf, pulled to the full first-stage exterior. -/
abbrev correspondenceLeftExteriorTorSheaf (n : ℕ) :
    (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules :=
  (Scheme.Modules.pullback (correspondenceLeftExteriorProjection f g h i z w v)).obj
    (correspondencePairTorSheaf f g h z w n)

/-- The same actual Tor degree on the whole finite local model. -/
abbrev correspondenceRemainingFiniteTorSheaf
    (x : correspondenceLeftImageIncidence f g h i z w v) (n : ℕ) :
    (correspondenceRemainingFiniteModel f g h i z w v x).Modules :=
  (Scheme.Modules.pullback (correspondenceRemainingFiniteModelProjection f g h i z w v x)).obj
    (correspondenceLeftExteriorTorSheaf f g h i z w v n)

/-- The canonical module over the full finite algebra, with its sheaf-section action. -/
abbrev correspondenceRemainingFiniteTorModule
    (x : correspondenceLeftImageIncidence f g h i z w v) (n : ℕ) :
    ModuleCat (correspondenceRemainingFiniteRing f g h i z w v x) :=
  ModuleCat.of (correspondenceRemainingFiniteRing f g h i z w v x)
    Γ(correspondenceRemainingFiniteTorSheaf f g h i z w v x n, ⊤)

/-- Ordinary exterior pullback preserves quasi-coherence and finite type. -/
theorem isQuasicoherent_isFiniteType_correspondenceLeftExteriorTorSheaf [IsSeparated g]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)] (n : ℕ) :
    (correspondenceLeftExteriorTorSheaf f g h i z w v n).IsQuasicoherent ∧
      (correspondenceLeftExteriorTorSheaf f g h i z w v n).IsFiniteType := by
  obtain ⟨hqc, hft⟩ := isQuasicoherent_isFiniteType_correspondencePairTorSheaf f g h z w n
  let := hft
  exact ⟨Stacks.Modules.isQuasicoherent_pullback
      (correspondenceLeftExteriorProjection f g h i z w v) _ hqc,
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      (correspondenceLeftExteriorProjection f g h i z w v).toLRSHom.toShHom _⟩

/-- Localization to the entire finite model preserves the two finiteness properties. -/
theorem isQuasicoherent_isFiniteType_correspondenceRemainingFiniteTorSheaf [IsSeparated g]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]
    (x : correspondenceLeftImageIncidence f g h i z w v) (n : ℕ) :
    (correspondenceRemainingFiniteTorSheaf f g h i z w v x n).IsQuasicoherent ∧
      (correspondenceRemainingFiniteTorSheaf f g h i z w v x n).IsFiniteType := by
  obtain ⟨hqc, hft⟩ :=
    isQuasicoherent_isFiniteType_correspondenceLeftExteriorTorSheaf f g h i z w v n
  let := hft
  exact ⟨Stacks.Modules.isQuasicoherent_pullback
      (correspondenceRemainingFiniteModelProjection f g h i z w v x) _ hqc,
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      (correspondenceRemainingFiniteModelProjection f g h i z w v x).toLRSHom.toShHom _⟩

/-- The actual Tor coefficient module is finite over the whole finite algebra. -/
theorem moduleFinite_correspondenceRemainingFiniteTorModule [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) (n : ℕ) :
    Module.Finite (correspondenceRemainingFiniteRing f g h i z w v x)
      (correspondenceRemainingFiniteTorModule f g h i z w v x n) := by
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  obtain ⟨hqc, hft⟩ :=
    isQuasicoherent_isFiniteType_correspondenceRemainingFiniteTorSheaf f g h i z w v x n
  let := hqc
  let := hft
  exact Stacks.AlgebraicGeometry.CoherentFinite.finite_sections
    (correspondenceRemainingFiniteTorSheaf f g h i z w v x n) (isAffineOpen_top _)

/-- The actual exterior coefficient keeps the original Tor degree and full fibre multiplicity. -/
theorem sheafMultiplicity_correspondenceLeftExteriorTorSheaf [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) (n : ℕ) :
    sheafMultiplicity (correspondenceLeftExteriorTorSheaf f g h i z w v n) x =
      ((Module.length
        (correspondenceIncidenceAmbientStalk f g h z w
          (correspondenceLeftExteriorProjection f g h i z w v x))
        (correspondenceIncidenceAmbientTor f g h z w
          (correspondenceLeftExteriorProjection f g h i z w v x) n)).toNat : ℤ) *
            (correspondenceLeftExteriorFiberLength f g h i z w v x : ℤ) := by
  rw [sheafMultiplicity_correspondenceLeftExterior_pullback]
  congr 1
  change ((Module.length _ _).toNat : ℤ) = _
  rw [length_correspondencePairTorSheaf_stalk]

section ActualGenericImage

variable [IsSeparated g] [IsSeparated h]
  [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]
  [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))

local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "B" => correspondenceRemainingFiniteRing f g h i z w v x.1
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk
  (correspondenceLeftImageMiddlePair f g h i z w v
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))
local notation3 (prettyPrint := false) "α" => correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "M" => correspondenceRemainingFiniteTorModule f g h i z w v x.1

/-- Every degree of the actual original Tor family has finite remaining homology. -/
theorem length_correspondenceRemainingFiniteTorKoszul_ne_top {r : ℕ} (s : Fin r → A)
    (hr : RingTheory.Sequence.IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) (b n : ℕ) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    Module.length B
      ((Koszul.seqComplexTensor (fun j => algebraMap R B (α (s j))) (M b)).homology n) ≠ ⊤ := by
  let := moduleFinite_correspondenceRemainingFiniteTorModule f g h i z w v hz hw x.1 b
  exact length_correspondenceRemainingFiniteKoszul_ne_top f g h i z w v hz hw x s hr hs (M b) n

/-- Signed integer Euler for the actual whole finite original Tor family. All original
minimal primes, higher Tor signs, and native original residue degrees remain explicit. -/
theorem sum_signed_seqEuler_correspondenceRemainingFiniteTorModule {r : ℕ} (s : Fin r → A)
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) (J : Finset ℕ) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∑ b ∈ J, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : {q : PrimeSpectrum B // IsMin q},
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          ((Module.length (Localization.AtPrime q.1.asIdeal)
            (LocalizedModule q.1.asIdeal.primeCompl (M b))).toNat : ℤ)) *
              (Stacks.Length.primeResidueDegree (algebraMap R B)
                (q.1.asIdeal.comap (algebraMap R B)) q.1.asIdeal : ℤ) *
                  Koszul.seqEuler (fun j => α (s j))
                    (R ⧸ q.1.asIdeal.comap (algebraMap R B)) := by
  letI : ∀ b, Module.Finite B (M b) :=
    fun b => moduleFinite_correspondenceRemainingFiniteTorModule f g h i z w v hz hw x.1 b
  exact sum_signed_seqEuler_correspondenceRemainingFiniteModel f g h i z w v hz hw x s hs M J

end ActualGenericImage

end Stacks.Chow
