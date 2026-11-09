/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteModel
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightFirstTorSheaf
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic

/-!
# Original G,H Tor sections over the whole actual right finite algebra

The exterior Tor sheaf and full finite model already exist. Pull that same family onto
that same model and take global sections, without selecting a branch or discarding
nilpotents. Native quasi-coherence and finite type give finite modules in every original
Tor degree. No family, local comparison, finite-map flatness, or degree bound is an input.

References: Stacks 01PB (finite sections on an affine scheme), 0AZT (actual Tor sheaves).
The independent motivic source is a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean,
blob 5771cc85d24a32f3610872f2a94d457154d1673b, lines 107-260. This leaf supplies the
actual whole-family input only, not its weighted-cycle replacement.
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

/-- The original last-pair Tor sheaf on the entire right finite model, in degree n. -/
abbrev correspondenceRightRemainingFiniteTorSheaf
    (x : correspondenceRightImageIncidence f g h i z w v) (n : ℕ) :
    (correspondenceRightRemainingFiniteModel f g h i z w v x).Modules :=
  (Scheme.Modules.pullback
    (correspondenceRightRemainingFiniteModelProjection f g h i z w v x)).obj
      (correspondenceRightExteriorTorSheaf f g h i z w v n)

/-- Global sections with their actual full coordinate-algebra action. -/
abbrev correspondenceRightRemainingFiniteTorModule
    (x : correspondenceRightImageIncidence f g h i z w v) (n : ℕ) :
    ModuleCat (correspondenceRightRemainingFiniteRing f g h i z w v x) :=
  ModuleCat.of (correspondenceRightRemainingFiniteRing f g h i z w v x)
    Γ(correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n, ⊤)

/-- The original family's quasi-coherence and finite type survive the actual pullback. -/
theorem isQuasicoherent_isFiniteType_correspondenceRightRemainingFiniteTorSheaf
    [IsSeparated h] [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
    (x : correspondenceRightImageIncidence f g h i z w v) (n : ℕ) :
    (correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).IsQuasicoherent ∧
      (correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).IsFiniteType := by
  obtain ⟨hqc, hft⟩ :=
    isQuasicoherent_isFiniteType_correspondenceRightExteriorTorSheaf f g h i z w v n
  let := hft
  exact ⟨Stacks.Modules.isQuasicoherent_pullback
      (correspondenceRightRemainingFiniteModelProjection f g h i z w v x) _ hqc,
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      (correspondenceRightRemainingFiniteModelProjection f g h i z w v x).toLRSHom.toShHom _⟩

/-- Every degree is finite over the full finite algebra, with no chosen affine branch. -/
theorem moduleFinite_correspondenceRightRemainingFiniteTorModule [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) (n : ℕ) :
    Module.Finite (correspondenceRightRemainingFiniteRing f g h i z w v x)
      (correspondenceRightRemainingFiniteTorModule f g h i z w v x n) := by
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  obtain ⟨hqc, hft⟩ :=
    isQuasicoherent_isFiniteType_correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n
  let := hqc
  let := hft
  exact Stacks.AlgebraicGeometry.CoherentFinite.finite_sections
    (correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n) (isAffineOpen_top _)

end Stacks.Chow
