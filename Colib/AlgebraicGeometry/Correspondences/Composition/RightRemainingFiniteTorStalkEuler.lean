/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorStalkIso
public import Colib.RingTheory.Koszul.RestrictionComparison
public import Colib.RingTheory.Koszul.GenericEuler

/-!
# Actual right finite tensor-localization Euler equals the actual Tor-sheaf stalk Euler

The finite-pushforward coefficient is the tensor localization of the canonical global
sections module. The actual affine localization-to-stalk equivalence identifies it with
the same Tor sheaf's stalk, and the native Koszul projection formula changes the scalar
ring along that actual ring isomorphism. Module length is unchanged because this scalar
map is surjective. The list is literally mapped to its section germs, entry by entry.

This is the base-ring change missing from a same-ring coefficient-complex comparison.
It neither assumes finite length nor identifies different scalar-ring Koszul complexes
by definitional equality. The original finite algebra and full sheaf stalk are retained.
The subsequent original G,H comparison uses the existing actual right exterior sheaf
stalk and the original first-middle Y action. It is not an equality assumption here.

References: native affine sheaf germ localization (`isLocalizedModule_germₗ`),
Mathlib's `IsLocalization.algEquiv`, the native exterior-power Koszul base-change map
consumed by `Koszul.homologySeqComplexTensorRestrictScalarsIso`, and Mathlib's
`Module.length_eq_of_surjective`. This is a direct application to the canonical family.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
  (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)

/-- Each remaining homology length is unchanged on passing from the actual tensor
localization to the actual sheaf stalk, with its actual section-germ list. -/
theorem length_correspondenceRightRemainingFiniteTorTensorKoszul_eq_stalk
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (n : ℕ) {r : ℕ} (s : Fin r → (correspondenceRightRemainingFiniteRing f g h i z w v x)) (a : ℕ) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let Q := (correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q
    let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    letI := stalkModule (F n) q
    Module.length (Localization.AtPrime p.asIdeal)
      ((Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (Localization.AtPrime p.asIdeal ⊗[B] M n)).homology a) =
      Module.length Q
        ((Koszul.seqComplexTensor (fun j => (E).presheaf.germ ⊤ q trivial (s j))
          ((F n).presheaf.stalk q)).homology a) := by
  dsimp only
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let Q := (correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q
  let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
  let L := Localization.AtPrime p.asIdeal
  let : Algebra B Q := (E.presheaf.germ ⊤ q trivial).hom.toAlgebra
  let e := correspondenceRightRemainingFiniteStalkAlgEquiv f g h i z w v hw hv x q
  let := stalkModule (F n) q
  let : Algebra L Q := e.toRingEquiv.toRingHom.toAlgebra
  let N : ModuleCat Q := ModuleCat.of Q ((F n).presheaf.stalk q)
  let sL : Fin r → L := fun j => algebraMap B L (s j)
  let N₀ := (ModuleCat.restrictScalars (algebraMap L Q)).obj N
  have hl : (fun j => algebraMap L Q (sL j)) =
      (fun j => (E).presheaf.germ ⊤ q trivial (s j)) := by
    funext j
    exact e.commutes (s j)
  have he := ((HomologicalComplex.homologyFunctor (ModuleCat L) (.down ℕ) a).mapIso
    (correspondenceRightRemainingFiniteTorTensorKoszulStalkIso
      f g h i z w v hw hv x q n s)).toLinearEquiv.length_eq
  have hp := (Koszul.homologySeqComplexTensorRestrictScalarsIso sL N a).toLinearEquiv.length_eq
  let H := (Koszul.seqComplexTensor (fun j => algebraMap L Q (sL j)) N).homology a
  let : Module L H := Module.compHom H (algebraMap L Q)
  let : IsScalarTower L Q H := .of_algebraMap_smul fun _ _ => rfl
  have hlen : Module.length L H = Module.length Q H :=
    Module.length_eq_of_surjective e.surjective
  calc
    _ = Module.length L ((Koszul.seqComplexTensor sL N₀).homology a) := he
    _ = Module.length L H := hp
    _ = Module.length Q H := hlen
    _ = _ := congrArg
      (fun t : Fin r → Q => Module.length Q ((Koszul.seqComplexTensor t N).homology a)) hl

/-- The actual localized Euler equals the actual sheaf-stalk Euler over its own local ring.
All original equations and degrees are unchanged; no length finiteness is hidden in the claim. -/
theorem seqEuler_correspondenceRightRemainingFiniteTorTensor_eq_stalk
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (n : ℕ) {r : ℕ} (s : Fin r → (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    letI := stalkModule (F n) q
    Koszul.seqEuler (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
      (Localization.AtPrime p.asIdeal ⊗[B] M n) =
      Koszul.seqEuler (fun j => (E).presheaf.germ ⊤ q trivial (s j))
        ((F n).presheaf.stalk q) := by
  dsimp only
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let Q := (correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q
  let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  let := stalkModule (F n) q
  unfold Koszul.seqEuler
  apply Finset.sum_congr rfl
  intro a _
  rw [length_correspondenceRightRemainingFiniteTorTensorKoszul_eq_stalk
    f g h i z w v hw hv x q n s a]

end Stacks.Chow
