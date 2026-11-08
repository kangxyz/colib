/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStageExteriorBaseChange
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor

/-!
# Full-exterior support Koszul homology is the pullback of original pair Tor

The actual first-stage support square gives the native local-ring pushout
`P = P₀ ⊗[D₀] D`. The original Y list computes pair Tor as a `D₀`-module, with the
`D₀` action restricted from the canonical original incidence action over `P₀`.
Native flat Koszul base change and native pushout cancellation therefore identify
full-exterior support homology with `P ⊗[P₀] Tor_original`, as `D`-modules.

Every ring and map below is an original scheme stalk or its actual stalk map. Neither
Tor nor the scalar action is an input. Flatness is required only for the full exterior
projection, supplied by the third support over the base. No reduced product, geometric
integrality, or fibre-length-one hypothesis occurs.

The remaining comparison with the sixfold first Koszul homology must still identify the
same original Y stalk through the actual ambient projection and extend linearity to `P`.
This file proves the support-side base-change identification, not that remaining identification
or either complete correspondence bracket formula.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceLeftIntermediateSupportProduct f g h i z w v)

local notation3 (prettyPrint := false) "π" =>
  (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
    (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) :
    correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶
      correspondenceIncidence f g h z w)
local notation3 (prettyPrint := false) "D₀" =>
  (correspondenceSupportProduct f g h z w).presheaf.stalk
    (correspondenceIncidenceToSupportProduct f g h z w (π x))
local notation3 (prettyPrint := false) "P₀" =>
  (correspondenceIncidence f g h z w).presheaf.stalk (π x)
local notation3 (prettyPrint := false) "D" =>
  (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceLeftIntermediateToTripleSupport f g h i z w v x)
local notation3 (prettyPrint := false) "P" =>
  (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk x
local notation3 (prettyPrint := false) "φ" =>
  correspondenceLeftExteriorSupportStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "η₀" =>
  ((correspondenceIncidenceToSupportProduct f g h z w).stalkMap (π x)).hom
local notation3 (prettyPrint := false) "η" =>
  ((correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap x).hom
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion f g h z w (π x)
local notation3 (prettyPrint := false) "R₀" =>
  (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h p₀)
local notation3 (prettyPrint := false) "β" => ((correspondenceMiddlePair f g h).stalkMap p₀).hom
local notation3 (prettyPrint := false) "ρ" => correspondenceIncidenceSupportStalkMap f g h z w (π x)

/-- Full-exterior homology is the actual first-incidence base change of original pair Tor,
with its canonical quotient-induced original-incidence action. -/
theorem correspondenceLeftExterior_originalPairTor_baseChange
    [Flat f] [Flat h] [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) (n : ℕ) :
    letI := correspondenceIncidenceTorModule f g h z w (π x) n
    letI : Algebra P₀ P := ((π).stalkMap x).hom.toAlgebra
    letI : Algebra D P := (η).toAlgebra
    Nonempty (((Koszul.seqComplexTensor (fun j => φ (ρ (β (t j)))) D).homology n) ≃ₗ[D]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor f g h z w (π x) n)) := by
  let : Algebra D₀ D := (φ).toAlgebra
  let : Algebra D₀ P₀ := (η₀).toAlgebra
  let : Algebra D₀ P := ((η).comp φ).toAlgebra
  let : Algebra P₀ P := ((π).stalkMap x).hom.toAlgebra
  let : Algebra D P := (η).toAlgebra
  have : IsScalarTower D₀ D P := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower D₀ P₀ P := IsScalarTower.of_algebraMap_eq' (by
    exact congrArg (fun a => a.hom)
      (Stacks.Cohomology.StalkPushout.stalkMap_comm_of_isPullback
        (correspondenceLeftIntermediate_support_isPullback f g h i z w v) x
        (correspondenceLeftIntermediate_support_point_eq f g h i z w v x)).symm)
  have : Algebra.IsPushout D₀ P₀ D P :=
    correspondenceLeftIntermediate_support_stalk_isPushout f g h i z w v x
  have : Algebra.IsPushout D₀ D P₀ P := Algebra.IsPushout.symm inferInstance
  have : Module.Flat D₀ D := flat_correspondenceLeftExteriorSupportStalkMap f g h i z w v x
  let T := correspondenceIncidenceAmbientTor f g h z w (π x) n
  let := correspondenceIncidenceTorModule f g h z w (π x) n
  let := correspondenceIncidenceTorSupportModule f g h z w (π x) n
  have : IsScalarTower D₀ P₀ T := IsScalarTower.of_compHom D₀ P₀ T
  let a : Fin r → D₀ := fun j => ρ (β (t j))
  let eunit := (Koszul.seqComplexTensorFunctor (fun j => φ (a j))).mapIso
    (TensorProduct.AlgebraTensorModule.rid D₀ D D).symm.toModuleIso
  obtain ⟨eflat⟩ := KoszulC.homology_baseChange_linearEquiv (S := D) a D₀ n
  let eoriginal := correspondenceIncidenceTorOriginalSupportLinearEquiv
    f g h z w (π x) t ht hkt n
  exact ⟨((HomologicalComplex.homologyFunctor _ _ n).mapIso eunit).toLinearEquiv.trans
    (eflat.trans ((TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl D D) eoriginal.symm).trans
        (Algebra.IsPushout.cancelBaseChange D₀ D P₀ P T).symm))⟩

end Stacks.Chow
