/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStageAmbientStalkSquare
public import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStagePairTorBaseChange

/-!
# Actual sixfold first Koszul homology and the original pair Tor coefficient

The original Y-stalk family is pulled through the actual pair ambient and its actual
projection into the sixfold ambient. Flat local base change proves regularity, and native
Cartesian ideal base change proves its actual first-diagonal kernel. Thus the first-stage
quotient action is the already proved canonical action, not a caller-supplied structure.

The coefficient restriction comparison uses the actual commuting stalk square. Native flat
support base change and pushout cancellation identify its homology with the pullback of the
original pair Tor. Finally, the actual surjection from the sixfold ambient to the full first
incidence extends linearity to that incidence ring. The result retains the original pair
incidence action on the tensor factor and every higher Tor degree.

No length is declared unchanged under the exterior flat map. Subsequent multiplicity formulas
must keep the full closed-fibre length. This identification is one coefficient supplier for
Cor associativity; it is not the remaining Euler or finite-image bracket comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open scoped TensorProduct

universe u

namespace Stacks.Chow

private theorem map_actual_ideal_stalk_congr {X : Scheme.{u}} (I : X.IdealSheafData)
    {x y : X} (hxy : x = y) :
    (IdealSheafData.stalk I x).map
      (X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom.hom =
        IdealSheafData.stalk I y := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "u" =>
  correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" =>
  (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
    (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) :
    correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶
      correspondenceIncidence f g h z w)
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion f g h z w (π u)
local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "A₀" => correspondenceIncidenceAmbientStalk f g h z w (π u)
local notation3 (prettyPrint := false) "D" =>
  (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceTripleIncidenceToTripleSupport f g h i z w v x)
local notation3 (prettyPrint := false) "P" =>
  (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk u
local notation3 (prettyPrint := false) "P₀" =>
  (correspondenceIncidence f g h z w).presheaf.stalk (π u)
local notation3 (prettyPrint := false) "R₀" =>
  (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h p₀)
local notation3 (prettyPrint := false) "β" => ((correspondenceMiddlePair f g h).stalkMap p₀).hom
local notation3 (prettyPrint := false) "α" =>
  correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "ε" =>
  correspondenceTripleIncidenceSupportStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "ρ" => correspondenceIncidenceSupportStalkMap f g h z w (π u)
local notation3 (prettyPrint := false) "φ" =>
  correspondenceLeftExteriorSupportStalkMap f g h i z w v u
local notation3 (prettyPrint := false) "κ" =>
  correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "η" =>
  ((correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap u).hom
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x

/-- The actual first diagonal ideal is the extension of the original pair diagonal kernel. -/
theorem correspondenceTripleIncidence_firstDiagonalIdeal_eq_map_pair [IsSeparated g] :
    IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
      (RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
        (correspondenceIncidenceInclusion f g h z w (π u))).hom).map α := by
  let q := correspondenceSecondDiagonalInclusion f g h i
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)
  let πd := pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)
  have hp : correspondenceTripleInclusion f g h (πd q) =
      correspondenceSixfoldPairProjection f g h i p := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m => m q) (correspondenceFirstDiagonal_baseChange f g h i).w
  have hk := Stacks.Flatness.ker_stalkMap_of_isPullback
    (correspondenceFirstDiagonal_baseChange f g h i).flip q hp
  rw [ker_stalkMap_eq_idealStalk_ker (correspondenceTripleInclusion f g h) (πd q),
    CommRingCat.hom_comp, ← Ideal.map_map,
    map_actual_ideal_stalk_congr _ hp, ker_stalkMap_eq_idealStalk_ker] at hk
  change IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
    (IdealSheafData.stalk (correspondenceTripleInclusion f g h).ker
      (correspondenceSixfoldPairProjection f g h i p)).map
        ((correspondenceSixfoldPairProjection f g h i).stalkMap p).hom at hk
  have hk₀ : RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
      (correspondenceIncidenceInclusion f g h z w (π u))).hom =
        IdealSheafData.stalk (correspondenceTripleInclusion f g h).ker p₀ :=
    ker_stalkMap_eq_idealStalk_ker (correspondenceTripleInclusion f g h)
      (correspondenceIncidenceInclusion f g h z w (π u))
  rw [hk₀, correspondenceTripleIncidencePairAmbientStalkMap,
    CommRingCat.hom_comp, ← Ideal.map_map,
    map_actual_ideal_stalk_congr _
      (correspondenceTripleIncidence_pairAmbient_point_eq f g h i z w v x)]
  exact hk

/-- The original Y list gives the actual first-stage regular equations through the actual maps. -/
theorem correspondenceOriginalPairList_first_regular [Flat f] [Flat h] [Flat i] [IsSeparated g]
    {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) :
    IsRegular A (List.ofFn (fun j => α (β (t j)))) ∧
      IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList (List.ofFn (fun j => α (β (t j)))) := by
  obtain ⟨hr₀, hk₀⟩ := correspondenceOriginalMiddleList_pair_regular f g h
    (correspondenceIncidenceInclusion f g h z w (π u)) t ht hkt
  let : Algebra A₀ A := (α).toAlgebra
  have : Module.Flat A₀ A := flat_correspondenceTripleIncidencePairAmbientStalkMap
    f g h i z w v x
  have : IsLocalHom (algebraMap A₀ A) := by
    change IsLocalHom (α)
    unfold correspondenceTripleIncidencePairAmbientStalkMap
    have := CommRingCat.isLocalHom_of_iso
      ((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
        (Inseparable.of_eq (correspondenceTripleIncidence_pairAmbient_point_eq f g h i z w v x)))
    exact CommRingCat.isLocalHom_comp _ _
  have : Module.FaithfullyFlat A₀ A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  constructor
  · have hr : IsRegular A ((List.ofFn (fun j => β (t j))).map (algebraMap A₀ A)) :=
      hr₀.of_faithfullyFlat
    change IsRegular A ((List.ofFn (fun j => β (t j))).map α) at hr
    simpa only [List.map_ofFn, Function.comp_def] using hr
  · rw [correspondenceTripleIncidence_firstDiagonalIdeal_eq_map_pair, hk₀,
      Ideal.map_span, ← Set.range_comp, ← Ideal.ofList_ofFn]

/-- Actual sixfold first homology is the genuine first-incidence pullback of original pair Tor,
linear over the full first-stage stalk with its canonical quotient-induced action. -/
def correspondenceTripleIncidenceFirstKoszulIsoOriginalPairTor
    [Flat f] [Flat h] [Flat i] [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) (n : ℕ) :
    let a := fun j => α (β (t j))
    let l := List.ofFn a
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x t ht hkt
    letI := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    letI := correspondenceIncidenceTorModule f g h z w (π u) n
    letI : Algebra P₀ P := ((π).stalkMap u).hom.toAlgebra
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor f g h z w (π u) n) := by
  let a : Fin r → A := fun j => α (β (t j))
  let l := List.ofFn a
  let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x t ht hkt
  letI := correspondenceTripleIncidenceFirstKoszulModule
    f g h i z w v x l hreg.1 hreg.2 n
  letI := correspondenceIncidenceTorModule f g h z w (π u) n
  letI : Algebra P₀ P := ((π).stalkMap u).hom.toAlgebra
  letI : Algebra A D := (ε).toAlgebra
  letI : Algebra A P := (κ).toAlgebra
  letI : Algebra D P := (η).toAlgebra
  letI : IsScalarTower A D P := IsScalarTower.of_algebraMap_eq'
    (correspondenceTripleIncidenceSupportStalkMap_firstStage_comp f g h i z w v x).symm
  letI := correspondenceTripleIncidenceFirstKoszulScalarTower
    f g h i z w v x l hreg.1 hreg.2 n
  let N := (Koszul.seqComplexTensor (fun j => φ (ρ (β (t j)))) D).homology n
  letI : Module A N := Module.compHom N ε
  letI : IsScalarTower A D N := IsScalarTower.of_compHom A D N
  have htuple : (⟨l.length, l.get⟩ : Σ k, Fin k → A) = ⟨r, a⟩ :=
    List.equivSigmaTuple.apply_symm_apply ⟨r, a⟩
  have hcomplex : Koszul.seqComplexTensor l.get M = Koszul.seqComplexTensor a M :=
    congrArg (fun q : Σ k, Fin k → A => Koszul.seqComplexTensor q.2 M) htuple
  let e₁ := (HomologicalComplex.homologyFunctor _ _ n).mapIso (eqToIso hcomplex)
  let e₂ := Koszul.homologySeqComplexTensorRestrictScalarsIso a (ModuleCat.of D D) n
  have hlist : (fun j => ε (a j)) = (fun j => φ (ρ (β (t j)))) := by
    funext j
    exact congrArg (fun ψ : A₀ →+* D => ψ (β (t j)))
      (correspondenceTripleIncidence_ambientSupport_stalk_comm f g h i z w v x)
  let e₃ := (ModuleCat.restrictScalars (ε)).mapIso
    (eqToIso (congrArg (fun bs : Fin r → D => (Koszul.seqComplexTensor bs D).homology n) hlist))
  obtain ⟨ebase⟩ := correspondenceLeftExterior_originalPairTor_baseChange
    f g h i z w v u t ht hkt n
  let eA := (e₁ ≪≫ e₂ ≪≫ e₃).toLinearEquiv.trans (ebase.restrictScalars A)
  exact eA.extendScalarsOfSurjective
    (correspondenceTripleIncidenceFirstStageStalkMap_surjective f g h i z w v x)

end Stacks.Chow
