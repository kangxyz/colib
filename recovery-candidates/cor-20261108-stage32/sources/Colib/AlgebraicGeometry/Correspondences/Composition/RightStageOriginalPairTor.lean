/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageAmbientStalkSquare
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStagePairTorBaseChange

/-!
# Actual Z-first Koszul homology and original last-pair Tor

The original Z-stalk regular family is pulled through the actual last-pair
ambient into the unchanged common sixfold ambient. Native flat local base
change proves regularity, and the actual Z-first Cartesian square proves its
kernel ideal. The full right-stage ring therefore acts by the canonical
quotient construction, with its original sixfold action recovered exactly.

The original common support coefficient module is retained. A proved equality
of support points supplies its explicit stalk-congruence isomorphism to the
right-labelled support stalk. The actual scalar square, native support flat
base change, and pushout cancellation then identify every homology degree
with the full tensor pullback of original G,H Tor. Surjectivity of the actual
ambient-to-right-stage map upgrades the comparison to right-stage linearity.

Only flatness over the original base is required of the first support. No
flatness of a finite intermediate image, no reversed admissibility, and no
coefficient comparison are assumed. Nilpotents and all exterior multiplicities
are retained. This is a first-homology supplier, not an associativity theorem.

Reference: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean,
Git blob 5771cc85d24a32f3610872f2a94d457154d1673b. The proof reuses the accepted
native FirstStageOriginalPairTor construction with actual Z-first maps.
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

private theorem idealStalk_ker_eq_map_of_isPullback
    {U V T B : Scheme.{u}} {j : U ⟶ V} {q : U ⟶ T} {π : V ⟶ B} {k : T ⟶ B}
    (H : IsPullback j q π k) [IsClosedImmersion k] (u : U) (p : V) (hp : p = j u) :
    IdealSheafData.stalk j.ker p =
      (IdealSheafData.stalk k.ker (π p)).map (π.stalkMap p).hom := by
  subst p
  have : IsClosedImmersion j := MorphismProperty.of_isPullback H.flip inferInstance
  have hpt : k (q u) = π (j u) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m u) H.w.symm
  have hk := Stacks.Flatness.ker_stalkMap_of_isPullback H u hpt
  rw [ker_stalkMap_eq_idealStalk_ker k (q u), CommRingCat.hom_comp,
    ← Ideal.map_map, map_actual_ideal_stalk_congr _ hpt,
    ker_stalkMap_eq_idealStalk_ker] at hk
  exact hk

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "u" =>
  correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" =>
  correspondenceRightExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion g h i w v (π u)
local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "A₀" => correspondenceIncidenceAmbientStalk g h i w v (π u)
local notation3 (prettyPrint := false) "D" =>
  (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceRightIntermediateToTripleSupport f g h i z w v u)
local notation3 (prettyPrint := false) "P" =>
  (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk u
local notation3 (prettyPrint := false) "P₀" =>
  (correspondenceIncidence g h i w v).presheaf.stalk (π u)
local notation3 (prettyPrint := false) "R₀" =>
  (pullback h h).presheaf.stalk (correspondenceMiddlePair g h i p₀)
local notation3 (prettyPrint := false) "β" => ((correspondenceMiddlePair g h i).stalkMap p₀).hom
local notation3 (prettyPrint := false) "α" =>
  correspondenceTripleIncidenceRightPairAmbientStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "ε" =>
  correspondenceTripleIncidenceRightSupportStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "ρ" => correspondenceIncidenceSupportStalkMap g h i w v (π u)
local notation3 (prettyPrint := false) "φ" =>
  correspondenceRightExteriorSupportStalkMap f g h i z w v u
local notation3 (prettyPrint := false) "κ" =>
  correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "η" =>
  ((correspondenceRightIntermediateToTripleSupport f g h i z w v).stalkMap u).hom
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x

/-- The actual Z-first diagonal ideal is the extension of the original pair diagonal kernel. -/
theorem correspondenceTripleIncidence_secondDiagonalIdeal_eq_map_pair [IsSeparated h] :
    IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      (RingHom.ker ((correspondenceTripleInclusion g h i).stalkMap
        (correspondenceIncidenceInclusion g h i w v (π u))).hom).map α := by
  let q := correspondenceRightIntermediateSupportInclusion f g h i z w v u
  have hp : p = correspondenceSecondAmbientInclusion f g h i q :=
    correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v x
  have hk := idealStalk_ker_eq_map_of_isPullback
    (correspondenceSecondAmbient_baseChange_right f g h i).flip q p hp
  have hk₀ : RingHom.ker ((correspondenceTripleInclusion g h i).stalkMap
      (correspondenceIncidenceInclusion g h i w v (π u))).hom =
        IdealSheafData.stalk (correspondenceTripleInclusion g h i).ker p₀ :=
    ker_stalkMap_eq_idealStalk_ker (correspondenceTripleInclusion g h i)
      (correspondenceIncidenceInclusion g h i w v (π u))
  rw [hk₀, correspondenceTripleIncidenceRightPairAmbientStalkMap,
    CommRingCat.hom_comp, ← Ideal.map_map,
    map_actual_ideal_stalk_congr _
      (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v x)]
  exact hk

/-- The original Z list gives the actual right-stage regular equations through the actual maps. -/
theorem correspondenceOriginalLastPairList_rightFirst_regular [Flat f] [Flat g] [Flat i]
  [IsSeparated h]
    {r : ℕ} (s : Fin r → R₀) (hs : IsRegular R₀ (List.ofFn s))
    (hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s)) :
    IsRegular A (List.ofFn (fun j => α (β (s j)))) ∧
      IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (List.ofFn (fun j => α (β (s j)))) := by
  obtain ⟨hr₀, hk₀⟩ := correspondenceOriginalMiddleList_pair_regular g h i
    (correspondenceIncidenceInclusion g h i w v (π u)) s hs hks
  change IsRegular A₀ (List.ofFn (fun j => β (s j))) at hr₀
  change RingHom.ker ((correspondenceTripleInclusion g h i).stalkMap
    (correspondenceIncidenceInclusion g h i w v (π u))).hom =
      Ideal.span (Set.range (fun j => β (s j))) at hk₀
  let : Algebra A₀ A := (α).toAlgebra
  have : Module.Flat A₀ A := flat_correspondenceTripleIncidenceRightPairAmbientStalkMap
    f g h i z w v x
  have : IsLocalHom (algebraMap A₀ A) := by
    change IsLocalHom (α)
    unfold correspondenceTripleIncidenceRightPairAmbientStalkMap
    have := isLocalHom_of_iso
      ((correspondenceIntersectionAmbient g h i).presheaf.stalkCongr
        (Inseparable.of_eq (correspondenceTripleIncidence_rightPairAmbient_point_eq f g h i z w v
          x)))
    exact CommRingCat.isLocalHom_comp _ _
  have : Module.FaithfullyFlat A₀ A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  constructor
  · have hr : IsRegular A ((List.ofFn (fun j => β (s j))).map (algebraMap A₀ A)) :=
      hr₀.of_faithfullyFlat
    change IsRegular A ((List.ofFn (fun j => β (s j))).map α) at hr
    simpa only [List.map_ofFn, Function.comp_def] using hr
  · rw [correspondenceTripleIncidence_secondDiagonalIdeal_eq_map_pair, hk₀,
      Ideal.map_span, ← Set.range_comp, ← Ideal.ofList_ofFn]
    rfl

/-- Actual Z-first homology is the genuine right-exterior pullback of original last-pair Tor,
linear over the full right-stage stalk with its canonical quotient-induced action. -/
def correspondenceTripleIncidenceRightFirstKoszulIsoOriginalPairTor
    [Flat f] [Flat g] [Flat i] [IsSeparated h]
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    {r : ℕ} (s : Fin r → R₀) (hs : IsRegular R₀ (List.ofFn s))
    (hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s)) (n : ℕ) :
    let a := fun j => α (β (s j))
    let l := List.ofFn a
    let hreg := correspondenceOriginalLastPairList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    letI := correspondenceIncidenceTorModule g h i w v (π u) n
    letI : Algebra P₀ P := ((π).stalkMap u).hom.toAlgebra
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π u) n) := by
  let a : Fin r → A := fun j => α (β (s j))
  let l := List.ofFn a
  let hreg := correspondenceOriginalLastPairList_rightFirst_regular f g h i z w v x s hs hks
  letI := correspondenceTripleIncidenceRightFirstKoszulModule
    f g h i z w v x l hreg.1 hreg.2 n
  letI := correspondenceIncidenceTorModule g h i w v (π u) n
  letI : Algebra P₀ P := ((π).stalkMap u).hom.toAlgebra
  letI : Algebra A D := (ε).toAlgebra
  letI : Algebra A P := (κ).toAlgebra
  letI : Algebra D P := (η).toAlgebra
  letI : IsScalarTower A D P := IsScalarTower.of_algebraMap_eq'
    (correspondenceTripleIncidenceRightSupportStalkMap_firstStage_comp f g h i z w v x).symm
  letI := correspondenceTripleIncidenceRightFirstKoszulScalarTower
    f g h i z w v x l hreg.1 hreg.2 n
  let N := (Koszul.seqComplexTensor (fun j => φ (ρ (β (s j)))) D).homology n
  letI : Module A N := Module.compHom N ε
  letI : IsScalarTower A D N := IsScalarTower.of_compHom A D N
  have htuple : (⟨l.length, l.get⟩ : Σ k, Fin k → A) = ⟨r, a⟩ :=
    List.equivSigmaTuple.apply_symm_apply ⟨r, a⟩
  have hcomplex : Koszul.seqComplexTensor l.get M = Koszul.seqComplexTensor a M :=
    congrArg (fun q : Σ k, Fin k → A => Koszul.seqComplexTensor q.2 M) htuple
  let e₁ := (HomologicalComplex.homologyFunctor _ _ n).mapIso (eqToIso hcomplex)
  let eCoeff := (HomologicalComplex.homologyFunctor _ _ n).mapIso
    ((Koszul.seqComplexTensorFunctor a).mapIso
      (correspondenceTripleIncidenceRightSupportStalkIso f g h i z w v x))
  let e₂ := Koszul.homologySeqComplexTensorRestrictScalarsIso a (ModuleCat.of D D) n
  have hlist : (fun j => ε (a j)) = (fun j => φ (ρ (β (s j)))) := by
    funext j
    exact congrArg (fun ψ : A₀ →+* D => ψ (β (s j)))
      (correspondenceTripleIncidence_rightAmbientSupport_stalk_comm f g h i z w v x)
  let e₃ := (ModuleCat.restrictScalars (ε)).mapIso
    (eqToIso (congrArg (fun bs : Fin r → D => (Koszul.seqComplexTensor bs D).homology n) hlist))
  let ebase := Classical.choice (correspondenceRightExterior_originalPairTor_baseChange
    f g h i z w v u s hs hks n)
  let eA := (e₁ ≪≫ eCoeff ≪≫ e₂ ≪≫ e₃).toLinearEquiv.trans (ebase.restrictScalars A)
  exact eA.extendScalarsOfSurjective
    (correspondenceTripleIncidenceRightFirstStageStalkMap_surjective f g h i z w v x)

end Stacks.Chow
