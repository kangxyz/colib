/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageOriginalPairTor
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Retaining the actual common ordered Z list in right first homology

The original-middle supplier gives a list in the common Z self-product stalk
and the equality of its extended ideal with the actual Z-first kernel. Native
faithfully-flat ideal-map injectivity recovers the original diagonal ideal;
there is no additional unproved original-ideal hypothesis. The proved equality
of Z points transports that same ordered list to the original G,H incidence.
Its image back in the common ambient is exactly the initial mapped list.

The P-linear first-homology comparison therefore uses precisely the list and
unchanged full support module occurring in the common signed total complex.
It does not choose a replacement regular sequence or change coefficients.
This is a local right first-homology comparison, not a weighted bracket or
associativity theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open scoped TensorProduct

universe u

namespace Stacks.Chow

private theorem map_actual_ideal_stalk_congr {T : Scheme.{u}} (I : T.IdealSheafData)
    {a b : T} (hab : a = b) :
    (IdealSheafData.stalk I a).map
      (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom.hom =
        IdealSheafData.stalk I b := by
  subst b
  simp [TopCat.Presheaf.stalkCongr]

private theorem idealStalk_ker_eq_map_of_isPullback
    {U V T B : Scheme.{u}} {j : U ⟶ V} {q : U ⟶ T} {π : V ⟶ B} {k : T ⟶ B}
    (H : IsPullback j q π k) [IsClosedImmersion k] (u : U) (p : V) (hp : p = j u) :
    IdealSheafData.stalk j.ker p =
      (IdealSheafData.stalk k.ker (π p)).map ((π).stalkMap p).hom := by
  subst p
  have : IsClosedImmersion j := MorphismProperty.of_isPullback H.flip inferInstance
  have hpt : k (q u) = π (j u) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m u) H.w.symm
  have hk := Stacks.Flatness.ker_stalkMap_of_isPullback H u hpt
  rw [ker_stalkMap_eq_idealStalk_ker k (q u), CommRingCat.hom_comp,
    ← Ideal.map_map, map_actual_ideal_stalk_congr _ hpt,
    ker_stalkMap_eq_idealStalk_ker] at hk
  exact hk

private theorem regular_idealStalk_transport {T : Scheme.{u}} (I : T.IdealSheafData)
    {a b : T} (hab : a = b) (s : List (T.presheaf.stalk b))
    (hs : IsRegular (T.presheaf.stalk b) s)
    (hks : IdealSheafData.stalk I b = Ideal.ofList s) :
    let s₀ := s.map (T.presheaf.stalkCongr (Inseparable.of_eq hab)).inv.hom
    IsRegular (T.presheaf.stalk a) s₀ ∧ IdealSheafData.stalk I a = Ideal.ofList s₀ := by
  subst b
  simpa [TopCat.Presheaf.stalkCongr] using And.intro hs hks

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual common Z projection is flat by the two native right ambient projections. -/
instance flat_correspondenceSixfoldSecondMiddlePair [Flat f] [Flat g] [Flat i] :
    Flat (correspondenceSixfoldSecondMiddlePair f g h i) := by
  rw [← correspondenceSixfoldRightPairProjection_middlePair]
  infer_instance

variable (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "q" =>
  correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" => correspondenceRightExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion g h i w v (π q)
local notation3 (prettyPrint := false) "A" => correspondenceTripleIncidenceAmbientStalk f g h i z
  w v x
local notation3 (prettyPrint := false) "R₀" =>
  (pullback h h).presheaf.stalk (correspondenceMiddlePair g h i p₀)
local notation3 (prettyPrint := false) "R₂" =>
  (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
local notation3 (prettyPrint := false) "σ" =>
  (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceTripleIncidence_originalSecondMiddle_point_eq f g h i z w v x))
local notation3 (prettyPrint := false) "α" =>
  correspondenceTripleIncidenceRightPairAmbientStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "β" => ((correspondenceMiddlePair g h i).stalkMap p₀).hom
local notation3 (prettyPrint := false) "γ" =>
  ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "P" =>
  (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
local notation3 (prettyPrint := false) "P₀" =>
  (correspondenceIncidence g h i w v).presheaf.stalk (π q)
local notation3 (prettyPrint := false) "κ" =>
  correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x

/-- The same ordered original Z list, transported to the proved-equal original G,H point. -/
abbrev correspondenceRightOriginalMiddleList (s : List R₂) : List R₀ := s.map (σ).inv.hom

/-- Pulling the transported list through the actual pair ambient recovers the literal common
  list. -/
theorem correspondenceRightOriginalMiddleList_map (s : List R₂) :
    (correspondenceRightOriginalMiddleList f g h i z w v x s).map ((α).comp β) = s.map γ := by
  rw [correspondenceRightOriginalMiddleList, List.map_map]
  congr 1
  funext a
  have he := congrArg (fun ψ : R₀ →+* A => ψ ((σ).inv.hom a))
    (correspondenceTripleIncidence_originalSecondMiddle_stalkMap f g h i z w v x)
  change α (β ((σ).inv.hom a)) = γ ((σ).hom.hom ((σ).inv.hom a)) at he
  have hc : (σ).hom.hom ((σ).inv.hom a) = a :=
    congrArg (fun m : R₂ ⟶ R₂ => m a) (σ).inv_hom_id
  exact he.trans (congrArg γ hc)

/-- The mapped common kernel identifies the original Z ideal by native faithfully-flat descent. -/
theorem correspondenceCommonSecondList_diagonalIdeal
    [Flat f] [Flat g] [Flat i] [IsSeparated h] (s : List R₂)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) :
    IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceSixfoldSecondMiddlePair f g h i p) = Ideal.ofList s := by
  let : Algebra R₂ A := (γ).toAlgebra
  have : Module.Flat R₂ A := Flat.stalkMap (correspondenceSixfoldSecondMiddlePair f g h i) p
  have : IsLocalHom (algebraMap R₂ A) := by
    change IsLocalHom (γ)
    infer_instance
  have : Module.FaithfullyFlat R₂ A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let q₂ := correspondenceRightIntermediateSupportInclusion f g h i z w v q
  have hp : p = correspondenceSecondAmbientInclusion f g h i q₂ :=
    correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v x
  have hk := idealStalk_ker_eq_map_of_isPullback
    (correspondenceSixfoldSecondDiagonal_isPullback f g h i).flip q₂ p hp
  apply Ideal.map_injective_of_faithfullyFlat (B := A)
  change (IdealSheafData.stalk (pullback.diagonal h).ker
    (correspondenceSixfoldSecondMiddlePair f g h i p)).map γ = (Ideal.ofList s).map γ
  rw [← hk, Ideal.map_ofList, hks]

/-- The common ordered list remains regular and generates the original G,H diagonal ideal. -/
theorem correspondenceRightOriginalMiddleList_regular_ideal
    [Flat f] [Flat g] [Flat i] [IsSeparated h] (s : List R₂)
    (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) :
    IsRegular R₀ (correspondenceRightOriginalMiddleList f g h i z w v x s) ∧
      IdealSheafData.stalk (pullback.diagonal h).ker (correspondenceMiddlePair g h i p₀) =
        Ideal.ofList (correspondenceRightOriginalMiddleList f g h i z w v x s) :=
  regular_idealStalk_transport (pullback.diagonal h).ker
    (correspondenceTripleIncidence_originalSecondMiddle_point_eq f g h i z w v x) s hs
    (correspondenceCommonSecondList_diagonalIdeal f g h i z w v x s hks)

/-- The exact common mapped Z list gives the canonical right first-stage action. -/
theorem correspondenceCommonSecondList_rightFirst_regular
    [Flat f] [Flat g] [Flat i] (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) :
    IsRegular A (s.map γ) ∧
      IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map γ) := by
  let : Algebra R₂ A := (γ).toAlgebra
  have : Module.Flat R₂ A := Flat.stalkMap (correspondenceSixfoldSecondMiddlePair f g h i) p
  have : IsLocalHom (algebraMap R₂ A) := by
    change IsLocalHom (γ)
    infer_instance
  have : Module.FaithfullyFlat R₂ A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨hs.of_faithfullyFlat, hks⟩

/-- First homology for the exact common Z list is actual original last-pair Tor pullback,
linearly over the full right stage with its canonical quotient action. -/
def correspondenceTripleIncidenceRightCommonKoszulIsoOriginalPairTor
    [Flat f] [Flat g] [Flat i] [IsSeparated h]
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) (n : ℕ) :
    let l := s.map γ
    let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    letI := correspondenceIncidenceTorModule g h i w v (π q) n
    letI : Algebra P₀ P := ((π).stalkMap q).hom.toAlgebra
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n) := by
  let s₀ := correspondenceRightOriginalMiddleList f g h i z w v x s
  obtain ⟨hs₀, hks₀⟩ := correspondenceRightOriginalMiddleList_regular_ideal
    f g h i z w v x s hs hks
  have hs₀' : IsRegular R₀ (List.ofFn s₀.get) := by
    simpa only [List.ofFn_get] using hs₀
  have hks₀' : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s₀.get) := by
    rw [← Ideal.ofList_ofFn, List.ofFn_get]
    exact hks₀
  let l := s.map γ
  let l₀ := List.ofFn (fun j => α (β (s₀.get j)))
  have hlist : l₀ = l := by
    calc
      l₀ = s₀.map ((α).comp β) := by
        simpa only [List.map_ofFn, Function.comp_def, RingHom.coe_comp] using
          congrArg (List.map ((α).comp β)) (List.ofFn_get s₀)
      _ = l := correspondenceRightOriginalMiddleList_map f g h i z w v x s
  let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
  let hreg₀ := correspondenceOriginalLastPairList_rightFirst_regular
    f g h i z w v x s₀.get hs₀' hks₀'
  let := correspondenceTripleIncidenceRightFirstKoszulModule
    f g h i z w v x l hreg.1 hreg.2 n
  let := correspondenceTripleIncidenceRightFirstKoszulModule
    f g h i z w v x l₀ hreg₀.1 hreg₀.2 n
  let := correspondenceIncidenceTorModule g h i w v (π q) n
  let : Algebra P₀ P := ((π).stalkMap q).hom.toAlgebra
  let : Algebra A P := (κ).toAlgebra
  let := correspondenceTripleIncidenceRightFirstKoszulScalarTower
    f g h i z w v x l hreg.1 hreg.2 n
  let := correspondenceTripleIncidenceRightFirstKoszulScalarTower
    f g h i z w v x l₀ hreg₀.1 hreg₀.2 n
  let T := P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n
  let : Module A T := Module.compHom T κ
  let : IsScalarTower A P T := IsScalarTower.of_compHom A P T
  let e₀ := correspondenceTripleIncidenceRightFirstKoszulIsoOriginalPairTor
    f g h i z w v x s₀.get hs₀' hks₀' n
  let eList := (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (eqToIso (congrArg (fun a : List A => Koszul.seqComplexTensor a.get M) hlist.symm))
  let eA := eList.toLinearEquiv.trans (e₀.restrictScalars A)
  exact eA.extendScalarsOfSurjective
    (correspondenceTripleIncidenceRightFirstStageStalkMap_surjective f g h i z w v x)

end Stacks.Chow
