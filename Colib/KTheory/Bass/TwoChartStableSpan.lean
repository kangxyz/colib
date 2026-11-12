/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.TwoChartSigns
public import Colib.Topology.Prespectrum.PushoutStableGeneration
public import Colib.Topology.Prespectrum.StrictSquareCone
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
Source: `Quillen/KTheory/Bass/TwoChartStableSpan.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The all-degree quotient of the original two-chart span

A genuine retraction of the plus leg kills the preceding overlap kernel in every signed
degree. Together with explicitly retained cone excision and original right-cone collapse,
this identifies the unchanged reduced pushout with the cokernel of the positive diagonal.
The forward representative is the difference of the two original inclusions.

The retraction is data supplied for the actual diagram; this file does not construct a
geometric polynomial zero section or assert excision for arbitrary prespectra.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open CategoryTheory CategoryTheory.Limits Topology.LoopPrespectrum
universe u
namespace KTheory.Bass.TwoChartStable

variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- Both original overlap maps have positive signs. -/
def overlap (d : ℤ) : (stableHomotopyFunctor d).obj A ⟶
    (stableHomotopyFunctor d).obj B ⊞ (stableHomotopyFunctor d).obj C :=
  biprod.lift ((stableHomotopyFunctor d).map f) ((stableHomotopyFunctor d).map g)

/-- The original left inclusion minus the original right inclusion. -/
def representative (d : ℤ) : (stableHomotopyFunctor d).obj B ⊞ (stableHomotopyFunctor d).obj C ⟶
    (stableHomotopyFunctor d).obj (HomotopyPushout.prespectrum f g) :=
  biprod.desc ((stableHomotopyFunctor d).map (HomotopyPushout.inl f g))
    (-((stableHomotopyFunctor d).map (HomotopyPushout.inr f g)))

/-- The actual cylinder makes the positive overlap vanish under the signed representative. -/
@[reassoc]
theorem overlap_representative (d : ℤ) : overlap f g d ≫ representative f g d = 0 := by
  have h := (HomotopyPushout.glue f g).stableHomotopyMap_eq d
  simp only [Functor.map_comp] at h
  simp [overlap, representative, biprod.lift_desc, h]

/-- Negating the second chart converts the positive diagonal to the usual signed overlap. -/
theorem overlap_secondChartNegation (d : ℤ) :
    overlap f g d ≫ (secondChartNegation _ _).hom =
      biprod.lift ((stableHomotopyFunctor d).map f) (-((stableHomotopyFunctor d).map g)) := by
  apply biprod.hom_ext <;>
    simp [overlap, secondChartNegation, biprod.lift_fst, biprod.lift_snd]

/-- The signed representative is the original sum after second-chart conjugation. -/
theorem representative_secondChartNegation (d : ℤ) :
    representative f g d = (secondChartNegation _ _).hom ≫
      biprod.desc ((stableHomotopyFunctor d).map (HomotopyPushout.inl f g))
        ((stableHomotopyFunctor d).map (HomotopyPushout.inr f g)) :=
  (secondChartNegation_sum _ _).symm

variable (r : B ⟶ A) (hr : f ≫ r = 𝟙 A)

include hr in
/-- The actual zero evaluation splits the original plus map in every signed degree. -/
theorem plus_retraction (d : ℤ) :
    (stableHomotopyFunctor d).map f ≫ (stableHomotopyFunctor d).map r =
      𝟙 ((stableHomotopyFunctor d).obj A) := by
  rw [← Functor.map_comp, hr]
  exact (stableHomotopyFunctor d).map_id A

include r hr in
/-- In particular the hidden preceding overlap kernel is zero in every degree. -/
theorem plus_injective (d : ℤ) : Function.Injective ((stableHomotopyFunctor d).map f) := by
  intro x y h
  have he := ConcreteCategory.congr_hom (plus_retraction f r hr d)
  exact (he x).symm.trans ((congrArg ((stableHomotopyFunctor d).map r) h).trans (he y))

include hr in
/-- Projection to the plus chart followed by actual zero evaluation retracts the positive overlap.
-/
theorem overlap_retraction (d : ℤ) : overlap f g d ≫ biprod.fst ≫
    (stableHomotopyFunctor d).map r = 𝟙 ((stableHomotopyFunctor d).obj A) := by
  rw [← Category.assoc, overlap, biprod.lift_fst]
  exact plus_retraction f r hr d

include r hr in
/-- The positive overlap is injective in every signed degree, including the preceding one. -/
theorem overlap_injective (d : ℤ) : Function.Injective (overlap f g d) := by
  intro x y h
  apply plus_injective f r hr d
  have he := congrArg (fun z => (biprod.fst :
    (stableHomotopyFunctor d).obj B ⊞ (stableHomotopyFunctor d).obj C ⟶ _) z) h
  simpa only [← ConcreteCategory.comp_apply, overlap, biprod.lift_fst] using he

/-- Descending the literal zero evaluation also retracts the original right inclusion. -/
def rightRetraction : HomotopyPushout.prespectrum f g ⟶ C :=
  HomotopyPushout.desc f g (r ≫ g) (𝟙 C)
    ((Homotopy.refl g).cast (by simp [← Category.assoc, hr]) (by simp))

@[reassoc]
theorem inr_rightRetraction : HomotopyPushout.inr f g ≫ rightRetraction f g r hr = 𝟙 C := by
  simp [rightRetraction]

include r hr in
/-- The original right inclusion remains injective on all signed stable groups. -/
theorem inr_injective (d : ℤ) :
    Function.Injective ((stableHomotopyFunctor d).map (HomotopyPushout.inr f g)) := by
  intro x y h
  have he : (stableHomotopyFunctor d).map (HomotopyPushout.inr f g) ≫
      (stableHomotopyFunctor d).map (rightRetraction f g r hr) = 𝟙 _ := by
    rw [← Functor.map_comp, inr_rightRetraction]
    exact (stableHomotopyFunctor d).map_id C
  exact (ConcreteCategory.congr_hom he x).symm.trans
    ((congrArg ((stableHomotopyFunctor d).map (rightRetraction f g r hr)) h).trans
      (ConcreteCategory.congr_hom he y))

variable (hf : IsStableEquivalence (mappingConeFiberComparison f))
  (hi : IsStableEquivalence (mappingConeFiberComparison (HomotopyPushout.inr f g)))
  (hc : IsStableEquivalence (HomotopyPushout.rightConeCollapse f g))

include r hr hf in
/-- Retraction kills the actual preceding cone boundary, with no connectivity hypothesis. -/
theorem coneInclusion_surjective (d : ℤ) :
    Function.Surjective ((stableHomotopyFunctor d).map (mappingConeInclusion f)) := by
  have hs : Function.Surjective
      ((stableHomotopyFunctor (d - 1 + 1)).map (mappingConeInclusion f)) := by
    intro y
    apply (stableMappingConeConnecting_exact_cone f hf (d - 1) y).mp
    apply plus_injective f r hr (d - 1)
    rw [map_zero]
    exact (stableMappingConeConnecting_exact_source f hf (d - 1) _).mpr ⟨y, rfl⟩
  exact Eq.mp (congrArg
    (fun k : ℤ => Function.Surjective ((stableHomotopyFunctor k).map (mappingConeInclusion f)))
      (sub_add_cancel d 1)) hs

include r hr hf hi hc in
/-- The signed original chart inclusions generate in every signed degree. -/
theorem representative_surjective (d : ℤ) : Function.Surjective (representative f g d) := by
  let := hc d
  intro z
  obtain ⟨b, hb⟩ := coneInclusion_surjective f r hr hf d
    ((stableHomotopyFunctor d).map (HomotopyPushout.rightConeCollapse f g)
      ((stableHomotopyFunctor d).map (mappingConeInclusion (HomotopyPushout.inr f g)) z))
  have hleft := ConcreteCategory.congr_hom
    (congrArg (fun k => (stableHomotopyFunctor d).map k)
      (HomotopyPushout.inl_coneInclusion_rightConeCollapse f g)) b
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hleft
  let lb : (stableHomotopyFunctor d).obj (HomotopyPushout.prespectrum f g) :=
    (stableHomotopyFunctor d).map (HomotopyPushout.inl f g) b
  have hz : (stableHomotopyFunctor d).map (mappingConeInclusion (HomotopyPushout.inr f g))
      (z - lb) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor d).map (HomotopyPushout.rightConeCollapse f g))).injective
    simp only [map_sub, map_zero, lb, hleft, hb, sub_self]
  obtain ⟨c, he⟩ := (stableMappingCone_exact_target (HomotopyPushout.inr f g) hi d _).mp hz
  refine ⟨(AddCommGrpCat.biprodIsoProd _ _).inv (b, -c), ?_⟩
  have hp := AddCommGrpCat.biprodIsoProd_inv_comp_desc
    ((stableHomotopyFunctor d).map (HomotopyPushout.inl f g))
    (-((stableHomotopyFunctor d).map (HomotopyPushout.inr f g)))
  have hpair := ConcreteCategory.congr_hom hp (b, -c)
  simpa [representative, he, lb] using hpair

include r hr hf hi in
/-- The only relations among the original signed inclusions are the positive overlap image. -/
theorem representative_exact (d : ℤ) :
    Function.Exact (overlap f g d) (representative f g d) := by
  intro x
  constructor
  · intro hx
    let b := (biprod.fst : (stableHomotopyFunctor d).obj B ⊞ (stableHomotopyFunctor d).obj C ⟶ _) x
    let c := (biprod.snd : (stableHomotopyFunctor d).obj B ⊞ (stableHomotopyFunctor d).obj C ⟶ _) x
    have hx' : (stableHomotopyFunctor d).map (HomotopyPushout.inl f g) b -
        (stableHomotopyFunctor d).map (HomotopyPushout.inr f g) c = 0 := by
      simpa [representative, biprod.desc_eq, b, c, sub_eq_add_neg] using hx
    have he := sub_eq_zero.mp hx'
    have hb : (stableHomotopyFunctor d).map (mappingConeInclusion f) b = 0 := by
      have hleft := ConcreteCategory.congr_hom
        (congrArg (fun k => (stableHomotopyFunctor d).map k)
          (HomotopyPushout.inl_coneInclusion_rightConeCollapse f g)) b
      simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hleft
      rw [← hleft, he]
      have hz := (stableMappingCone_exact_target (HomotopyPushout.inr f g) hi d _).mpr ⟨c, rfl⟩
      rw [hz, map_zero]
    obtain ⟨a, ha⟩ := (stableMappingCone_exact_target f hf d b).mp hb
    have hg : (stableHomotopyFunctor d).map g a = c := by
      apply inr_injective f g r hr d
      have hglue := ConcreteCategory.congr_hom
        ((HomotopyPushout.glue f g).stableHomotopyMap_eq d) a
      simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hglue
      exact hglue.symm.trans ((congrArg ((stableHomotopyFunctor d).map
        (HomotopyPushout.inl f g)) ha).trans he)
    refine ⟨a, ?_⟩
    have hfst : (biprod.fst : (stableHomotopyFunctor d).obj B ⊞ (stableHomotopyFunctor d).obj C ⟶ _)
        (overlap f g d a) = b := by
      exact (ConcreteCategory.congr_hom (biprod.lift_fst _ _) a).trans ha
    have hsnd : (biprod.snd : (stableHomotopyFunctor d).obj B ⊞ (stableHomotopyFunctor d).obj C ⟶ _)
        (overlap f g d a) = c := by
      exact (ConcreteCategory.congr_hom (biprod.lift_snd _ _) a).trans hg
    have htotal (y : ((stableHomotopyFunctor d).obj B ⊞
        (stableHomotopyFunctor d).obj C : AddCommGrpCat.{u})) :
        (biprod.inl : (stableHomotopyFunctor d).obj B ⟶ _)
            ((biprod.fst : _ ⟶ (stableHomotopyFunctor d).obj B) y) +
          (biprod.inr : (stableHomotopyFunctor d).obj C ⟶ _)
            ((biprod.snd : _ ⟶ (stableHomotopyFunctor d).obj C) y) = y := by
      exact ConcreteCategory.congr_hom (biprod.total (X := (stableHomotopyFunctor d).obj B)
        (Y := (stableHomotopyFunctor d).obj C)) y
    rw [← htotal (overlap f g d a), hfst, hsnd]
    exact htotal x
  · rintro ⟨a, rfl⟩
    exact ConcreteCategory.congr_hom (overlap_representative f g d) a

/-- The original positive overlap and signed inclusions form an exact short complex. -/
def spanShortComplex (d : ℤ) : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (overlap f g d) (representative f g d) (overlap_representative f g d)

/-- Excision and genuine zero evaluation give the actual span cokernel universal property. -/
def spanIsCokernel (d : ℤ) :
    IsColimit (CokernelCofork.ofπ (representative f g d) (overlap_representative f g d)) := by
  have : Epi ((spanShortComplex f g d).g) := (AddCommGrpCat.epi_iff_surjective _).mpr
    (representative_surjective f g r hr hf hi hc d)
  have he : (spanShortComplex f g d).Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    exact representative_exact f g r hr hf hi d
  exact he.gIsCokernel

/-- In every signed degree the actual span is the cokernel of the positive overlap map. -/
def spanCokernelIso (d : ℤ) : cokernel (overlap f g d) ≅
    (stableHomotopyFunctor d).obj (HomotopyPushout.prespectrum f g) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (spanIsCokernel f g r hr hf hi hc d)

/-- The forward isomorphism preserves the difference of the original chart inclusions. -/
@[reassoc]
theorem spanCokernelIso_π (d : ℤ) : cokernel.π (overlap f g d) ≫
    (spanCokernelIso f g r hr hf hi hc d).hom = representative f g d :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom
    (spanIsCokernel f g r hr hf hi hc d) WalkingParallelPair.one

end KTheory.Bass.TwoChartStable

namespace KTheory.Bass.TwoChartStable

variable (S : Arrow (Arrow LoopPrespectrum.{u}))

/-- The genuine generic inputs needed for the unchanged strict-square span.
The intended finite geometric models discharge the excision and collapse conditions separately.
-/
structure SpanConditions where
  /-- The actual plus-chart zero evaluation. -/
  retraction : S.left.right ⟶ S.left.left
  /-- Evaluation retracts the original polynomial extension. -/
  retraction_eq : S.left.hom ≫ retraction = 𝟙 S.left.left
  /-- Actual plus-arrow cone-to-fiber excision. -/
  plus_excision : IsStableEquivalence (mappingConeFiberComparison S.left.hom)
  /-- Actual right-inclusion cone-to-fiber excision. -/
  right_excision : IsStableEquivalence
    (mappingConeFiberComparison (HomotopyPushout.inr S.left.hom S.hom.left))
  /-- Stability of the unchanged right-inclusion cone collapse. -/
  collapse_stable : IsStableEquivalence (HomotopyPushout.rightConeCollapse S.left.hom S.hom.left)

/-- The original positive diagonal of the two strict-square source legs. -/
def strictOverlap (d : ℤ) := overlap S.left.hom S.hom.left d

/-- The original signed representative into the actual strict-square span. -/
def strictRepresentative (d : ℤ) := representative S.left.hom S.hom.left d

/-- The two original Laurent chart maps, with the classical second-chart minus sign. -/
def chartDifference (d : ℤ) :
    (stableHomotopyFunctor d).obj S.left.right ⊞ (stableHomotopyFunctor d).obj S.right.left ⟶
      (stableHomotopyFunctor d).obj S.right.right :=
  biprod.desc ((stableHomotopyFunctor d).map S.hom.right)
    (-((stableHomotopyFunctor d).map S.right.hom))

/-- The original comparison sends the original signed representative to the original difference.
-/
@[reassoc]
theorem strictRepresentative_comparison (d : ℤ) :
    strictRepresentative S d ≫ (stableHomotopyFunctor d).map (StrictSquare.comparison S) =
      chartDifference S d := by
  apply biprod.hom_ext'
  · simp only [strictRepresentative, representative, biprod.inl_desc_assoc, chartDifference,
      biprod.inl_desc]
    rw [← Functor.map_comp]
    simp [StrictSquare.comparison]
  · simp only [strictRepresentative, representative, biprod.inr_desc_assoc, chartDifference,
      biprod.inr_desc, Preadditive.neg_comp]
    rw [← Functor.map_comp]
    simp [StrictSquare.comparison]

/-- The unchanged strict square makes the Laurent difference kill the positive overlap. -/
@[reassoc]
theorem strictOverlap_chartDifference (d : ℤ) :
    strictOverlap S d ≫ chartDifference S d = 0 := by
  rw [← strictRepresentative_comparison, ← Category.assoc]
  exact (congrArg (fun k => k ≫ (stableHomotopyFunctor d).map (StrictSquare.comparison S))
    (overlap_representative S.left.hom S.hom.left d)).trans zero_comp

/-- The Laurent comparison descended through the actual positive-overlap cokernel. -/
def spanComparison (d : ℤ) : cokernel (strictOverlap S d) ⟶
    (stableHomotopyFunctor d).obj S.right.right :=
  cokernel.desc _ (chartDifference S d) (strictOverlap_chartDifference S d)

@[reassoc (attr := simp)]
theorem spanComparison_π (d : ℤ) :
    cokernel.π (strictOverlap S d) ≫ spanComparison S d = chartDifference S d :=
  cokernel.π_desc _ _ _

/-- Actual span cokernel, in every signed degree, under the displayed geometric inputs. -/
def strictSpanIso (hS : SpanConditions S) (d : ℤ) : cokernel (strictOverlap S d) ≅
    (stableHomotopyFunctor d).obj (StrictSquare.span S) :=
  spanCokernelIso S.left.hom S.hom.left hS.retraction hS.retraction_eq
    hS.plus_excision hS.right_excision hS.collapse_stable d

@[reassoc]
theorem strictSpanIso_π (hS : SpanConditions S) (d : ℤ) :
    cokernel.π (strictOverlap S d) ≫ (strictSpanIso S hS d).hom = strictRepresentative S d :=
  spanCokernelIso_π _ _ _ _ _ _ _ _

/-- The span quotient retains the original comparison, rather than a replacement Laurent map. -/
@[reassoc]
theorem strictSpanIso_comparison (hS : SpanConditions S) (d : ℤ) :
    (strictSpanIso S hS d).hom ≫ (stableHomotopyFunctor d).map (StrictSquare.comparison S) =
      spanComparison S d := by
  apply (cancel_epi (cokernel.π (strictOverlap S d))).mp
  rw [← Category.assoc, strictSpanIso_π, strictRepresentative_comparison, spanComparison_π]

variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T)

/-- The unchanged strict square map acts independently on both original chart groups. -/
def chartMap (d : ℤ) :
    (stableHomotopyFunctor d).obj S.left.right ⊞ (stableHomotopyFunctor d).obj S.right.left ⟶
      (stableHomotopyFunctor d).obj T.left.right ⊞ (stableHomotopyFunctor d).obj T.right.left :=
  biprod.map ((stableHomotopyFunctor d).map a.left.right)
    ((stableHomotopyFunctor d).map a.right.left)

@[reassoc]
theorem strictOverlap_naturality (d : ℤ) :
    strictOverlap S d ≫ chartMap a d =
      (stableHomotopyFunctor d).map a.left.left ≫ strictOverlap T d := by
  apply biprod.hom_ext
  · simp only [strictOverlap, overlap, chartMap, Category.assoc, biprod.map_fst,
      biprod.lift_fst_assoc, biprod.lift_fst, ← Functor.map_comp]
    exact congrArg ((stableHomotopyFunctor d).map) a.left.w.symm
  · simp only [strictOverlap, overlap, chartMap, Category.assoc, biprod.map_snd,
      biprod.lift_snd_assoc, biprod.lift_snd, ← Functor.map_comp]
    exact congrArg ((stableHomotopyFunctor d).map) (congrArg (fun k => k.left) a.w).symm

@[reassoc]
theorem chartDifference_naturality (d : ℤ) :
    chartMap a d ≫ chartDifference T d =
      chartDifference S d ≫ (stableHomotopyFunctor d).map a.right.right := by
  apply biprod.hom_ext'
  · simp only [chartMap, chartDifference, biprod.inl_map_assoc, biprod.inl_desc_assoc,
      biprod.inl_desc, ← Functor.map_comp]
    exact congrArg ((stableHomotopyFunctor d).map) (congrArg (fun k => k.right) a.w)
  · simp only [chartMap, chartDifference, biprod.inr_map_assoc, biprod.inr_desc_assoc,
      biprod.inr_desc, Preadditive.comp_neg, Preadditive.neg_comp, ← Functor.map_comp]
    exact congrArg (fun k => -((stableHomotopyFunctor d).map k)) a.right.w

/-- Strict square maps preserve the signed original pushout representatives. -/
@[reassoc]
theorem strictRepresentative_naturality (d : ℤ) :
    chartMap a d ≫ strictRepresentative T d =
      strictRepresentative S d ≫ (stableHomotopyFunctor d).map (StrictSquare.spanMap a) := by
  apply biprod.hom_ext'
  · simp only [chartMap, strictRepresentative, representative, biprod.inl_map_assoc,
      biprod.inl_desc_assoc, biprod.inl_desc, ← Functor.map_comp]
    exact congrArg ((stableHomotopyFunctor d).map)
      (HomotopyPushout.inl_map _ _ _ _ _ _ _ _ _).symm
  · simp only [chartMap, strictRepresentative, representative, biprod.inr_map_assoc,
      biprod.inr_desc_assoc, biprod.inr_desc, Preadditive.comp_neg, Preadditive.neg_comp,
      ← Functor.map_comp]
    exact congrArg (fun k => -((stableHomotopyFunctor d).map k))
      (HomotopyPushout.inr_map _ _ _ _ _ _ _ _ _).symm

/-- The genuine induced map of positive-overlap cokernels. -/
def spanCokernelMap (d : ℤ) : cokernel (strictOverlap S d) ⟶ cokernel (strictOverlap T d) :=
  cokernel.map _ _ ((stableHomotopyFunctor d).map a.left.left) (chartMap a d)
    (strictOverlap_naturality a d)

@[reassoc (attr := simp)]
theorem spanCokernelMap_π (d : ℤ) :
    cokernel.π (strictOverlap S d) ≫ spanCokernelMap a d =
      chartMap a d ≫ cokernel.π (strictOverlap T d) := by
  simp [spanCokernelMap]

/-- The quotient comparison is natural for the original strict square map. -/
@[reassoc]
theorem spanComparison_naturality (d : ℤ) :
    spanCokernelMap a d ≫ spanComparison T d =
      spanComparison S d ≫ (stableHomotopyFunctor d).map a.right.right := by
  apply (cancel_epi (cokernel.π (strictOverlap S d))).mp
  rw [← Category.assoc, spanCokernelMap_π, Category.assoc, spanComparison_π,
    ← Category.assoc, spanComparison_π, chartDifference_naturality]

/-- The actual span isomorphism is natural; no compatibility of chosen retractions is needed. -/
@[reassoc]
theorem strictSpanIso_naturality (hS : SpanConditions S) (hT : SpanConditions T) (d : ℤ) :
    spanCokernelMap a d ≫ (strictSpanIso T hT d).hom =
      (strictSpanIso S hS d).hom ≫ (stableHomotopyFunctor d).map (StrictSquare.spanMap a) := by
  apply (cancel_epi (cokernel.π (strictOverlap S d))).mp
  rw [← Category.assoc, spanCokernelMap_π, Category.assoc, strictSpanIso_π,
    ← Category.assoc, strictSpanIso_π, strictRepresentative_naturality]

end KTheory.Bass.TwoChartStable
