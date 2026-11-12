/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.TwoChartStableSpan
public import Colib.Topology.Prespectrum.ConeStableNaturality
public import Colib.Topology.Prespectrum.StableShift
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
Source: `Quillen/KTheory/Bass/TwoChartStableSequence.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The natural spectral two-chart Bass row

For the original strict square, actual zero evaluation and explicitly retained excision give
`0 → coker Δ_(d+1) → π_d(BE) → ker(coker a_d → Laurent_d) → 0` in every integer degree.
The left arrow is the original Laurent cone inclusion followed by the genuine signed
parameter-loop shift. Naturality uses the original strict square and its original cone map.

The right term is the kernel of the induced positive-overlap cokernel comparison. Its further
description as `ker Δ_d / im a_d` is an algebraic quotient description of this same term.
No polynomial zero section or finite-model excision is constructed in this generic owner.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open CategoryTheory CategoryTheory.Limits Topology.LoopPrespectrum
universe u
namespace KTheory.Bass.TwoChartStable

variable (S : Arrow (Arrow LoopPrespectrum.{u}))

/-- The actual inputs for the spectral row, including excision of the original comparison. -/
structure SpectralConditions extends SpanConditions S where
  /-- Excision for the unchanged span-to-Laurent comparison. -/
  comparison_excision : IsStableEquivalence (mappingConeFiberComparison (StrictSquare.comparison S))

/-- Degree d of the original parameter-looped strict-square cone. -/
def bassGroup (d : ℤ) := (stableHomotopyFunctor d).obj (strictSquareLoopedConeFunctor.obj S)

/-- The genuine signed parameter-loop shift on this same original cone. -/
def bassShift (d : ℤ) : bassGroup S d ≅
    (stableHomotopyFunctor (d + 1)).obj (mappingCone (StrictSquare.comparison S)) :=
  parameterStableHomotopyIso (mappingCone (StrictSquare.comparison S)) d

/-- The right end is the kernel of the comparison induced on the positive-overlap cokernel. -/
def bassRightGroup (d : ℤ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (AddMonoidHom.ker (spanComparison S d).hom)

/-- The literal inclusion of that kernel into the actual overlap cokernel. -/
def bassRightInclusion (d : ℤ) : bassRightGroup S d ⟶ cokernel (strictOverlap S d) :=
  AddCommGrpCat.ofHom (AddSubgroup.subtype _)

/-- The positive overlap and original Laurent difference form the original chart complex. -/
def chartComplex (d : ℤ) : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (strictOverlap S d) (chartDifference S d) (strictOverlap_chartDifference S d)

/-- Homology of the original chart complex is the actual induced-cokernel kernel. -/
def chartHomologyRightIso (d : ℤ) : (chartComplex S d).homology ≅ bassRightGroup S d :=
  (ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel (chartComplex S d)).homologyIso ≪≫
    AddCommGrpCat.kernelIsoKer (spanComparison S d)

/-- The right end is the quotient of the original difference kernel by the positive overlap image.
The image is taken after the canonical lift of the positive diagonal into that kernel.
-/
def bassRightQuotientIso (d : ℤ) : bassRightGroup S d ≅
    AddCommGrpCat.of ((AddMonoidHom.ker (chartDifference S d).hom) ⧸
      AddMonoidHom.range (chartComplex S d).abToCycles) :=
  (asIso (ShortComplex.leftRightHomologyComparison' (chartComplex S d).abLeftHomologyData
    (ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel (chartComplex S d))) ≪≫
      AddCommGrpCat.kernelIsoKer (spanComparison S d)).symm

/-- A difference-kernel representative enters the same positive-overlap cokernel on both sides.
This fixes the quotient identification to the original chart maps.
-/
@[reassoc]
theorem bassRightQuotientIso_π (d : ℤ) :
    AddCommGrpCat.ofHom (QuotientAddGroup.mk'
      (AddMonoidHom.range (chartComplex S d).abToCycles)) ≫
        (bassRightQuotientIso S d).inv ≫ bassRightInclusion S d =
      AddCommGrpCat.ofHom (AddSubgroup.subtype (AddMonoidHom.ker (chartDifference S d).hom)) ≫
        cokernel.π (strictOverlap S d) := by
  simp only [bassRightQuotientIso, Iso.symm_inv, Iso.trans_hom, asIso_hom,
    Category.assoc, bassRightInclusion]
  rw [AddCommGrpCat.kernelIsoKer_hom_comp_subtype]
  exact ShortComplex.π_leftRightHomologyComparison'_ι (chartComplex S d).abLeftHomologyData
    (ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel (chartComplex S d))

/-- Original chart middle exactness kills the actual right term of the spectral row. -/
theorem bassRightGroup_isZero_of_chart_exact (d : ℤ)
    (h : Function.Exact (strictOverlap S d) (chartDifference S d)) :
    IsZero (bassRightGroup S d) := by
  have he : (chartComplex S d).Exact := (ShortComplex.ab_exact_iff_function_exact _).mpr h
  exact ((chartComplex S d).exact_iff_isZero_homology.mp he).of_iso
    (chartHomologyRightIso S d).symm

instance bassRightInclusion_mono (d : ℤ) : Mono (bassRightInclusion S d) :=
  (AddCommGrpCat.mono_iff_injective _).mpr Subtype.val_injective

variable (hS : SpectralConditions S)

include hS in
/-- The unchanged stable comparison followed by its unchanged cone inclusion is zero. -/
@[reassoc]
theorem comparison_coneInclusion (d : ℤ) :
    (stableHomotopyFunctor d).map (StrictSquare.comparison S) ≫
      (stableHomotopyFunctor d).map (mappingConeInclusion (StrictSquare.comparison S)) = 0 := by
  ext x
  exact (stableMappingCone_exact_target (StrictSquare.comparison S) hS.comparison_excision d _).mpr
    ⟨x, rfl⟩

/-- The Laurent cokernel enters through the original cone inclusion and actual inverse shift. -/
def bassLeft (d : ℤ) : cokernel (chartDifference S (d + 1)) ⟶ bassGroup S d :=
  cokernel.desc _ ((stableHomotopyFunctor (d + 1)).map
    (mappingConeInclusion (StrictSquare.comparison S)) ≫ (bassShift S d).inv) (by
      rw [← strictRepresentative_comparison, Category.assoc, ← Category.assoc
        ((stableHomotopyFunctor (d + 1)).map (StrictSquare.comparison S)),
        comparison_coneInclusion S hS, zero_comp, comp_zero])

/-- Every original Laurent representative uses the unchanged cone and signed shift. -/
@[reassoc]
theorem bassLeft_π (d : ℤ) :
    cokernel.π (chartDifference S (d + 1)) ≫ bassLeft S hS d =
      (stableHomotopyFunctor (d + 1)).map (mappingConeInclusion (StrictSquare.comparison S)) ≫
        (bassShift S d).inv := cokernel.π_desc _ _ _

@[reassoc]
theorem bassLeft_π_shift (d : ℤ) :
    cokernel.π (chartDifference S (d + 1)) ≫ bassLeft S hS d ≫ (bassShift S d).hom =
      (stableHomotopyFunctor (d + 1)).map (mappingConeInclusion (StrictSquare.comparison S)) := by
  rw [← Category.assoc, bassLeft_π, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original signed cone boundary, expressed in the original span quotient. -/
def bassBoundary (d : ℤ) : bassGroup S d ⟶ cokernel (strictOverlap S d) :=
  (bassShift S d).hom ≫
    stableMappingConeConnecting (StrictSquare.comparison S) hS.comparison_excision d ≫
      (strictSpanIso S hS.toSpanConditions d).inv

/-- The actual boundary lands in the kernel of the actual Laurent comparison. -/
@[reassoc]
theorem bassBoundary_spanComparison (d : ℤ) : bassBoundary S hS d ≫ spanComparison S d = 0 := by
  simp only [bassBoundary, Category.assoc, ← strictSpanIso_comparison S hS.toSpanConditions d,
    Iso.inv_hom_id_assoc]
  have hz : stableMappingConeConnecting (StrictSquare.comparison S) hS.comparison_excision d ≫
      (stableHomotopyFunctor d).map (StrictSquare.comparison S) = 0 := by
    ext x
    exact (stableMappingConeConnecting_exact_source (StrictSquare.comparison S)
      hS.comparison_excision d _).mpr ⟨x, rfl⟩
  rw [hz, comp_zero]

/-- The original signed boundary as a homomorphism to the actual right-end kernel. -/
def bassRight (d : ℤ) : bassGroup S d ⟶ bassRightGroup S d :=
  AddCommGrpCat.ofHom
    { toFun := fun x => ⟨bassBoundary S hS d x,
        ConcreteCategory.congr_hom (bassBoundary_spanComparison S hS d) x⟩
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' := by intro x y; apply Subtype.ext; exact map_add _ x y }

/-- The right arrow is precisely the original cone boundary followed by the inverse span quotient.
-/
@[reassoc]
theorem bassRight_inclusion (d : ℤ) :
    bassRight S hS d ≫ bassRightInclusion S d = bassBoundary S hS d := by
  ext x
  rfl

include hS in
/-- The original spectral left arrow is injective, using all-degree chart generation. -/
theorem bassLeft_injective (d : ℤ) : Function.Injective (bassLeft S hS d) := by
  have hz (x : (cokernel (chartDifference S (d + 1)) : AddCommGrpCat.{u}))
      (hx : bassLeft S hS d x = 0) : x = 0 := by
    obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
      (cokernel.π (chartDifference S (d + 1)))).mp inferInstance x
    have hi : (stableHomotopyFunctor (d + 1)).map
        (mappingConeInclusion (StrictSquare.comparison S)) z = 0 := by
      have he := ConcreteCategory.congr_hom (bassLeft_π_shift S hS d) z
      simp only [ConcreteCategory.comp_apply] at he
      rw [hx, map_zero] at he
      exact he.symm
    obtain ⟨y, hy⟩ := (stableMappingCone_exact_target (StrictSquare.comparison S)
      hS.comparison_excision (d + 1) z).mp hi
    obtain ⟨v, hv⟩ := representative_surjective S.left.hom S.hom.left
      hS.retraction hS.retraction_eq hS.plus_excision hS.right_excision hS.collapse_stable (d + 1) y
    have he : chartDifference S (d + 1) v = z := by
      have hp := ConcreteCategory.congr_hom (strictRepresentative_comparison S (d + 1)) v
      simp only [ConcreteCategory.comp_apply] at hp
      exact hp.symm.trans ((congrArg ((stableHomotopyFunctor (d + 1)).map
        (StrictSquare.comparison S)) hv).trans hy)
    rw [← he]
    exact ConcreteCategory.congr_hom (cokernel.condition (chartDifference S (d + 1))) v
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

/-- The original boundary is surjective onto the kernel of the actual quotient comparison. -/
theorem bassRight_surjective (d : ℤ) : Function.Surjective (bassRight S hS d) := by
  intro y
  have hy : (stableHomotopyFunctor d).map (StrictSquare.comparison S)
      ((strictSpanIso S hS.toSpanConditions d).hom y.val) = 0 :=
    (ConcreteCategory.congr_hom (strictSpanIso_comparison S hS.toSpanConditions d) y.val).trans
      y.property
  obtain ⟨z, hz⟩ := (stableMappingConeConnecting_exact_source (StrictSquare.comparison S)
    hS.comparison_excision d _).mp hy
  refine ⟨(bassShift S d).inv z, ?_⟩
  apply Subtype.ext
  change bassBoundary S hS d ((bassShift S d).inv z) = y.val
  have he : (bassShift S d).inv ≫ bassBoundary S hS d =
      stableMappingConeConnecting (StrictSquare.comparison S) hS.comparison_excision d ≫
        (strictSpanIso S hS.toSpanConditions d).inv := by
    simp only [bassBoundary, Iso.inv_hom_id_assoc]
  calc
    _ = (strictSpanIso S hS.toSpanConditions d).inv
        (stableMappingConeConnecting (StrictSquare.comparison S) hS.comparison_excision d z) :=
      ConcreteCategory.congr_hom he z
    _ = (strictSpanIso S hS.toSpanConditions d).inv
        ((strictSpanIso S hS.toSpanConditions d).hom y.val) :=
      congrArg (strictSpanIso S hS.toSpanConditions d).inv hz
    _ = y.val := ConcreteCategory.congr_hom (strictSpanIso S hS.toSpanConditions d).hom_inv_id y.val

/-- The displayed spectral arrows compose to zero through the unchanged cone sequence. -/
@[reassoc]
theorem bassLeft_right (d : ℤ) : bassLeft S hS d ≫ bassRight S hS d = 0 := by
  apply (cancel_mono (bassRightInclusion S d)).mp
  rw [Category.assoc, bassRight_inclusion, zero_comp]
  apply (cancel_epi (cokernel.π (chartDifference S (d + 1)))).mp
  simp only [bassBoundary, bassLeft_π_shift_assoc, comp_zero]
  have hz : (stableHomotopyFunctor (d + 1)).map
      (mappingConeInclusion (StrictSquare.comparison S)) ≫
        stableMappingConeConnecting (StrictSquare.comparison S) hS.comparison_excision d = 0 := by
    ext x
    exact (stableMappingConeConnecting_exact_cone (StrictSquare.comparison S)
      hS.comparison_excision d _).mpr ⟨x, rfl⟩
  rw [← Category.assoc, hz, zero_comp]

/-- Exactness at the original looped cone, with its original left and right arrows. -/
theorem bassRow_exact (d : ℤ) : Function.Exact (bassLeft S hS d) (bassRight S hS d) := by
  intro x
  constructor
  · intro hx
    have hb : bassBoundary S hS d x = 0 := by
      have he := ConcreteCategory.congr_hom (bassRight_inclusion S hS d) x
      simp only [ConcreteCategory.comp_apply] at he
      rw [hx, map_zero] at he
      exact he.symm
    have hc : stableMappingConeConnecting (StrictSquare.comparison S)
        hS.comparison_excision d ((bassShift S d).hom x) = 0 := by
      have he : bassBoundary S hS d ≫ (strictSpanIso S hS.toSpanConditions d).hom =
          (bassShift S d).hom ≫ stableMappingConeConnecting (StrictSquare.comparison S)
            hS.comparison_excision d := by
        simp only [bassBoundary, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have hv := ConcreteCategory.congr_hom he x
      simp only [ConcreteCategory.comp_apply] at hv
      rw [hb, map_zero] at hv
      exact hv.symm
    obtain ⟨z, hz⟩ := (stableMappingConeConnecting_exact_cone (StrictSquare.comparison S)
      hS.comparison_excision d _).mp hc
    refine ⟨cokernel.π (chartDifference S (d + 1)) z, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (bassShift S d).hom).injective
    exact (ConcreteCategory.congr_hom (bassLeft_π_shift S hS d) z).trans hz
  · rintro ⟨y, rfl⟩
    exact ConcreteCategory.congr_hom (bassLeft_right S hS d) y

/-- The actual all-degree spectral Bass short complex. -/
def bassSequence (d : ℤ) : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (bassLeft S hS d) (bassRight S hS d) (bassLeft_right S hS d)

/-- The original row is short exact in every signed degree under the displayed actual inputs. -/
theorem bassSequence_shortExact (d : ℤ) : (bassSequence S hS d).ShortExact := by
  have : Mono (bassSequence S hS d).f := (AddCommGrpCat.mono_iff_injective _).mpr
    (bassLeft_injective S hS d)
  have : Epi (bassSequence S hS d).g := (AddCommGrpCat.epi_iff_surjective _).mpr
    (bassRight_surjective S hS d)
  refine ⟨?_⟩
  rw [ShortComplex.ab_exact_iff_function_exact]
  exact bassRow_exact S hS d

end KTheory.Bass.TwoChartStable

namespace KTheory.Bass.TwoChartStable

variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T)

/-- The original difference square induces the left-end cokernel map. -/
def chartCokernelMap (d : ℤ) : cokernel (chartDifference S d) ⟶ cokernel (chartDifference T d) :=
  cokernel.map _ _ (chartMap a d) ((stableHomotopyFunctor d).map a.right.right)
    (chartDifference_naturality a d).symm

@[reassoc (attr := simp)]
theorem chartCokernelMap_π (d : ℤ) :
    cokernel.π (chartDifference S d) ≫ chartCokernelMap a d =
      (stableHomotopyFunctor d).map a.right.right ≫ cokernel.π (chartDifference T d) := by
  simp [chartCokernelMap]

/-- The actual original B map, obtained from the original strict-square cone functor. -/
def bassMap (d : ℤ) : bassGroup S d ⟶ bassGroup T d :=
  (stableHomotopyFunctor d).map (strictSquareLoopedConeFunctor.map a)

/-- The right-end map is the restriction of the original positive-overlap cokernel map. -/
def bassRightMap (d : ℤ) : bassRightGroup S d ⟶ bassRightGroup T d :=
  AddCommGrpCat.ofHom
    { toFun := fun x => ⟨spanCokernelMap a d x.val, by
        have he := ConcreteCategory.congr_hom (spanComparison_naturality a d) x.val
        simp only [ConcreteCategory.comp_apply] at he
        exact he.trans (by rw [x.property, map_zero])⟩
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' := by intro x y; apply Subtype.ext; exact map_add _ x.val y.val }

@[reassoc]
theorem bassRightMap_inclusion (d : ℤ) :
    bassRightMap a d ≫ bassRightInclusion T d = bassRightInclusion S d ≫ spanCokernelMap a d := by
  ext x
  rfl

/-- The genuine signed shift is natural for the original square-induced cone map. -/
@[reassoc]
theorem bassMap_shift (d : ℤ) :
    bassMap a d ≫ (bassShift T d).hom = (bassShift S d).hom ≫
      (stableHomotopyFunctor (d + 1)).map (mappingConeMap (strictSquareComparisonFunctor.map a)) :=
  parameterStableHomotopyIso_naturality (mappingConeMap (strictSquareComparisonFunctor.map a)) d

@[reassoc]
theorem bassMap_shift_inv (d : ℤ) :
    (bassShift S d).inv ≫ bassMap a d =
      (stableHomotopyFunctor (d + 1)).map (mappingConeMap (strictSquareComparisonFunctor.map a)) ≫
        (bassShift T d).inv :=
  parameterStableHomotopyIso_inv_naturality (mappingConeMap (strictSquareComparisonFunctor.map a)) d

/-- The actual Laurent side and original cone map preserve the original cone inclusion. -/
@[reassoc]
theorem comparisonConeMap_inclusion (d : ℤ) :
    (stableHomotopyFunctor d).map a.right.right ≫
      (stableHomotopyFunctor d).map (mappingConeInclusion (StrictSquare.comparison T)) =
        (stableHomotopyFunctor d).map (mappingConeInclusion (StrictSquare.comparison S)) ≫
          (stableHomotopyFunctor d).map (mappingConeMap (strictSquareComparisonFunctor.map a)) := by
  have h := (mappingConeInclusionSquare (strictSquareComparisonFunctor.map a)).w
  change a.right.right ≫ mappingConeInclusion (StrictSquare.comparison T) =
    mappingConeInclusion (StrictSquare.comparison S) ≫
      mappingConeMap (strictSquareComparisonFunctor.map a) at h
  have hm := congrArg ((stableHomotopyFunctor d).map) h
  rw [Functor.map_comp, Functor.map_comp] at hm
  exact hm

variable (hS : SpectralConditions S) (hT : SpectralConditions T)

/-- Naturality of the original Laurent inclusion and original signed loop shift. -/
@[reassoc]
theorem bassLeft_naturality (d : ℤ) :
    chartCokernelMap a (d + 1) ≫ bassLeft T hT d = bassLeft S hS d ≫ bassMap a d := by
  apply (cancel_epi (cokernel.π (chartDifference S (d + 1)))).mp
  rw [chartCokernelMap_π_assoc, bassLeft_π, bassLeft_π_assoc,
    comparisonConeMap_inclusion_assoc, bassMap_shift_inv]

/-- Inverse span transport is natural for the original span map, independently of the retractions.
-/
@[reassoc]
theorem strictSpanIso_inv_naturality (d : ℤ) :
    (stableHomotopyFunctor d).map (StrictSquare.spanMap a) ≫
      (strictSpanIso T hT.toSpanConditions d).inv =
        (strictSpanIso S hS.toSpanConditions d).inv ≫ spanCokernelMap a d := by
  apply (cancel_mono (strictSpanIso T hT.toSpanConditions d).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [strictSpanIso_naturality a hS.toSpanConditions hT.toSpanConditions d,
    Iso.inv_hom_id_assoc]

/-- The actual B map preserves the original cone boundary expressed in the span quotient. -/
@[reassoc]
theorem bassBoundary_naturality (d : ℤ) :
    bassMap a d ≫ bassBoundary T hT d = bassBoundary S hS d ≫ spanCokernelMap a d := by
  calc
    _ = (bassMap a d ≫ (bassShift T d).hom) ≫
        stableMappingConeConnecting (StrictSquare.comparison T) hT.comparison_excision d ≫
          (strictSpanIso T hT.toSpanConditions d).inv := by
      simp only [bassBoundary, Category.assoc]
    _ = ((bassShift S d).hom ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeMap (strictSquareComparisonFunctor.map a))) ≫
          stableMappingConeConnecting (StrictSquare.comparison T) hT.comparison_excision d ≫
            (strictSpanIso T hT.toSpanConditions d).inv := by rw [bassMap_shift]
    _ = (bassShift S d).hom ≫
        (stableMappingConeConnecting (StrictSquare.comparison S) hS.comparison_excision d ≫
          (stableHomotopyFunctor d).map (StrictSquare.spanMap a)) ≫
            (strictSpanIso T hT.toSpanConditions d).inv := by
      let sq : Arrow.mk (StrictSquare.comparison S) ⟶ Arrow.mk (StrictSquare.comparison T) :=
        Arrow.homMk (StrictSquare.spanMap a) a.right.right (StrictSquare.comparison_naturality a)
      have hn := stableMappingConeConnecting_naturality sq
        hS.comparison_excision hT.comparison_excision d
      change (stableHomotopyFunctor (d + 1)).map (mappingConeMap sq) ≫
          stableMappingConeConnecting (StrictSquare.comparison T) hT.comparison_excision d =
        stableMappingConeConnecting (StrictSquare.comparison S) hS.comparison_excision d ≫
          (stableHomotopyFunctor d).map (StrictSquare.spanMap a) at hn
      have hs : sq = strictSquareComparisonFunctor.map a := rfl
      rw [hs] at hn
      simpa only [Category.assoc] using congrArg (fun k => (bassShift S d).hom ≫ k ≫
        (strictSpanIso T hT.toSpanConditions d).inv) hn
    _ = (bassShift S d).hom ≫
        stableMappingConeConnecting (StrictSquare.comparison S) hS.comparison_excision d ≫
          ((stableHomotopyFunctor d).map (StrictSquare.spanMap a) ≫
            (strictSpanIso T hT.toSpanConditions d).inv) := by simp only [Category.assoc]
    _ = _ := by
      rw [strictSpanIso_inv_naturality a hS hT d]
      simp only [bassBoundary, Category.assoc]

/-- Naturality of the original right arrow for the actual B map and overlap-cokernel map. -/
@[reassoc]
theorem bassRight_naturality (d : ℤ) :
    bassMap a d ≫ bassRight T hT d = bassRight S hS d ≫ bassRightMap a d := by
  apply (cancel_mono (bassRightInclusion T d)).mp
  rw [Category.assoc, bassRight_inclusion, Category.assoc, bassRightMap_inclusion,
    ← Category.assoc, bassRight_inclusion, bassBoundary_naturality]

/-- Every original strict-square map gives a morphism of the actual spectral Bass rows. -/
def bassSequenceMap (d : ℤ) : bassSequence S hS d ⟶ bassSequence T hT d where
  τ₁ := chartCokernelMap a (d + 1)
  τ₂ := bassMap a d
  τ₃ := bassRightMap a d
  comm₁₂ := bassLeft_naturality a hS hT d
  comm₂₃ := bassRight_naturality a hS hT d

end KTheory.Bass.TwoChartStable
