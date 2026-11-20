/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.SpectralSequence.FiniteConvergence
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.StageZero
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.AbsoluteWindows
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.Pages
import all Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Stages

/-!
# Finite convergence of the motivic coniveau spectral sequence

The filtration on represented cohomology is the image of the original tower of
closed-support cohomology. The large-page terms are its associated graded pieces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian.SpectralObject CategoryTheory.ComposableArrows
open CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite OrderDual TopologicalSpace

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]
  (X : SmoothSite (Spec (.of k))) (K : EffectiveMotivesMinus k)

/-- The represented cohomology of the original effective smooth motive. -/
abbrev coniveauAbutment (n : ℤ) : AddCommGrpCat.{w'} :=
  AddCommGrpCat.of ((effectiveSmoothMotive k).obj X ⟶ K⟦n⟧)

/-- The support stage maps to represented cohomology through stage zero. -/
@[no_expose]
def coniveauCohomologyToAbutment (n : ℤ) (p : ℕ) :
    coniveauCohomology k X K n p ⟶ coniveauAbutment k X K n :=
  coniveauCohomologyTransition k X K n (Nat.zero_le p) ≫
    (coniveauCohomologyZeroIso k X K n).hom

/-- The coniveau filtration is the image of cohomology with supports of codimension at least `p`. -/
def coniveauFiltration (n : ℤ) (p : ℕ) : Subobject (coniveauAbutment k X K n) :=
  imageSubobject (coniveauCohomologyToAbutment k X K n p)

/-- Successive weakenings of support conditions agree with their composite. -/
theorem coniveauCohomologyTransition_comp (n : ℤ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    coniveauCohomologyTransition k X K n hbc ≫ coniveauCohomologyTransition k X K n hab =
      coniveauCohomologyTransition k X K n (hab.trans hbc) := by
  let f : op c ⟶ op b := (homOfLE hbc).op
  let g : op b ⟶ op a := (homOfLE hab).op
  exact ((coniveauCohomologyTower k X K n).map_comp f g).symm

private theorem coniveauTransition_comp_toAbutment (n : ℤ) {p q : ℕ} (hpq : p ≤ q) :
    coniveauCohomologyTransition k X K n hpq ≫ coniveauCohomologyToAbutment k X K n p =
      coniveauCohomologyToAbutment k X K n q := by
  simp only [coniveauCohomologyToAbutment, ← Category.assoc, coniveauCohomologyTransition_comp]

/-- The coniveau filtration decreases with the codimension bound. -/
theorem coniveauFiltration_antitone (n : ℤ) : Antitone (coniveauFiltration k X K n) := by
  intro p q hpq
  unfold coniveauFiltration
  refine imageSubobject_le (coniveauCohomologyToAbutment k X K n q)
    (coniveauCohomologyTransition k X K n hpq ≫
      factorThruImageSubobject (coniveauCohomologyToAbutment k X K n p)) ?_
  rw [Category.assoc, imageSubobject_arrow_comp, coniveauTransition_comp_toAbutment]

/-- A support stage surjecting onto stage zero gives the whole abutment. -/
theorem coniveauFiltration_eq_top_of_epi (n : ℤ) (p : ℕ)
    (h : Epi (coniveauCohomologyTransition k X K n (Nat.zero_le p))) :
    coniveauFiltration k X K n p = ⊤ := by
  have : Epi (coniveauCohomologyToAbutment k X K n p) := by
    unfold coniveauCohomologyToAbutment
    infer_instance
  exact (Subobject.epi_iff_mk_eq_top _).1 (epi_image_of_epi _)

/-- Stage zero of the coniveau filtration is all represented cohomology. -/
@[simp]
theorem coniveauFiltration_zero (n : ℤ) : coniveauFiltration k X K n 0 = ⊤ := by
  apply coniveauFiltration_eq_top_of_epi
  have h : coniveauCohomologyTransition k X K n (Nat.zero_le 0) = 𝟙 _ := by
    apply colimit.hom_ext
    intro Z
    simp only [ι_coniveauCohomologyTransition, Category.comp_id]
    rfl
  rw [h]
  infer_instance

/-- A zero support stage gives a zero stage of the filtration on the abutment. -/
theorem coniveauFiltration_eq_bot_of_isZero (n : ℤ) (p : ℕ)
    (h : IsZero (coniveauCohomology k X K n p)) : coniveauFiltration k X K n p = ⊥ := by
  apply Subobject.mk_eq_bot_iff_zero.2
  exact image.ι_zero' (h.eq_of_src _ _)

/-- The coniveau filtration is zero above any natural upper bound for the dimension. -/
theorem coniveauFiltration_eq_bot_of_dimension_lt (n : ℤ) {d p : ℕ}
    (hX : topologicalKrullDim X.left ≤ d) (h : d < p) : coniveauFiltration k X K n p = ⊥ :=
  coniveauFiltration_eq_bot_of_isZero k X K n p
    (isZero_coniveauCohomology_above_dimension k X K n hX h)

/-- The map from filtration stage `p` to the quotient by stage `p+1`. -/
abbrev coniveauAssociatedGradedMap (n : ℤ) (p : ℕ) :
    (coniveauFiltration k X K n p : AddCommGrpCat.{w'}) ⟶
      cokernel (coniveauFiltration k X K n (p + 1)).arrow :=
  (coniveauFiltration k X K n p).arrow ≫
    cokernel.π (coniveauFiltration k X K n (p + 1)).arrow

/-- The associated graded piece, as the image of stage `p` in the quotient of the abutment. -/
abbrev coniveauAssociatedGraded (n : ℤ) (p : ℕ) : AddCommGrpCat.{w'} :=
  image (coniveauAssociatedGradedMap k X K n p)

/-- The image description of the graded piece identifies it with `Fᵖ / Fᵖ⁺¹`. -/
@[colib_tag "COL-1318"]
def coniveauAssociatedGradedIsoCokernel (n : ℤ) (p : ℕ) :
    coniveauAssociatedGraded k X K n p ≅ cokernel (Subobject.ofLE _ _
      (coniveauFiltration_antitone k X K n (Nat.le_succ p))) :=
  (Subobject.cokernelOfLEIsoImage _).symm

/-- If the next support stage vanishes and the indicated stage surjects onto
stage zero, its associated graded piece is the whole abutment. -/
@[no_expose]
def coniveauAssociatedGradedIsoOfIsZeroOfEpi (n : ℤ) (p : ℕ)
    (hzero : IsZero (coniveauCohomology k X K n (p + 1)))
    (hepi : Epi (coniveauCohomologyTransition k X K n (Nat.zero_le p))) :
    coniveauAssociatedGraded k X K n p ≅ coniveauAbutment k X K n := by
  let f := (coniveauFiltration k X K n p).arrow
  let g := (coniveauFiltration k X K n (p + 1)).arrow
  have : Epi (coniveauCohomologyToAbutment k X K n p) := by
    unfold coniveauCohomologyToAbutment
    infer_instance
  have : Epi f := epi_of_epi_fac (imageSubobject_arrow_comp
    (coniveauCohomologyToAbutment k X K n p))
  have : IsIso f := isIso_of_mono_of_epi f
  have hg : g = 0 := by
    dsimp [g]
    rw [coniveauFiltration_eq_bot_of_isZero k X K n (p + 1) hzero, Subobject.bot_arrow]
  have : Mono (cokernel.π g) := (ShortComplex.exact_cokernel g).mono_g hg
  exact imageMonoIsoSource (f ≫ cokernel.π g) ≪≫ asIso f

private theorem isZero_coniveauAssociatedGraded_of_dimension_lt (n : ℤ) {d p : ℕ}
    (hX : topologicalKrullDim X.left ≤ d) (h : d < p) :
    IsZero (coniveauAssociatedGraded k X K n p) := by
  have hf : (coniveauFiltration k X K n p).arrow = 0 := by
    rw [coniveauFiltration_eq_bot_of_dimension_lt k X K n hX h, Subobject.bot_arrow]
  have hzero : coniveauAssociatedGradedMap k X K n p = 0 := by
    simp only [coniveauAssociatedGradedMap, hf, zero_comp]
  exact (isZero_zero _).of_iso (imageZero' hzero)

private abbrev coniveauAbutmentToWindow (n : ℤ) (b : ℕ) :
    coniveauAbutment k X K n ⟶ coniveauRelativeSupportCohomology k X K n 0 b :=
  (coniveauCohomologyZeroIso k X K n).inv ≫ coniveauCohomologyToWindow k X K n 0 b

private lemma coniveauCohomologyToAbutment_comp_toWindow (n : ℤ) (b : ℕ) :
    coniveauCohomologyToAbutment k X K n b ≫ coniveauAbutmentToWindow k X K n b = 0 := by
  simp only [coniveauCohomologyToAbutment, coniveauAbutmentToWindow, Category.assoc,
    Iso.hom_inv_id_assoc, coniveauCohomologyTransition_comp_toWindow]

private def coniveauQuotientWindowComplex (n : ℤ) (b : ℕ) : ShortComplex AddCommGrpCat.{w'} :=
  ShortComplex.mk (coniveauFiltration k X K n b).arrow (coniveauAbutmentToWindow k X K n b)
    (imageSubobject_arrow_comp_eq_zero (coniveauCohomologyToAbutment_comp_toWindow k X K n b))

private theorem coniveauQuotientWindowComplex_exact (n : ℤ) (b : ℕ) :
    (coniveauQuotientWindowComplex k X K n b).Exact := by
  let S := ShortComplex.mk (coniveauCohomologyTransition k X K n (Nat.zero_le b))
    (coniveauCohomologyToWindow k X K n 0 b)
    (coniveauCohomologyTransition_comp_toWindow k X K n (Nat.zero_le b))
  let φ : S ⟶ coniveauQuotientWindowComplex k X K n b :=
    { τ₁ := factorThruImageSubobject (coniveauCohomologyToAbutment k X K n b)
      τ₂ := (coniveauCohomologyZeroIso k X K n).hom
      τ₃ := 𝟙 _
      comm₁₂ := imageSubobject_arrow_comp (coniveauCohomologyToAbutment k X K n b)
      comm₂₃ := by
        let e := coniveauCohomologyZeroIso k X K n
        let f := coniveauCohomologyToWindow k X K n 0 b
        change e.hom ≫ e.inv ≫ f = f ≫ 𝟙 _
        exact (e.hom_inv_id_assoc f).trans (Category.comp_id f).symm }
  have : Epi φ.τ₁ :=
    inferInstanceAs (Epi (factorThruImageSubobject (coniveauCohomologyToAbutment k X K n b)))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (coniveauCohomologyZeroIso k X K n).hom)
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
    (coniveauCohomologyStage_exact k X K n (Nat.zero_le b))

/-- The quotient of the abutment by stage `b` embeds in the window `(0,b)`. -/
@[no_expose]
def coniveauCohomologyQuotientToWindow (n : ℤ) (b : ℕ) :
    cokernel (coniveauFiltration k X K n b).arrow ⟶ coniveauRelativeSupportCohomology k X K n 0 b :=
  cokernel.desc _ (coniveauAbutmentToWindow k X K n b)
    (coniveauQuotientWindowComplex k X K n b).zero

instance (n : ℤ) (b : ℕ) : Mono (coniveauCohomologyQuotientToWindow k X K n b) :=
  (coniveauQuotientWindowComplex_exact k X K n b).mono_cokernelDesc

/-- The quotient embedding is induced by the original map from the zero stage to the window. -/
@[reassoc]
theorem cokernel_π_coniveauCohomologyQuotientToWindow (n : ℤ) (b : ℕ) :
    cokernel.π (coniveauFiltration k X K n b).arrow ≫
        coniveauCohomologyQuotientToWindow k X K n b =
      (coniveauCohomologyZeroIso k X K n).inv ≫ coniveauCohomologyToWindow k X K n 0 b :=
  cokernel.π_desc _ _ (coniveauQuotientWindowComplex k X K n b).zero

private lemma coniveauCohomologyToAbutment_comp_quotientToWindow (n : ℤ) (p b : ℕ) :
    coniveauCohomologyToAbutment k X K n p ≫ cokernel.π (coniveauFiltration k X K n b).arrow ≫
        coniveauCohomologyQuotientToWindow k X K n b =
      coniveauCohomologyTransition k X K n (Nat.zero_le p) ≫
        coniveauCohomologyToWindow k X K n 0 b := by
  rw [cokernel_π_coniveauCohomologyQuotientToWindow]
  simp only [coniveauCohomologyToAbutment, Category.assoc,
    Iso.hom_inv_id_assoc]

private def coniveauWindowImageIsoAssociatedGradedData (n : ℤ) {d p b : ℕ}
    (hX : topologicalKrullDim X.left ≤ d) (hdb : d < b) (hpb : p + 1 ≤ b) :
    {e : image (coniveauWindowMap k X K n (Nat.zero_le p) hpb) ≅
        coniveauAssociatedGraded k X K n p //
      e.hom ≫ image.ι (coniveauAssociatedGradedMap k X K n p) ≫
          coniveauCohomologyQuotientToWindow k X K n (p + 1) =
        image.ι (coniveauWindowMap k X K n (Nat.zero_le p) hpb)} := by
  let e := coniveauAbsoluteWindowIso k X K n ((Nat.le_succ p).trans hpb) hX hdb
  let f := coniveauAssociatedGradedMap k X K n p
  let t : coniveauCohomology k X K n p ⟶ (coniveauFiltration k X K n p : AddCommGrpCat.{w'}) :=
    factorThruImageSubobject (coniveauCohomologyToAbutment k X K n p)
  let m := coniveauCohomologyQuotientToWindow k X K n (p + 1)
  let j := coniveauWindowMap k X K n (Nat.zero_le p) hpb
  have ht : t ≫ (coniveauFiltration k X K n p).arrow = coniveauCohomologyToAbutment k X K n p :=
    imageSubobject_arrow_comp _
  have hs : t ≫ f ≫ m = e.hom ≫ j := by
    calc
      t ≫ f ≫ m = (t ≫ (coniveauFiltration k X K n p).arrow) ≫
          cokernel.π (coniveauFiltration k X K n (p + 1)).arrow ≫ m := by
        simp only [f, coniveauAssociatedGradedMap, Category.assoc]
      _ = e.hom ≫ j := by
        rw [ht, coniveauCohomologyToAbutment_comp_quotientToWindow,
          coniveauAbsoluteWindowIso_hom, coniveauCohomologyToWindow_comp_windowMap]
  have hcomm : (e.inv ≫ t ≫ factorThruImage f) ≫ (image.ι f ≫ m) = j := by
    simp only [Category.assoc, image.fac_assoc, hs, Iso.inv_hom_id_assoc]
  have : Epi t :=
    inferInstanceAs (Epi (factorThruImageSubobject (coniveauCohomologyToAbutment k X K n p)))
  have : Epi (e.inv ≫ t ≫ factorThruImage f) := epi_comp e.inv (t ≫ factorThruImage f)
  letI : StrongEpi (e.inv ≫ t ≫ factorThruImage f) := strongEpi_of_epi _
  have : Mono (image.ι f ≫ m) := by
    dsimp [m]
    infer_instance
  exact ⟨(image.isoStrongEpiMono _ _ hcomm).symm,
    image.isoStrongEpiMono_inv_comp_mono _ _ hcomm⟩

/-- Once the source window contains the whole support stage, its diagonal map into
`(0,p+1)` has image the `p`th associated graded piece of represented cohomology. -/
@[no_expose]
def coniveauWindowImageIsoAssociatedGraded (n : ℤ) {d p b : ℕ}
    (hX : topologicalKrullDim X.left ≤ d) (hdb : d < b) (hpb : p + 1 ≤ b) :
    image (coniveauWindowMap k X K n (Nat.zero_le p) hpb) ≅
      coniveauAssociatedGraded k X K n p :=
  (coniveauWindowImageIsoAssociatedGradedData k X K n hX hdb hpb).val

/-- The comparison of images preserves the inclusion in the target window. -/
@[reassoc]
theorem coniveauWindowImageIsoAssociatedGraded_hom_comp_ι (n : ℤ) {d p b : ℕ}
    (hX : topologicalKrullDim X.left ≤ d) (hdb : d < b) (hpb : p + 1 ≤ b) :
    (coniveauWindowImageIsoAssociatedGraded k X K n hX hdb hpb).hom ≫
        image.ι (coniveauAssociatedGradedMap k X K n p) ≫
          coniveauCohomologyQuotientToWindow k X K n (p + 1) =
      image.ι (coniveauWindowMap k X K n (Nat.zero_le p) hpb) :=
  (coniveauWindowImageIsoAssociatedGradedData k X K n hX hdb hpb).property

local notation "data" => coreE₁DecreasingFiltration coniveauIndex

private def coniveauSpectralObjectEImageIso (n : ℤ) {a b c d : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    (coniveauSpectralObject k X K).E
        (homOfLE (show toDual d ≤ toDual c from hcd))
        (homOfLE (show toDual c ≤ toDual b from hbc))
        (homOfLE (show toDual b ≤ toDual a from hab)) (n - 1) n (n + 1) ≅
      image (coniveauWindowMap k X K n hab hcd) := by
  let S := coniveauSpectralObject k X K
  let f₁ : toDual d ⟶ toDual c := homOfLE hcd
  let f₂ : toDual c ⟶ toDual b := homOfLE hbc
  let f₃ : toDual b ⟶ toDual a := homOfLE hab
  let f₁₂ : toDual d ⟶ toDual b := homOfLE (hbc.trans hcd)
  let f₂₃ : toDual c ⟶ toDual a := homOfLE (hab.trans hbc)
  have h₁₂ : f₁ ≫ f₂ = f₁₂ := Subsingleton.elim _ _
  have h₂₃ : f₂ ≫ f₃ = f₂₃ := Subsingleton.elim _ _
  let α := pageWindowMorphism f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃
  let e₁ := coniveauSpectralObjectWindowIso k X K n b d (hbc.trans hcd)
  let e₂ := coniveauSpectralObjectWindowIso k X K n a c (hab.trans hbc)
  refine S.pageImageIso f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ (n - 1) n (n + 1) (by omega) rfl ≪≫ ?_
  exact (Limits.im (C := AddCommGrpCat.{w'})).mapIso
    (Arrow.isoMk' ((S.H n).map α) (coniveauWindowMap k X K n hab hcd) e₁ e₂
      (coniveauSpectralObjectWindowIso_naturality k X K n (hbc.trans hcd) (hab.trans hbc) α).symm)

private def coniveauSpectralSequencePageImageIsoOfIndices (r : ℤ) (hr : 1 ≤ r) (p : ℕ) (q : ℤ)
    {a b : ℕ} (ha : a ≤ p) (hb : p + 1 ≤ b)
    (ha' : a = ((p : ℤ) - r + 1).toNat) (hb' : b = ((p : ℤ) + r).toNat) :
    ((coniveauSpectralSequence k X K).page r).X ((p : ℤ), q) ≅
      image (coniveauWindowMap k X K ((p : ℤ) + q) ha hb) := by
  have h₀ : toDual b = (data).i₀ r ((p : ℤ), q) := by
    apply toDual_inj.mpr
    change b = (-(-(p : ℤ) - r)).toNat
    omega
  have h₃ : toDual a = (data).i₃ r ((p : ℤ), q) := by
    apply toDual_inj.mpr
    change a = (-(-(p : ℤ) + r - 1)).toNat
    omega
  let n : ℤ := (p : ℤ) + q
  exact (coniveauSpectralObject k X K).spectralSequencePageXIso (data) r hr ((p : ℤ), q)
    (toDual b) (toDual (p + 1)) (toDual p) (toDual a)
    h₀ (coniveauFirstPageIndex₁ p q) (coniveauFirstPageIndex₂ p q) h₃ (n - 1) n (n + 1) rfl ≪≫
      coniveauSpectralObjectEImageIso k X K n ha (Nat.le_succ p) hb

/-- In nonnegative codimension the native page is the image of the map from window
`(p,p+r)` to window `(max(p-r+1,0),p+1)`. -/
@[no_expose]
def coniveauSpectralSequencePageImageIso (r : ℤ) (hr : 1 ≤ r) (p : ℕ) (q : ℤ) :
    ((coniveauSpectralSequence k X K).page r).X ((p : ℤ), q) ≅
      image (coniveauWindowMap k X K ((p : ℤ) + q)
        (show ((p : ℤ) - r + 1).toNat ≤ p by omega)
        (show p + 1 ≤ ((p : ℤ) + r).toNat by omega)) :=
  coniveauSpectralSequencePageImageIsoOfIndices k X K r hr p q _ _ rfl rfl

/-- Every page term in negative codimension vanishes. -/
theorem isZero_coniveauSpectralSequencePage_of_lt_zero (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hp : p < 0) : IsZero (((coniveauSpectralSequence k X K).page r).X (p, q)) := by
  let z := toDual (0 : ℕ)
  have h₁ : z = (data).i₁ (p, q) := by
    apply toDual_inj.mpr
    change 0 = (-(-p - 1)).toNat
    omega
  have h₂ : z = (data).i₂ (p, q) := by
    apply toDual_inj.mpr
    change 0 = (-(-p)).toNat
    omega
  let S := coniveauSpectralObject k X K
  exact S.isZero_spectralSequence_page_X_of_isZero_H (data) r hr (p, q) (p + q) rfl z z h₁ h₂
    (S.isZero_H_map_mk₁_of_isIso (p + q) (𝟙 z))

private theorem isZero_coniveauSpectralSequencePage_nat_above_dimension (r : ℤ) (hr : 1 ≤ r)
    (p : ℕ) (q : ℤ) {d : ℕ} (hX : topologicalKrullDim X.left ≤ d) (hp : d < p) :
    IsZero (((coniveauSpectralSequence k X K).page r).X ((p : ℤ), q)) := by
  let n : ℤ := (p : ℤ) + q
  let S := coniveauSpectralObject k X K
  let hab := Nat.le_succ p
  exact S.isZero_spectralSequence_page_X_of_isZero_H (data) r hr ((p : ℤ), q) n rfl
    (toDual (p + 1)) (toDual p) (coniveauFirstPageIndex₁ p q) (coniveauFirstPageIndex₂ p q)
    ((isZero_coniveauCohomology_above_dimension k X K n hX hp).of_iso
      (coniveauSpectralObjectWindowIso k X K n p (p + 1) hab ≪≫
        (coniveauAbsoluteWindowIso k X K n hab hX (hp.trans_le hab)).symm))

/-- Every page term above the dimension bound vanishes. -/
theorem isZero_coniveauSpectralSequencePage_above_dimension (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    {d : ℕ} (hX : topologicalKrullDim X.left ≤ d) (hp : (d : ℤ) < p) :
    IsZero (((coniveauSpectralSequence k X K).page r).X (p, q)) := by
  have hcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by omega)
  simpa only [hcast] using
    isZero_coniveauSpectralSequencePage_nat_above_dimension k X K r hr p.toNat q hX (by omega)

/-- Beyond the dimension bound, every differential of the coniveau spectral sequence vanishes. -/
theorem coniveauSpectralSequence_d_eq_zero_of_dimension_lt (r : ℤ) (hr : 1 ≤ r)
    {d : ℕ} (hX : topologicalKrullDim X.left ≤ d) (hrd : (d : ℤ) < r)
    (pq pq' : ℤ × ℤ) : ((coniveauSpectralSequence k X K).page r).d pq pq' = 0 := by
  rcases pq with ⟨p, q⟩
  rcases pq' with ⟨p', q'⟩
  by_cases h : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel (p, q) (p', q')
  · change (p, q) + (r, 1 - r) = (p', q') at h
    have hh : p + r = p' := congrArg Prod.fst h
    by_cases hp : p < 0
    · exact (isZero_coniveauSpectralSequencePage_of_lt_zero k X K r hr p q hp).eq_of_src _ _
    · exact (isZero_coniveauSpectralSequencePage_above_dimension k X K r hr p' q' hX
        (by omega)).eq_of_tgt _ _
  · exact ((coniveauSpectralSequence k X K).page r).shape _ _ h

/-- Beyond the dimension bound the coniveau page identifies with the associated graded
of the original filtration on represented cohomology. -/
@[no_expose, colib_tag "COL-1318", colib_ref "Deglise2011Coniveau" "Equation (2.1.c)"
  "adaptation" "Finite associated graded of the represented effective coniveau filtration"]
def coniveauSpectralSequencePageStableIso (r : ℤ) (hr : 1 ≤ r) (p : ℕ) (q : ℤ)
    {d : ℕ} (hX : topologicalKrullDim X.left ≤ d) (hrd : (d : ℤ) < r) :
    ((coniveauSpectralSequence k X K).page r).X ((p : ℤ), q) ≅
      coniveauAssociatedGraded k X K ((p : ℤ) + q) p := by
  by_cases hp : p ≤ d
  · have hb : p + 1 ≤ ((p : ℤ) + r).toNat := by omega
    refine coniveauSpectralSequencePageImageIsoOfIndices k X K r hr p q (Nat.zero_le p) hb
      (by omega) rfl ≪≫ ?_
    exact coniveauWindowImageIsoAssociatedGraded k X K ((p : ℤ) + q) hX (by omega) hb
  · exact (isZero_coniveauSpectralSequencePage_nat_above_dimension k X K r hr p q hX
      (by omega)).iso (isZero_coniveauAssociatedGraded_of_dimension_lt k X K ((p : ℤ) + q) hX
        (by omega))

end AlgebraicGeometry.MotivicHomotopy
