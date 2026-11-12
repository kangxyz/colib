/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormRefinement
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare

/-!
# The whole cylinder and its actual puncture after coefficient restriction

The original open and marked pieces give the actual two-arrow cover. On the
source compactification the overlap, the boundary, and the entire marked
lift cover the whole space.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

/-- Restricting just the coefficients is a pullback of the whole parameter. -/
theorem wholeParameter_isPullback {S X : Scheme.{u}} (q : X ⟶ S) (V : S.Opens) :
    IsPullback (parameterOpen q ⊤ V).ι (parameterProjection q ⊤ V) q V.ι := by
  have H : IsPullback (parameterProjection q ⊤ V) (parameterOpen q ⊤ V).ι V.ι q := by
    apply IsOpenImmersion.isPullback _ _ _ _ (parameterProjection_base q ⊤ V).symm
    ext x
    simp [parameterOpen, Opens.opensRange_ι]
  exact H.flip

/-- A puncture meeting each original fiber still meets each fiber over a
coefficient open, with the actual second-source pullback. -/
theorem secondMap_surjective_base {S X A : Scheme.{u}}
    (q : X ⟶ S) (V : S.Opens) (a : A ⟶ X) (ha : Function.Surjective (a ≫ q)) :
    Function.Surjective (secondMap q ⊤ V a ≫ parameterProjection q ⊤ V) := by
  intro y
  obtain ⟨x, hx⟩ := ha (V.ι y)
  let z : (parameterOpen q ⊤ V).toScheme := ⟨a x, ⟨trivial, by
    change (a ≫ q) x ∈ V
    rw [hx]
    exact y.property⟩⟩
  obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback a (parameterOpen q ⊤ V).ι) x z rfl
  refine ⟨w, V.ι.isOpenEmbedding.injective ?_⟩
  change ((secondMap q ⊤ V a ≫ parameterProjection q ⊤ V) ≫ V.ι) w = V.ι y
  rw [Category.assoc, parameterProjection_base, Hom.comp_apply, hw]
  exact hx

/-- The two actual boundary maps and the puncture cover the compact target. -/
theorem target_puncture_boundary_cover {X P A Z D : Scheme.{u}}
    (j : X ⟶ P) (a : A ⟶ X) (z : Z ⟶ X) (d : D ⟶ P)
    (hd : (Set.range j)ᶜ ⊆ Set.range d)
    (hcover : ∀ x : X, x ∈ Set.range a ∨ x ∈ Set.range z) :
    ∀ x : P, x ∈ Set.range (a ≫ j) ∨ x ∈ Set.range d ∨ x ∈ Set.range (z ≫ j) := by
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    rcases hcover y with ⟨v, rfl⟩ | ⟨w, rfl⟩
    · exact Or.inl ⟨v, rfl⟩
    · exact Or.inr (Or.inr ⟨w, rfl⟩)
  · exact Or.inr (Or.inl (hd hx))

/-- The actual overlap of the first source with the puncture, the whole
boundary, and the entire marked lift cover the source compactification. -/
theorem source_overlap_boundary_cover {X Y C A Z D : Scheme.{u}}
    (j : Y ⟶ C) (p : Y ⟶ X) (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y)
    (H : IsPullback s (𝟙 Z) p z) (d : D ⟶ C)
    (hd : (Set.range j)ᶜ ⊆ Set.range d)
    (hcover : ∀ x : X, x ∈ Set.range a ∨ x ∈ Set.range z) :
    ∀ x : C, x ∈ Set.range (pullback.fst p a ≫ j) ∨ x ∈ Set.range d ∨
      x ∈ Set.range (s ≫ j) := by
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    rcases hcover (p y) with ⟨v, hv⟩ | ⟨w, hw⟩
    · obtain ⟨r, hr, -⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback p a) y v hv.symm
      exact Or.inl ⟨r, congrArg j hr⟩
    · obtain ⟨r, hr, -⟩ := Scheme.exists_preimage_of_isPullback H y w hw.symm
      exact Or.inr (Or.inr ⟨r, congrArg j hr⟩)
  · exact Or.inr (Or.inl (hd hx))

/-- The two original open and étale maps cover after retaining their full
Cartesian marked square and the complementary puncture. -/
theorem markedCover_mem_nisnevichTopology {S : Scheme.{u}}
    {A Y X : SmoothSite S} (a : A ⟶ X) (p : Y ⟶ X)
    [IsOpenImmersion a.left] [Etale p.left] {Z : Scheme.{u}}
    (z : Z ⟶ X.left) [IsClosedImmersion z] (s : Z ⟶ Y.left)
    (H : IsPullback s (𝟙 Z) p.left z)
    (hcover : ∀ x : X.left, x ∈ Set.range a.left ∨ x ∈ Set.range z)
    (hdisj : Disjoint (Set.range a.left) (Set.range z)) :
    Sieve.ofTwoArrows a p ∈ SmoothSite.nisnevichTopology S X := by
  have hIso : H.isoPullback.hom ≫ pullback.snd p.left z = 𝟙 Z := H.isoPullback_hom_snd
  have h : pullback.snd p.left z = H.isoPullback.inv := by
    apply (cancel_epi H.isoPullback.hom).1
    rw [hIso, Iso.hom_inv_id]
  let : IsIso (pullback.snd p.left z) := h.symm ▸ inferInstanceAs (IsIso H.isoPullback.inv)
  apply SmoothSite.ofTwoArrows_mem_nisnevichTopology_of_iso_complement a p z
  ext x
  constructor
  · exact fun hz ha ↦ Set.disjoint_left.mp hdisj ha hz
  · exact fun ha ↦ (hcover x).resolve_left ha

/-- A change of the displayed compactification projection along its actual
base-map equality retains the original four section choices. -/
def SectionData.changeProjection {S X Y C A Z D : Scheme.{u}}
    (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    {π π' : C ⟶ S} [IsSeparated π] [IsSeparated π'] (hπ : π = π')
    (j : Y ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ π)] [SmoothOfRelativeDimension 1 (j ≫ π')]
    (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (hq' : j ≫ π' = p ≫ q)
    (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
    (H : IsPullback s (𝟙 Z) p z)
    (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
      SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
    (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
    (ha : Disjoint (Set.range a) (Set.range z))
    (c : SectionData q π j p hq a z s hs H e d hd ha) :
    SectionData q π' j p hq' a z s hs H e d hd ha := by
  subst π'
  exact c

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

namespace AlgebraicGeometry.Scheme

/-- A projective parameter product on an open has the integrality of its
actual product over the original coefficient base. -/
theorem isIntegral_pullback_morphismRestrict {S X K : Scheme.{u}}
    (π : X ⟶ S) (V : S.Opens) (b : K ⟶ V.toScheme)
    (h : IsIntegral (pullback (b ≫ V.ι) π)) : IsIntegral (pullback b (π ∣_ V)) := by
  let H := (IsPullback.of_hasPullback b (π ∣_ V)).flip.paste_horiz
    (isPullback_morphismRestrict π V).flip
  let : IsIntegral (pullback (b ≫ V.ι) π) := h
  exact IsIntegral.of_isIso H.flip.isoPullback.inv

end AlgebraicGeometry.Scheme
