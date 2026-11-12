/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodCurveSections

/-!
# The element-level step for original marked-neighborhood induction

The source is an original marked-neighborhood value, so it can be the base small-site stalk
rather than F(k). An explicit equality between the two chart restrictions on an actual
further affine etale neighborhood supplies a preimage of the original representative.
The S1 action equality and the lower-dimensional isomorphism remain visible inputs.
No presheaf extension to a henselian scheme or extension-field transfer presheaf is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- An actual lower pullback isomorphism supplies a preimage under the original composite. -/
theorem exists_etaleNeighborhoodValuePullback_preimage_of_eq
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {X Y T : SmoothSite S} [IsAffine X.left] [IsAffine Y.left] [IsAffine T.left]
    (f : X ⟶ Y) (g : Y ⟶ T) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {ξ : Spec (.of Ω) ⟶ X.left} {η : Spec (.of Ω) ⟶ Y.left}
    {ζ : Spec (.of Ω) ⟶ T.left} (hf : ξ ≫ f.left = η) (hg : η ≫ g.left = ζ)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)]
    (w : etaleNeighborhoodValue Y η F) (x : etaleNeighborhoodValue X ξ F)
    (hw : etaleNeighborhoodValuePullback f hf F w = x) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback (f ≫ g) (by
        change ξ ≫ (f.left ≫ g.left) = ζ
        rw [← Category.assoc, hf, hg]) F z = x := by
  let z : etaleNeighborhoodValue T ζ F :=
    (asIso (etaleNeighborhoodValuePullback g hg F)).inv w
  have hz : etaleNeighborhoodValuePullback g hg F z = w :=
    ConcreteCategory.congr_hom (asIso (etaleNeighborhoodValuePullback g hg F)).inv_hom_id w
  refine ⟨z, ?_⟩
  rw [etaleNeighborhoodValuePullback_comp f g hf hg]
  change etaleNeighborhoodValuePullback f hf F (etaleNeighborhoodValuePullback g hg F z) = x
  rw [hz, hw]

/-- Equality after an actual affine etale refinement implies equality of original evaluations. -/
theorem toEtaleNeighborhoodValueFromObject_map_eq_of_refinement
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {X Y : SmoothSite S} [IsAffine X.left] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X.left) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (f g : X ⟶ Y) (N : EtaleNeighborhood X ξ) (a : F.obj (op Y))
    (ha : (F.map (etaleNeighborhoodHom X ξ N ≫ f).op).hom a =
      (F.map (etaleNeighborhoodHom X ξ N ≫ g).op).hom a) :
    toEtaleNeighborhoodValueFromObject X ξ F (F.map f.op a) =
      toEtaleNeighborhoodValueFromObject X ξ F (F.map g.op a) := by
  rw [toEtaleNeighborhoodValueFromObject_eq F N]
  have h := congrArg (fun z => (toEtaleNeighborhoodValue X ξ N F).hom z) ha
  simpa only [op_comp, F.map_comp, ConcreteCategory.comp_apply] using h

namespace EtaleChart

/-- If the two actual restrictions agree after a specified affine etale refinement, the
original representative comes from the lower source whenever its original pullback is an iso.
The restriction equality is an explicit S1 obligation, not asserted by this theorem. -/
theorem exists_representative_preimage_of_restrictions_eq {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A Y Z T : SmoothSite S} [IsAffine A.left] [IsAffine Y.left]
    [IsAffine Z.left] [IsAffine T.left]
    (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z) (g : Y ⟶ T)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
    (ζ : Spec (.of Ω) ⟶ T.left)
    (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left)
    (hg : η ≫ g.left = ζ) (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    [IsIso (etaleNeighborhoodValuePullback g hg F)] (a : F.obj (op A))
    (N : EtaleNeighborhood (refinementObject q p s) (refinementMark q p s ξ η hξ hs))
    (ha : (F.map (etaleNeighborhoodHom _ _ N ≫ refinementToChart q p s).op).hom a =
      (F.map (etaleNeighborhoodHom _ _ N ≫
        (refinementToSection q p s ≫ sectionToChart q s)).op).hom a) :
    ∃ z : etaleNeighborhoodValue T ζ F,
      etaleNeighborhoodValuePullback ((q ≫ p) ≫ g) (by
        change ξ ≫ ((q ≫ p).left ≫ g.left) = ζ
        rw [← Category.assoc, chartMark_base q p s ξ η hξ hs, hg]) F z =
          toEtaleNeighborhoodValueFromObject A ξ F a := by
  let v : etaleNeighborhoodValue (sectionObject q s) (sectionMark q s ξ η hξ) F :=
    (toEtaleNeighborhoodValueFromObject (sectionObject q s) (sectionMark q s ξ η hξ) F).hom
      ((F.map (sectionToChart q s).op).hom a)
  let eV : etaleNeighborhoodValue Y η F ≅
      etaleNeighborhoodValue (sectionObject q s) (sectionMark q s ξ η hξ) F :=
    etaleNeighborhoodValueEtaleIso (sectionToBase q s) (sectionMark_base q s ξ η hξ) F
  let w : etaleNeighborhoodValue Y η F := eV.inv.hom v
  apply exists_etaleNeighborhoodValuePullback_preimage_of_eq (q ≫ p) g
    (chartMark_base q p s ξ η hξ hs) hg F w
  have ho := ConcreteCategory.congr_hom (original_representative q p s ξ η hξ hs F) a
  have hr := ConcreteCategory.congr_hom (retract_representative q p s ξ η hξ hs F) a
  change toEtaleNeighborhoodValueFromObject A ξ F a =
    (refinementValueIso q p s ξ η hξ hs F).inv
      (toEtaleNeighborhoodValueFromObject (refinementObject q p s)
        (refinementMark q p s ξ η hξ hs) F (F.map (refinementToChart q p s).op a)) at ho
  change etaleNeighborhoodValuePullback (q ≫ p) _ F w =
    (refinementValueIso q p s ξ η hξ hs F).inv
      (toEtaleNeighborhoodValueFromObject (refinementObject q p s)
        (refinementMark q p s ξ η hξ hs) F
          (F.map (refinementToSection q p s ≫ sectionToChart q s).op a)) at hr
  have hB := toEtaleNeighborhoodValueFromObject_map_eq_of_refinement
    (refinementMark q p s ξ η hξ hs) F
    (refinementToChart q p s) (refinementToSection q p s ≫ sectionToChart q s) N a ha
  rw [ho, hB]
  exact hr

end EtaleChart
end AlgebraicGeometry.Scheme.SmoothSite
