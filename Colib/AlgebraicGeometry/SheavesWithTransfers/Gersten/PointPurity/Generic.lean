/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Topology.Category.TopCat.OpenNhds
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Whiskering
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

/-! # Ordinary cohomology at the generic point of a smooth model -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open Opposite TopologicalSpace SmoothSite Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.SheafWithTransfers.Gersten

variable {S : Scheme.{u}} [IsNoetherian S]
  (Y : SmoothSite S) (η : Y.left)
  (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})

/-- The germ of sections over the original Zariski neighborhoods of the point. -/
abbrev smoothSectionGerm : AddCommGrpCat.{u + 1} :=
  colimit ((OpenNhds.inclusion (X := Y.left.carrier) η ⋙ opensFunctor Y).op ⋙ F.obj)

variable [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

/-- The ordinary cohomology groups of the actual open neighborhoods of the point. -/
abbrev smoothCohomologyGermDiagram (n : ℕ) :
    (OpenNhds (X := Y.left.carrier) η)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (OpenNhds.inclusion (X := Y.left.carrier) η ⋙ opensFunctor Y).op ⋙
    cohomologyPresheaf.{u + 1, u + 1} F n

/-- The degree-zero cohomology germ is the original germ of sections. -/
def smoothCohomologyGermZeroIso :
    colimit (smoothCohomologyGermDiagram Y η F 0) ≅ smoothSectionGerm Y η F :=
  HasColimit.isoOfNatIso (Functor.isoWhiskerLeft _ (cohomologyPresheafIsoSections F))

omit [IsNoetherian S]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})] in
private theorem isGenericPoint_on_open (hη : IsGenericPoint η Set.univ)
    (U : OpenNhds (X := Y.left.carrier) η) :
    IsGenericPoint (⟨η, U.2⟩ : Scheme.Opens.toScheme (X := Y.left) U.1) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  let i := Scheme.Opens.ι (X := Y.left) U.1
  exact i.isOpenEmbedding.isInducing.specializes_iff.mp (hη.specializes (Set.mem_univ _))

set_option maxHeartbeats 700000 in
-- Use the actual open-chart inclusions on the original cohomology presheaf.
/-- Every positive cohomology class on a generic neighborhood becomes zero on a smaller
generic neighborhood. -/
theorem smoothCohomologyGermDiagram_eventually_zero [IsIntegral Y.left]
    (hη : IsGenericPoint η Set.univ) (n : ℕ) (U : OpenNhds (X := Y.left.carrier) η)
    (z : (smoothCohomologyGermDiagram Y η F (n + 1)).obj (op U)) :
    ∃ V : OpenNhds (X := Y.left.carrier) η, ∃ r : V ⟶ U,
      (smoothCohomologyGermDiagram Y η F (n + 1)).map r.op z = 0 := by
  let U₀ : Y.left.Opens := U.1
  let A := (opensFunctor Y).obj U₀
  let : Nonempty A.left := ⟨⟨η, U.2⟩⟩
  let : IsIntegral A.left := isIntegral_of_isOpenImmersion U₀.ι
  have hηA : genericPoint A.left = (⟨η, U.2⟩ : U₀.toScheme) :=
    (genericPoint_spec A.left).eq (isGenericPoint_on_open Y η hη U)
  obtain ⟨W, hW, hz⟩ := exists_generic_open_restriction_eq_zero F n A z
  let V : Y.left.Opens := U₀.ι ''ᵁ W
  have hV : η ∈ V := ⟨genericPoint A.left, hW, congrArg U₀.ι hηA⟩
  have hVU : V ≤ U₀ := by
    simpa only [Scheme.Opens.opensRange_ι] using U₀.ι.image_le_opensRange W
  let a := (opensFunctor Y).map (homOfLE hVU)
  let B := (opensFunctor A).obj W
  let C := (opensFunctor Y).obj V
  let e₀ := U₀.ι.isoImage W
  have hf : e₀.hom ≫ V.ι = W.ι ≫ U₀.ι := Scheme.Hom.isoImage_hom_ι U₀.ι W
  let e : B ≅ C := MorphismProperty.Over.isoMk e₀ (by
    change e₀.hom ≫ V.ι ≫ Y.hom = W.ι ≫ U₀.ι ≫ Y.hom
    rw [← Category.assoc, hf, Category.assoc])
  have he : e.hom ≫ a = openInclusion A W := by
    apply MorphismProperty.Over.Hom.ext
    change e₀.hom ≫ Y.left.homOfLE hVU = W.ι
    apply (cancel_mono U₀.ι).1
    rw [Category.assoc, Scheme.homOfLE_ι, hf]
  refine ⟨⟨V, hV⟩, homOfLE hVU, ?_⟩
  let H := cohomologyPresheaf.{u + 1, u + 1} F (n + 1)
  change H.map a.op z = 0
  apply (ConcreteCategory.bijective_of_isIso (H.map e.hom.op)).injective
  rw [map_zero]
  have hc : H.map a.op ≫ H.map e.hom.op = H.map (openInclusion A W).op :=
    (H.map_comp _ _).symm.trans (H.congr_map (congrArg (fun f : B ⟶ A => f.op) he))
  exact (ConcreteCategory.congr_hom hc z).trans hz

/-- Positive ordinary cohomology vanishes in the generic germ. -/
theorem subsingleton_smoothCohomologyGerm_succ [IsIntegral Y.left]
    (hη : IsGenericPoint η Set.univ) (n : ℕ) :
    Subsingleton (colimit (smoothCohomologyGermDiagram Y η F (n + 1)) :
      AddCommGrpCat.{u + 1}) := by
  let H := smoothCohomologyGermDiagram Y η F (n + 1)
  have hι (U : (OpenNhds (X := Y.left.carrier) η)ᵒᵖ) : colimit.ι H U = 0 := by
    apply ConcreteCategory.hom_ext
    intro c
    obtain ⟨V, r, hz⟩ := smoothCohomologyGermDiagram_eventually_zero Y η F hη n U.unop c
    have h := ConcreteCategory.congr_hom (colimit.w H r.op) c
    change colimit.ι H (op V) (H.map r.op c) = colimit.ι H U c at h
    change colimit.ι H U c = 0
    rw [← h, hz, map_zero]
  have h0 : 𝟙 (colimit H) = 0 := by
    apply colimit.hom_ext
    intro U
    rw [Category.comp_id, comp_zero, hι U]
  exact ⟨fun x y => (ConcreteCategory.congr_hom h0 x).trans
    (ConcreteCategory.congr_hom h0 y).symm⟩

end AlgebraicGeometry.SheafWithTransfers.Gersten
