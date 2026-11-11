/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Sites.Nisnevich.FieldLifting
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.NeighborhoodPoint
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Sheafification
public import Colib.CategoryTheory.Sites.Point.NeighborhoodRefinement
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Enough points for the smooth Nisnevich site

Take the small affine basis and mark each of its scheme points. A sieve
that admits lifts at the resulting points contains étale arrows jointly
lifting all field-valued points. Thus it is covering.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme.SmoothSite

open GrothendieckTopology.Point.ofIsCofiltered

private theorem hasEnoughPoints_nisnevichTopology (S : Scheme.{u}) [QuasiSeparatedSpace S]
    [HasSheafify (nisnevichTopology S) (Type (max u w))] :
    GrothendieckTopology.HasEnoughPoints.{max u w} (nisnevichTopology S) where
  exists_objectProperty := by
    obtain ⟨ι, U, hU⟩ := exists_smallFamily_openImmersionAtPoint S
    let P := ObjectProperty.ofObj
      (fun i : Σ i : ι, (U i).left ↦ nisnevichNeighborhoodPoint.{u,w} (U i.1) i.2)
    refine ⟨P, inferInstance, ObjectProperty.IsConservativeFamilyOfPoints.mk' ?_⟩
    intro X R hR
    let Q : Presieve X := fun _ f ↦ R f ∧ Etale f.left
    refine mem_nisnevichTopology_iff.mpr ⟨Q, ?_, fun _ _ h ↦ h.1⟩
    apply mem_nisnevichPrecoverage_iff.mpr
    apply Nisnevich.mem_precoverage_of_field_lifting
    · rintro _ _ ⟨h⟩
      exact h.2
    · intro K _ s
      obtain ⟨⟨x, c⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X.left).symm.surjective s
      obtain ⟨i, a, y, ha, hy⟩ := hU X x
      obtain ⟨A⟩ : Nonempty (NisnevichNeighborhood (U i) y) := IsCofiltered.nonempty
      let D := nisnevichNeighborhoodToSmooth (U i) y
      let f : D.obj A ⟶ X := nisnevichNeighborhoodHom (U i) y A ≫ a
      let Φ := nisnevichNeighborhoodPoint.{u,w} (U i) y
      let := nisnevichNeighborhoodInitiallySmall.{u,w} (U i) y
      let hΦ : P.FullSubcategory :=
        ⟨Φ, ObjectProperty.ofObj_apply _ (⟨i, y⟩ : Σ i : ι, (U i).left)⟩
      obtain ⟨Y, g, hg, b, hb⟩ := hR hΦ (fiberMk.{max u w} (p := D) f)
      change (fiber.{max u w} D).map g b = fiberMk.{max u w} f at hb
      obtain ⟨B, q, hq⟩ := exists_mem_sieve_of_fiber_map_eq_fiberMk hg hb
      have hq' : D.map q ≫ nisnevichNeighborhoodHom (U i) y A =
          nisnevichNeighborhoodHom (U i) y B :=
        MorphismProperty.Over.Hom.ext (nisnevichNeighborhoodMap_hom (U i) y q)
      let p := nisnevichNeighborhoodHom (U i) y B
      have hp : R (p ≫ a) := by
        change R (D.map q ≫ (nisnevichNeighborhoodHom (U i) y A ≫ a)) at hq
        rwa [← Category.assoc, hq'] at hq
      let l := nisnevichNeighborhoodMark (U i) y B
      let : IsOpenImmersion a.left := ha
      let : Etale p.left := inferInstanceAs (Etale ((nisnevichNeighborhoodHom (U i) y B).left))
      have he : Etale (p ≫ a).left := by
        change Etale (p.left ≫ a.left)
        infer_instance
      refine ⟨_, _, Presieve.map_map (F := forgetScheme S) (R := Q) ⟨hp, he⟩, ?_⟩
      subst x
      let d := a.left.residueFieldMap y
      let : IsIso d := inferInstanceAs (IsIso (a.left.residueFieldMap y))
      refine ⟨Spec.map (inv d ≫ c) ≫ l, ?_⟩
      change (Spec.map (inv d ≫ c) ≫ l) ≫ (p.left ≫ a.left) =
        Spec.map c ≫ X.left.fromSpecResidueField (a.left y)
      calc
        _ = Spec.map (inv d ≫ c) ≫ ((l ≫ p.left) ≫ a.left) := by
          simp only [Category.assoc]
        _ = _ := by
          rw [nisnevichNeighborhoodMark_hom,
            ← a.left.SpecMap_residueFieldMap_fromSpecResidueField y, ← Spec.map_comp_assoc]
          simp [d]

/-- The smooth Nisnevich site has enough points in the scheme universe. -/
instance nisnevichTopology_hasEnoughPoints (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    GrothendieckTopology.HasEnoughPoints.{u} (nisnevichTopology S) :=
  hasEnoughPoints_nisnevichTopology.{u,0} S

/-- The same neighborhood diagrams give enough points in the universe of the
large transfer coefficient sheaves. -/
instance nisnevichTopology_hasEnoughPoints_succ (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    GrothendieckTopology.HasEnoughPoints.{u+1} (nisnevichTopology S) :=
  hasEnoughPoints_nisnevichTopology.{u,u+1} S

end AlgebraicGeometry.Scheme.SmoothSite

attribute [colib_ref "MorelVoevodsky1999" "Section 3.1, pp. 99–100, before Lemma 1.11"
  "adaptation" "The conservative Nisnevich family with fibers from affine neighborhoods"]
  AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology_hasEnoughPoints

namespace AlgebraicGeometry.Scheme.SmoothSite

attribute [colib_tag "COL-1010"]
  nisnevichTopology_hasEnoughPoints
  nisnevichTopology_hasEnoughPoints_succ

end AlgebraicGeometry.Scheme.SmoothSite
