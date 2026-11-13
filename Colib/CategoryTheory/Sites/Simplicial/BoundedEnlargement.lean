/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.BoundedDeformationWitness
public import Colib.CategoryTheory.Sites.Simplicial.BoundedFiberSections
public import Colib.Topology.Realization.FiniteSubcomplexCardinal
public import Colib.Topology.Realization.MapWeakEquivalence
public import Colib.Topology.Realization.RestrictedDeformation
import Colib.CategoryTheory.Sites.Simplicial.ReducedConeContraction
import Colib.Topology.Realization.WeakHomotopyEquiv

/-!
# One bounded enlargement for site-fiber deformation witnesses

A bounded family of points and all finite subcomplexes in the current
fibers give a bounded family of homotopy supports. Their union enlarges
the subpresheaf while retaining the original inverse image. This is the
successor step of Jardine, *Simplicial presheaves*, Lemma 2.4, pp. 65–66.
https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval

universe t w v u

namespace CategoryTheory.SimplicialSubpresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ SSet.{w}} (f : P ⟶ Q)

private theorem hasCardinalLT_finiteFiberSubcomplexes
    (Φ : J.Point.{w}) (A : Subpresheaf Q) (κ : Cardinal.{t}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) (hA : HasBoundedSections A κ)
    (hΦ : ∀ U : C, HasCardinalLT (Φ.fiber.obj U) κ) :
    HasCardinalLT {K : (Φ.presheafFiber.obj (toPresheaf A)).Subcomplex // SSet.Finite K} κ := by
  apply SSet.hasCardinalLT_finiteSubcomplexes _ κ hκ
  have h := Φ.hasCardinalLT_presheafFiber_totalSimplices (toPresheaf A) κ hA hΦ
  let X := Φ.presheafFiber.obj (toPresheaf A)
  let code (s : X.Elements) : Σ n, X.obj n := ⟨s.obj, s.val⟩
  have hcode : Function.Injective code := by
    intro a b e
    exact congrArg (fun s : Σ n, X.obj n => X.elementsMk s.1 s.2) e
  exact h.of_injective (fun s : X.N => code (SSet.S.equivElements s.toS))
    (fun _ _ e => (SSet.N.ext_iff _ _).2 (SSet.S.equivElements.injective (hcode e)))

private theorem exists_homotopy_support
    (Φ : J.Point.{w}) (A : Subpresheaf Q) {K : (Φ.presheafFiber.obj (toPresheaf A)).Subcomplex}
    [SSet.Finite K]
    (R : TopCat.CylinderStrongDeformationRetract (SSet.toTop.map (Φ.presheafFiber.map f)))
    (κ : Cardinal.{t}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hC : ∀ q : Cᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ) :
    ∃ D : Subpresheaf Q, HasBoundedSections D κ ∧
      ∃ H : SSet.toTop.obj K ⊗ TopCat.I ⟶ SSet.toTop.obj (Φ.presheafFiber.obj (toPresheaf D)),
        H ≫ SSet.toTop.map (Φ.presheafFiber.map (inclusion D)) =
          (SSet.toTop.map (K.ι ≫ Φ.presheafFiber.map (inclusion A)) ▷ TopCat.I) ≫ R.H := by
  let l := K.ι ≫ Φ.presheafFiber.map (inclusion A)
  let L := SSet.Subcomplex.range l
  obtain ⟨_, _, D, hD, _, H, _, hH⟩ := exists_bounded_deformation_witness Φ f R L κ hκ hC
  refine ⟨D, hD, (SSet.toTop.map (SSet.Subcomplex.toRange l) ▷ TopCat.I) ≫ H, ?_⟩
  rw [Category.assoc, hH, ← Category.assoc, ← comp_whiskerRight, ← Functor.map_comp,
    SSet.Subcomplex.toRange_ι]

/-- One bounded enlargement supplies a relative lift of every finite
subcomplex of the old fiber through the inverse image of the enlarged one. -/
theorem exists_bounded_enlargement_of_weakEquivalences [Mono f]
    {ι : Type*} (point : ι → J.Point.{w}) (A : Subpresheaf Q)
    (hf : ∀ i, SSet.IsRealizationWeakEquivalence ((point i).presheafFiber.map f))
    (κ : Cardinal.{t}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hI : HasCardinalLT ι κ) (hA : HasBoundedSections A κ)
    (hC : ∀ q : Cᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ)
    (hPoint : ∀ i (U : C), HasCardinalLT ((point i).fiber.obj U) κ) :
    ∃ D : Subpresheaf Q, ∃ hAD : A ≤ D, HasBoundedSections D κ ∧
      ∀ (i : ι) (K : ((point i).presheafFiber.obj (toPresheaf A)).Subcomplex), SSet.Finite K →
        ∃ (r : C(|(K : SSet.{w})|,
          |(point i).presheafFiber.obj (toPresheaf (preimage D f))|))
          (H : ContinuousMap.Homotopy
            ((SSet.toTop.map ((point i).presheafFiber.map (preimageMap D f))).hom.comp r)
            (SSet.toTop.map (K.ι ≫ (point i).presheafFiber.map (homOfLE hAD))).hom),
          ∀ (t : unitInterval) (x : |(K : SSet.{w})|),
            (SSet.toTop.map (K.ι ≫ (point i).presheafFiber.map (homOfLE hAD))) x ∈
              Set.range (SSet.toTop.map ((point i).presheafFiber.map (preimageMap D f))) →
            H (t, x) = (SSet.toTop.map (K.ι ≫ (point i).presheafFiber.map (homOfLE hAD))) x := by
  have hmono (i : ι) {X Y : Cᵒᵖ ⥤ SSet.{w}} (g : X ⟶ Y) [Mono g] :
      Mono ((point i).presheafFiber.map g) := by
    let E := (point i).presheafFiber (A := SSet.{w})
    let hE : PreservesFiniteLimits E := inferInstanceAs
      (PreservesFiniteLimits ((point i).presheafFiber (A := SSet.{w})))
    let : PreservesLimitsOfShape WalkingCospan E := hE.preservesFiniteLimits WalkingCospan
    let : PreservesLimit (cospan g g) E := PreservesLimitsOfShape.preservesLimit
    exact preserves_mono_of_preservesLimit E g
  have hR (i : ι) : Nonempty (TopCat.CylinderStrongDeformationRetract
      (SSet.toTop.map ((point i).presheafFiber.map f))) := by
    let : Mono ((point i).presheafFiber.map f) := hmono i f
    exact TopCat.homotopyExtensionProperty_strongDeformationRetract
      (SSet.homotopyExtensionProperty_realization_mono _) (hf i).homotopyEquiv
      (hf i).homotopyEquiv_toFun
  let R := fun i => (hR i).some
  let KSet (i : ι) := {K : ((point i).presheafFiber.obj (toPresheaf A)).Subcomplex // SSet.Finite K}
  have hs (j : Σ i, KSet i) := by
    let : SSet.Finite j.2.val := j.2.property
    exact exists_homotopy_support f (point j.1) A (K := j.2.val) (R j.1) κ hκ hC
  choose B hB H hH using hs
  let B' : Option (Σ i, KSet i) → Subpresheaf Q := fun j => j.elim A B
  let D := ⨆ j, B' j
  have hAD : A ≤ D := le_iSup B' none
  have hD : HasBoundedSections D κ := Subfunctor.hasCardinalLT_totalSections_iSup B' κ
    ((hasCardinalLT_option_iff _ κ hκ.le).2
      (hasCardinalLT_sigma KSet κ hI (fun i =>
        hasCardinalLT_finiteFiberSubcomplexes (point i) A κ hκ hA (hPoint i))))
    (fun j => Option.casesOn j hA hB)
  refine ⟨D, hAD, hD, ?_⟩
  intro i K hK
  let j : Σ i, KSet i := ⟨i, K, hK⟩
  let E := (point i).presheafFiber (A := SSet.{w})
  let : Mono (E.map f) := hmono i f
  let : Mono (E.map (inclusion D)) := hmono i (inclusion D)
  let hBD : B j ≤ D := le_iSup B' (some j)
  let l := K.ι ≫ E.map (homOfLE hAD)
  let HH := H j ≫ SSet.toTop.map (E.map (homOfLE hBD))
  have hHH : HH ≫ SSet.toTop.map (E.map (inclusion D)) =
      (SSet.toTop.map (l ≫ E.map (inclusion D)) ▷ TopCat.I) ≫ (R i).H := by
    dsimp only [HH, l]
    rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, homOfLE_inclusion,
      Category.assoc, ← Functor.map_comp, homOfLE_inclusion]
    exact hH j
  let hE : PreservesFiniteLimits E := inferInstanceAs
    (PreservesFiniteLimits ((point i).presheafFiber (A := SSet.{w})))
  let : PreservesLimitsOfShape WalkingCospan E := hE.preservesFiniteLimits WalkingCospan
  exact SSet.exists_relativeHomotopy_of_factored_deformation
    ((preimage_isPullback D f).map E) (R i) l HH hHH

end CategoryTheory.SimplicialSubpresheaf
