/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import Colib.AlgebraicGeometry.Correspondences.Incidence
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SchemeTheoreticImage

/-!
# Finite pushforward of native algebraic cycles

This geometric application uses the finite pushforward defined directly from
`AlgebraicGeometry.AlgebraicCycle.map` in `Chow.FinitePushforward`.
Thus every coefficient is the sum over the entire fibre, with the actual residue
field degree. Distinct source points are allowed to have the same image.
The references to Tags 02R4 and 02R5 concern their finite-morphism formulas;
the present cycle group is ungraded, without a chosen dimension function.

The native cycle type and its local-finiteness proof are reused unchanged.
Composition uses the native weighted pushforward composition theorem and
multiplicativity of the residue degree. No Chow quotient is used here.

The integral closed image is proved finite over the source when the ambient
projection is separated and locally of finite type and the original support is
finite over the source. The scheme-theoretic image is proper by Stacks 0AH6, its
fibres are finite by surjectivity from the original finite scheme, and Zariski Main
(Tag 02LS) gives finiteness. The component-image hypothesis is still separate.
The actual correspondence subgroup and incidence constructions below preserve it
explicitly; nonverticality is not inferred from finiteness of the incidence projection.

The incidence cycle remains an input. It is not replaced by the fundamental cycle
of the fibre product: selecting the correct Tor intersection cycle is a separate
construction. No associativity statement is asserted by this module.

The migration context is `kangxyz/motivic` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`. This implementation is constructed
independently from the native Mathlib and Stacks APIs cited below. It does not
claim historical byte recovery or a checked comparison with the original
composition construction.

## References

* Stacks Project, Tag 02R4: proper pushforward and its residue-degree coefficient.
* Stacks Project, Tag 02R5: functoriality of proper pushforward.
* Stacks Project, Tag 09G9: multiplicativity of degrees in towers of fields.
* Stacks Project, Tag 0AH6: properness of the scheme-theoretic image.
* Stacks Project, Tag 02LS: proper and quasi-finite implies finite.
* The image identification uses Stacks
  `Chow/ChernCapPushforward/ComponentDegree.lean`, `map_integralComponentAt`,
  directly. No duplicate image-identification theorem is introduced.
* Mathlib `AlgebraicGeometry/AlgebraicCycle/Basic.lean`, revision
  `56a005855ea17e0b0958f73ec801ae140b0a1679`.
* Stacks `Chow/ProperPushforwardChow/Functoriality.lean` and
  `Chow/ProperPushforwardPrincipal/ResidueTrdeg.lean`, revision
  `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Classical.propDecidable

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X Y Z : Scheme.{u}}

/-! ## Finiteness of the actual integral closed image -/

/-- The scheme-theoretic image of a scheme finite over the base is finite over
that base when the ambient projection is separated and locally of finite type.
The image is the native `Scheme.Hom.image`, not a replacement support scheme. -/
@[stacks 0AH6 "properness and surjectivity of the scheme-theoretic image are inputs",
  stacks 02LS "proper with finite fibres implies finite, applied to the scheme-theoretic image"]
theorem finiteCyclePushforward_isFinite_imageι_comp
    {A B S : Scheme.{u}} (r : A ⟶ B) (p : B ⟶ S)
    [IsFinite (r ≫ p)] [IsSeparated p] [LocallyOfFiniteType p] :
    IsFinite (r.imageι ≫ p) := by
  have : Surjective r.toImage := AlgebraicGeometry.surjective_toImage r p
  have : IsProper (r.imageι ≫ p) := AlgebraicGeometry.isProper_imageι_comp r p
  have hfib (s : S) : ((r.imageι ≫ p) ⁻¹' {s}).Finite := by
    refine (((r ≫ p).finite_preimage_singleton s).image r.toImage).subset ?_
    intro z hz
    obtain ⟨x, rfl⟩ := r.toImage.surjective z
    refine ⟨x, ?_, rfl⟩
    change (r.imageι ≫ p) (r.toImage x) = s at hz
    change (r ≫ p) x = s
    simpa [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base] using hz
  have : LocallyQuasiFinite (r.imageι ≫ p) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ hfib
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Finiteness over the base of the original support implies finiteness of the
actual integral closed image support, under the stated ambient hypotheses. -/
theorem finiteCyclePushforward_isFinite_integralComponentAt
    {S : Scheme.{u}} (r : X ⟶ Y) (p : Y ⟶ S)
    [IsSeparated p] [LocallyOfFiniteType p] (x : X)
    (hx : IsFinite (((integralComponentAt x).subschemeι ≫ r) ≫ p)) :
    IsFinite ((integralComponentAt (r.base x)).subschemeι ≫ p) := by
  have := hx
  have himage : IsFinite (((integralComponentAt x).map r).subschemeι ≫ p) :=
    finiteCyclePushforward_isFinite_imageι_comp ((integralComponentAt x).subschemeι ≫ r) p
  exact (congrArg (fun I : Y.IdealSheafData ↦ IsFinite (I.subschemeι ≫ p))
    (map_integralComponentAt r x)).mp himage

/-- Under a finite map, the support of the image component is the actual image
of the original closed support, without an additional closure. -/
theorem finiteCyclePushforward_image_support (r : X ⟶ Y) [IsFinite r] (x : X) :
    r.base '' ((integralComponentAt x).support : Set X) =
      ((integralComponentAt (r.base x)).support : Set Y) := by
  simp only [coe_support_integralComponentAt]
  simpa only [Set.image_singleton] using
    (r.isClosedMap.closure_image_eq_of_continuous r.continuous ({x} : Set X)).symm

/-- Transport the actual projected closed-support image. This is the geometric
identity needed to carry, rather than remove, the incidence component hypothesis. -/
theorem finiteCyclePushforward_projected_support (r : X ⟶ Y) [IsFinite r]
    {S : Scheme.{u}} (p : Y ⟶ S) (x : X) :
    p.base '' ((integralComponentAt (r.base x)).support : Set Y) =
      (r ≫ p).base '' ((integralComponentAt x).support : Set X) := by
  rw [← finiteCyclePushforward_image_support r x, Set.image_image]
  rfl

/-- Finiteness alone does not supply this conclusion: the image being a source
component is an explicit hypothesis, transported along the finite map. -/
theorem finiteCyclePushforward_image_mem_irreducibleComponents
    (r : X ⟶ Y) [IsFinite r] {S : Scheme.{u}} (p : Y ⟶ S) (x : X)
    (hcomp : (r ≫ p).base '' ((integralComponentAt x).support : Set X) ∈
      irreducibleComponents S) :
    p.base '' ((integralComponentAt (r.base x)).support : Set Y) ∈
      irreducibleComponents S := by
  rwa [finiteCyclePushforward_projected_support r p x]


/-! ## The actual finite-correspondence subgroup -/

/-- The range of the projected integral support is its actual set-theoretic image. -/
theorem finiteCyclePushforward_range_integralComponentAt
    (p : X ⟶ Y) (x : X) :
    Set.range ((integralComponentAt x).subschemeι ≫ p) =
      p.base '' ((integralComponentAt x).support : Set X) := by
  change Set.range (p.base ∘ (integralComponentAt x).subschemeι.base) = _
  rw [Set.range_comp, (integralComponentAt x).range_subschemeι]

/-- The native finite pushforward lands in the actual native finite-correspondence
subgroup when each nonzero input support is finite over the source and its
projected image is an irreducible source component. Cancellation and collisions
are allowed: a nonzero output coefficient only requires some contributing point. -/
theorem finiteCyclePushforward_mem_finiteCorrespondences
    {S A : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsSeparated g] [LocallyOfFiniteType g]
    (r : A ⟶ CategoryTheory.Limits.pullback f g) [IsFinite r]
    (c : AlgebraicCycle A ℤ) (hc : c.support.Finite)
    (hfin : ∀ a, c a ≠ 0 →
      IsFinite (((integralComponentAt a).subschemeι ≫ r) ≫
        CategoryTheory.Limits.pullback.fst f g))
    (hcomp : ∀ a, c a ≠ 0 →
      Set.range (((integralComponentAt a).subschemeι ≫ r) ≫
        CategoryTheory.Limits.pullback.fst f g) ∈ irreducibleComponents X) :
    finiteCyclePushforward r c ∈ finiteCorrespondences f g := by
  refine (mem_finiteCorrespondences f g _).mpr
    ⟨finiteCyclePushforward_finite_support r c hc, ?_⟩
  intro y hy
  obtain ⟨a, ha, rfl⟩ := finiteCyclePushforward_support_subset r c hy
  refine ⟨finiteCyclePushforward_isFinite_integralComponentAt r
    (CategoryTheory.Limits.pullback.fst f g) a (hfin a ha), ?_⟩
  have hcomp' : (r ≫ CategoryTheory.Limits.pullback.fst f g).base ''
      ((integralComponentAt a).support : Set A) ∈ irreducibleComponents X := by
    simpa only [Category.assoc, finiteCyclePushforward_range_integralComponentAt] using
      hcomp a ha
  simpa only [finiteCyclePushforward_range_integralComponentAt] using
    finiteCyclePushforward_image_mem_irreducibleComponents r
      (CategoryTheory.Limits.pullback.fst f g) a hcomp'

/-! ## Incidence pushforward, retaining the component-image hypothesis -/

open CategoryTheory.Limits in
/-- The incidence scheme is finite over the source for admissible original supports. -/
theorem isFinite_correspondenceIncidenceLeft
    {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z)
    (hw : IsFiniteCorrespondencePoint g h w) :
    IsFinite (correspondenceIncidenceLeft f g h z w) := by
  have : IsFinite ((integralComponentAt z).subschemeι ≫ pullback.fst f g) := hz.1
  have : IsFinite ((integralComponentAt w).subschemeι ≫ pullback.fst g h) := hw.1
  dsimp [correspondenceIncidenceLeft]
  infer_instance

open CategoryTheory.Limits in
/-- Push the actual incidence cycle into the native correspondence subgroup.
The explicit `hcomp` is the nonverticality input: every relevant component of the
incidence cycle must project onto an irreducible component of the source. -/
def incidencePushforward
    {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsSeparated h] [LocallyOfFiniteType h]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z)
    (hw : IsFiniteCorrespondencePoint g h w)
    (c : AlgebraicCycle (correspondenceIncidence f g h z w) ℤ)
    (hc : c.support.Finite)
    (hcomp : ∀ t, c t ≠ 0 →
      Set.range ((integralComponentAt t).subschemeι ≫
        correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X) :
    finiteCorrespondences f h := by
  have : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  refine ⟨finiteCyclePushforward (correspondenceIncidenceMap f g h z w) c,
    finiteCyclePushforward_mem_finiteCorrespondences f h
      (correspondenceIncidenceMap f g h z w) c hc ?_ ?_⟩
  · intro t ht
    have : IsFinite (correspondenceIncidenceLeft f g h z w) :=
      isFinite_correspondenceIncidenceLeft f g h z w hz hw
    have hfinite : IsFinite ((integralComponentAt t).subschemeι ≫
        correspondenceIncidenceLeft f g h z w) := inferInstance
    simpa only [Category.assoc, correspondenceIncidenceMap_fst] using hfinite
  · intro t ht
    simpa only [Category.assoc, correspondenceIncidenceMap_fst] using hcomp t ht

open CategoryTheory.Limits in
/-- Incidence pushforward retains the complete native residue-degree coefficient,
including the sum of the contributions of every colliding incidence component. -/
theorem incidencePushforward_apply
    {S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsSeparated h] [LocallyOfFiniteType h]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z)
    (hw : IsFiniteCorrespondencePoint g h w)
    (c : AlgebraicCycle (correspondenceIncidence f g h z w) ℤ)
    (hc : c.support.Finite)
    (hcomp : ∀ t, c t ≠ 0 →
      Set.range ((integralComponentAt t).subschemeι ≫
        correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X)
    (y : pullback (C := Scheme) f h) :
    (incidencePushforward f g h z w hz hw c hc hcomp).1 y =
      ∑ᶠ t ∈ (correspondenceIncidenceMap f g h z w).base ⁻¹' {y},
        c t * ((correspondenceIncidenceMap f g h z w).residueDegree t : ℤ) := by
  have : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  exact finiteCyclePushforward_apply (correspondenceIncidenceMap f g h z w) c y

end Stacks.Chow
