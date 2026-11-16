/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.TwoChartMiddle
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Natural splittings of the original two-chart middle row

A natural retraction of the common coefficient map splits its original cokernel row. An actual
Laurent section whose original quotient is invertible defines a canonical quotient boundary,
with precisely that section. If the original middle row is exact, its descended difference and
the canonical boundary form a second naturally split row. Every additive functor preserves this
specific middle exactness using these two constructed splittings. No general preservation of
middle exactness by a right-exact functor is asserted.

Source: `Quillen/KTheory/Bass/TwoChartSplitExact.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace KTheory.Bass.TwoChart
variable {D : Type u} [Category.{w} D] {P L : D ⥤ D}
variable (c : 𝟭 D ⟶ P) (p m : P ⟶ L) (h : c ≫ p = c ≫ m)

private theorem exact_of_evaluation (S : ShortComplex (D ⥤ AddCommGrpCat.{v}))
    (hS : ∀ X, (S.map ((evaluation D AddCommGrpCat).obj X)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext X
  change 𝟙 (S.homology.obj X) = 0
  exact (IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (hS X))
    (S.mapHomologyIso ((evaluation D AddCommGrpCat).obj X)).symm).eq_of_src _ _

/-- Pointwise exactness of the original chart maps gives exactness of their natural middle row.
-/
theorem middleComplex_exact_of_pointwise (F : D ⥤ AddCommGrpCat.{v})
    (hF : ∀ X, Function.Exact ((middleCorner c p m F).app X)
      ((middleDifference p m F).app X)) : (middleComplex c p m h F).Exact :=
  exact_of_evaluation _ (fun X => (ShortComplex.ab_exact_iff_function_exact _).mpr (hF X))

/-- The first chart projection followed by the specified original coefficient retraction. -/
def middleCornerRetraction (e : P ⟶ 𝟭 D) (F : D ⥤ AddCommGrpCat.{v}) :
    polynomialDifferenceDiagram p m F ⋙ Arrow.leftFunc ⟶ F where
  app X := biprod.fst ≫ F.map (e.app X)
  naturality {X Y} f := by
    change biprod.map _ _ ≫ biprod.fst ≫ _ = (biprod.fst ≫ _) ≫ _
    rw [biprod.map_fst_assoc, Category.assoc, ← F.map_comp, ← F.map_comp]
    exact congrArg (fun k => biprod.fst ≫ F.map k) (e.naturality f)

/-- The actual natural common corner is split by its specified coefficient retraction. -/
@[reassoc (attr := simp)]
theorem middleCorner_retraction (e : P ⟶ 𝟭 D) (he : c ≫ e = 𝟙 (𝟭 D))
    (F : D ⥤ AddCommGrpCat.{v}) :
    middleCorner c p m F ≫ middleCornerRetraction p m e F = 𝟙 F := by
  apply NatTrans.ext
  funext X
  change biprod.lift _ _ ≫ biprod.fst ≫ _ = _
  rw [biprod.lift_fst_assoc, ← F.map_comp]
  have hx := NatTrans.congr_app he X
  change c.app X ≫ e.app X = 𝟙 X at hx
  rw [hx]
  exact F.map_id X

/-- The original corner cokernel row is naturally split, using its original retraction. -/
def middleCornerSplitting (e : P ⟶ 𝟭 D) (he : c ≫ e = 𝟙 (𝟭 D))
    (F : D ⥤ AddCommGrpCat.{v}) :
    (ShortComplex.cokernelSequence (middleCorner c p m F)).Splitting :=
  ShortComplex.Splitting.ofExactOfRetraction _
    (ShortComplex.cokernelSequence_exact (middleCorner c p m F))
    (middleCornerRetraction p m e F) (middleCorner_retraction c p m e he F) inferInstance

/-- The original signed difference descends through the original common-corner cokernel. -/
def middleDifferenceDesc (F : D ⥤ AddCommGrpCat.{v}) :
    cokernel (middleCorner c p m F) ⟶ L ⋙ F :=
  cokernel.desc _ (middleDifference p m F) (middleCorner_difference c p m h F)

/-- The descended map retains the unchanged original difference representative. -/
@[reassoc (attr := simp)]
theorem middleDifferenceDesc_π (F : D ⥤ AddCommGrpCat.{v}) :
    cokernel.π (middleCorner c p m F) ≫ middleDifferenceDesc c p m h F =
      middleDifference p m F := cokernel.π_desc _ _ _

variable (F G : D ⥤ AddCommGrpCat.{v}) (s : G ⟶ L ⋙ F)
variable [IsIso (s ≫ contractionπ p m F)]

/-- The canonical boundary determined by the actual section and original Laurent quotient. -/
def unitQuotientBoundary : L ⋙ F ⟶ G :=
  contractionπ p m F ≫ inv (s ≫ contractionπ p m F)

/-- The specified actual Laurent section splits the same canonical quotient boundary. -/
@[reassoc (attr := simp)]
theorem section_unitQuotientBoundary : s ≫ unitQuotientBoundary p m F G s = 𝟙 G := by
  rw [unitQuotientBoundary, ← Category.assoc, IsIso.hom_inv_id]

/-- The original signed difference is killed by the same canonical quotient boundary. -/
@[reassoc (attr := simp)]
theorem middleDifference_unitQuotientBoundary :
    middleDifference p m F ≫ unitQuotientBoundary p m F G s = 0 := by
  apply NatTrans.ext
  funext X
  change polynomialDifference p m F X ≫
    (contractionπ p m F).app X ≫ _ = 0
  rw [polynomialDifference_contractionπ_assoc, zero_comp]

/-- The actual natural boundary row, with its original chart difference. -/
def unitQuotientBoundarySequence : ShortComplex (D ⥤ AddCommGrpCat.{v}) :=
  ShortComplex.mk (middleDifference p m F) (unitQuotientBoundary p m F G s)
    (middleDifference_unitQuotientBoundary p m F G s)

/-- The canonical quotient boundary has exactly the original chart-difference kernel. -/
theorem unitQuotientBoundarySequence_exact : (unitQuotientBoundarySequence p m F G s).Exact := by
  apply exact_of_evaluation
  intro X
  let φ : ShortComplex.mk (polynomialDifference p m F X) ((contractionπ p m F).app X)
      (polynomialDifference_contractionπ p m F X) ⟶
      (unitQuotientBoundarySequence p m F G s).map ((evaluation D AddCommGrpCat).obj X) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (inv (s ≫ contractionπ p m F)).app X
      comm₁₂ := by simp [unitQuotientBoundarySequence, middleDifference]
      comm₂₃ := by simp [unitQuotientBoundarySequence, unitQuotientBoundary] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp (contraction_exact p m F X)

/-- The original descended difference and the same canonical boundary form the second row. -/
def splitUnitQuotientBoundarySequence : ShortComplex (D ⥤ AddCommGrpCat.{v}) :=
  ShortComplex.mk (middleDifferenceDesc c p m h F) (unitQuotientBoundary p m F G s) (by
    apply (cancel_epi (cokernel.π (middleCorner c p m F))).mp
    rw [← Category.assoc, middleDifferenceDesc_π, comp_zero]
    exact middleDifference_unitQuotientBoundary p m F G s)

/-- Passing through the original corner cokernel preserves exactness of the boundary row. -/
theorem splitUnitQuotientBoundarySequence_exact :
    (splitUnitQuotientBoundarySequence c p m h F G s).Exact := by
  let φ : unitQuotientBoundarySequence p m F G s ⟶
      splitUnitQuotientBoundarySequence c p m h F G s :=
    { τ₁ := cokernel.π (middleCorner c p m F)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        simp [unitQuotientBoundarySequence, splitUnitQuotientBoundarySequence]
      comm₂₃ := by simp [unitQuotientBoundarySequence, splitUnitQuotientBoundarySequence] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
    (unitQuotientBoundarySequence_exact p m F G s)

/-- Original middle exactness makes the descended difference monic, and the actual section
constructs a genuine natural splitting of the second row. -/
def unitQuotientBoundarySplitting (hF : (middleComplex c p m h F).Exact) :
    (splitUnitQuotientBoundarySequence c p m h F G s).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    (splitUnitQuotientBoundarySequence_exact c p m h F G s) s
    (section_unitQuotientBoundary p m F G s) hF.mono_cokernelDesc

include s in
/-- Any additive endofunctor preserves this specific original middle row, using its two
constructed natural splittings. -/
theorem middleComplex_map_exact (e : P ⟶ 𝟭 D) (he : c ≫ e = 𝟙 (𝟭 D))
    (hF : (middleComplex c p m h F).Exact)
    (T : (D ⥤ AddCommGrpCat.{v}) ⥤ (D ⥤ AddCommGrpCat.{v})) [T.Additive] :
    ((middleComplex c p m h F).map T).Exact := by
  let : Mono (T.map (middleDifferenceDesc c p m h F)) :=
    ((unitQuotientBoundarySplitting c p m h F G s hF).map T).mono_f
  let φ : (ShortComplex.cokernelSequence (middleCorner c p m F)).map T ⟶
      (middleComplex c p m h F).map T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := T.map (middleDifferenceDesc c p m h F)
      comm₁₂ := by simp [middleComplex]
      comm₂₃ := by
        symm
        change T.map (cokernel.π (middleCorner c p m F)) ≫
          T.map (middleDifferenceDesc c p m h F) = 𝟙 _ ≫ T.map (middleDifference p m F)
        rw [← T.map_comp, middleDifferenceDesc_π, Category.id_comp] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
    ((middleCornerSplitting c p m e he F).map T).exact

end KTheory.Bass.TwoChart
