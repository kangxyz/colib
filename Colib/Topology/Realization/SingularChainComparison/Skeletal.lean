/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Realization.SingularChainComparison
public import Colib.Topology.Realization.SingularChainComparison.StandardSimplex
public import Colib.Topology.Realization.SingularChainComparison.Colimits
public import Colib.Topology.Realization.Skeleton
public import Colib.Topology.Realization.MonomorphismEmbedding
public import Colib.Algebra.Homology.HomologicalComplex.QuasiIsoMiddle
public import Colib.Topology.LocalCoefficients.EmbeddingSquareChains
public import Colib.Topology.LocalCoefficients.SimplexAttachmentExcision
public import Colib.Topology.LocalCoefficients.IntegralChains
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Relative comparisons for skeletal attachments

The relative comparison is the map between the actual cokernels induced by the
adjunction unit. Short exact sequences relate it to the two absolute comparisons.
The geometric input below translates the existing simplex-attachment excision
theorem from image-subspace relative chains to the cokernels of the original
embedding chain maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Simplicial chains preserve colimits, as is seen on each free chain object. -/
lemma chainComplexFunctorObj_preservesColimitsOfShape (R : C)
    (J : Type*) [Category* J] [HasColimitsOfShape J (Type w)] :
    PreservesColimitsOfShape J ((chainComplexFunctor.{w} C).obj R) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J
    ((evaluation SimplexCategoryᵒᵖ (Type w)).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj R)
  infer_instance

/-- The unit comparison on the actual relative chain cokernels. -/
def realizationRelativeChainComparison {A X : SSet.{w}} (i : A ⟶ X) (R : C) :
    cokernel (chainComplexMap i R) ⟶
      cokernel (((singularChainComplexFunctor C).obj R).map (SSet.toTop.map i)) :=
  cokernel.map _ _ (realizationChainComparison A R) (realizationChainComparison X R)
    (realizationChainComparison_naturality i R)

/-- The relative comparison retains the original absolute unit on quotient maps. -/
@[reassoc (attr := simp)]
lemma realizationRelativeChainComparison_quotient {A X : SSet.{w}} (i : A ⟶ X) (R : C) :
    cokernel.π (chainComplexMap i R) ≫ realizationRelativeChainComparison i R =
      realizationChainComparison X R ≫
        cokernel.π (((singularChainComplexFunctor C).obj R).map (SSet.toTop.map i)) :=
  cokernel.π_desc _ _ _

private def realizationRelativeChainComparisonDiagram
    {A X : SSet.{w}} (i : A ⟶ X) (R : C) :
    ShortComplex.mk (chainComplexMap i R) (cokernel.π _) (cokernel.condition _) ⟶
      ShortComplex.mk
        (((singularChainComplexFunctor C).obj R).map (SSet.toTop.map i))
        (cokernel.π _) (cokernel.condition _) where
  τ₁ := realizationChainComparison A R
  τ₂ := realizationChainComparison X R
  τ₃ := realizationRelativeChainComparison i R
  comm₁₂ := (realizationChainComparison_naturality i R).symm
  comm₂₃ := (realizationRelativeChainComparison_quotient i R).symm

/-- Absolute unit comparisons induce the relative quasi-isomorphism for an actual
monic chain inclusion and its realized singular-chain inclusion. -/
lemma quasiIso_realizationRelativeChainComparison {A X : SSet.{w}}
    (i : A ⟶ X) (R : C) [Mono (chainComplexMap i R)]
    [Mono (((singularChainComplexFunctor C).obj R).map (SSet.toTop.map i))]
    (hA : QuasiIso (realizationChainComparison A R))
    (hX : QuasiIso (realizationChainComparison X R)) :
    QuasiIso (realizationRelativeChainComparison i R) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (realizationRelativeChainComparisonDiagram i R)
    { exact := ShortComplex.exact_cokernel _ }
    { exact := ShortComplex.exact_cokernel _ } hA hX

/-- The old-stage and relative unit comparisons imply the absolute comparison
on the next stage, including homological degree zero. -/
lemma quasiIso_realizationChainComparison_of_relative {A X : SSet.{w}}
    (i : A ⟶ X) (R : C) [Mono (chainComplexMap i R)]
    [Mono (((singularChainComplexFunctor C).obj R).map (SSet.toTop.map i))]
    (hA : QuasiIso (realizationChainComparison A R))
    (hrel : QuasiIso (realizationRelativeChainComparison i R)) :
    QuasiIso (realizationChainComparison X R) :=
  HomologicalComplex.quasiIso_middle_of_shortExact
    (realizationRelativeChainComparisonDiagram i R)
    { exact := ShortComplex.exact_cokernel _ }
    { exact := ShortComplex.exact_cokernel _ } hA hrel

end SSet

namespace FundamentalGroupoid.LocalCoefficients

variable {X₀ X₁ Y₀ Y₁ : Type u}
  [TopologicalSpace X₀] [TopologicalSpace X₁]
  [TopologicalSpace Y₀] [TopologicalSpace Y₁]

private lemma embeddingSquareCokernelMap_quasiIso_of_range
    (j : C(X₀, X₁)) (k : C(Y₀, Y₁)) (a : C(X₀, Y₀)) (b : C(X₁, Y₁))
    (w : b.comp j = k.comp a) (hj : Topology.IsEmbedding j) (hk : Topology.IsEmbedding k)
    (A : System.{u, u} Y₁) (hr : Set.MapsTo b (Set.range j) (Set.range k))
    (h : QuasiIso (relativePushforwardChainMap b (Set.range j) (Set.range k) hr A)) :
    QuasiIso (embeddingSquareCokernelMap j k a b w A) := by
  let eS := embeddingCokernelIsoRelative j hj (pullback b A)
  let eT := embeddingCokernelIsoRelative k hk A
  have he : embeddingSquareCokernelMap j k a b w A ≫ eT.hom =
      eS.hom ≫ relativePushforwardChainMap b (Set.range j) (Set.range k) hr A := by
    apply (cancel_epi (cokernel.π (pushforwardChainMap j (pullback b A)))).mp
    simp only [eS, eT, embeddingSquareCokernelMap_quotient_assoc,
      embeddingCokernelIsoRelative_quotient, embeddingCokernelIsoRelative_quotient_assoc]
    exact (relativePushforwardChainMap_quotient b (Set.range j) (Set.range k) hr A).symm
  have : QuasiIso (embeddingSquareCokernelMap j k a b w A ≫ eT.hom) := by
    rw [he]
    infer_instance
  exact quasiIso_of_comp_right _ eT.hom

/-- Excision for a parameterized simplex attachment, expressed on the cokernels
of the actual boundary inclusion and old-stage inclusion. -/
theorem simplexAttachment_embeddingSquareCokernelMap_quasiIso
    (P : TopCat.{u}) (n : ℕ) {B D : TopCat.{u}}
    {f : TopCat.of (P × Convexity.StdSimplex.boundary n) ⟶ B}
    {g : TopCat.of (P × Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : B ⟶ D}
    (sq : IsPushout (TopCat.parameterizedSimplexBoundaryInclusion P n) f g j)
    (L : System.{u, u} D) :
    QuasiIso (embeddingSquareCokernelMap
      (TopCat.parameterizedSimplexBoundaryInclusion P n).hom j.hom f.hom g.hom
      (congrArg TopCat.Hom.hom sq.w) L) := by
  let hr : Set.MapsTo g.hom
      (Set.range (TopCat.parameterizedSimplexBoundaryInclusion P n)) (Set.range j) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨f z, ConcreteCategory.congr_hom sq.w z |>.symm⟩
  apply embeddingSquareCokernelMap_quasiIso_of_range
      _ _ _ _ _ (TopCat.isClosedEmbedding_parameterizedSimplexBoundary P n).isEmbedding
      (TopCat.simplexAttachment_old_isClosedEmbedding P n sq).isEmbedding L hr
  have hrange : Set.range (TopCat.parameterizedSimplexBoundaryInclusion P n).hom =
      TopCat.SimplexAttachment.sourceBoundary P n :=
    TopCat.SimplexAttachment.range_boundaryInclusion P n
  have hrel (U : Set (P × Convexity.StdSimplex ℝ (Fin (n + 1))))
      (hU : U = TopCat.SimplexAttachment.sourceBoundary P n)
      (hmap : Set.MapsTo g.hom U (Set.range j)) :
      QuasiIso (relativePushforwardChainMap g.hom U (Set.range j) hmap L) := by
    subst U
    exact simplexAttachmentCell_relative_quasiIso P n sq L
  exact hrel _ hrange hr

/-- Constant local-coefficient relative cokernels identify with the cokernels of
Mathlib's actual singular-chain maps. -/
def constantChainCokernelIso (j : C(X₀, X₁)) (V : ModuleCat.{u} ℤ) :
    cokernel (pushforwardChainMap j (constant X₁ V)) ≅
      cokernel (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (TopCat.ofHom j)) :=
  cokernel.mapIso _ _ (constantChainComplexIso (X := X₀) V)
    (constantChainComplexIso (X := X₁) V) (constantChainComplexIso_naturality j V)

/-- The relative coefficient identification preserves the actual quotient map. -/
@[reassoc]
lemma constantChainCokernelIso_quotient (j : C(X₀, X₁)) (V : ModuleCat.{u} ℤ) :
    cokernel.π (pushforwardChainMap j (constant X₁ V)) ≫
        (constantChainCokernelIso j V).hom =
      (constantChainComplexIso (X := X₁) V).hom ≫
        cokernel.π (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map
          (TopCat.ofHom j)) := by
  exact cokernel.π_desc _ _ _

/-- The native singular-chain map between the actual cokernels of a commuting square. -/
def singularChainSquareCokernelMap
    (j : C(X₀, X₁)) (k : C(Y₀, Y₁)) (a : C(X₀, Y₀)) (b : C(X₁, Y₁))
    (w : b.comp j = k.comp a) (V : ModuleCat.{u} ℤ) :
    cokernel (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (TopCat.ofHom j)) ⟶
      cokernel (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (TopCat.ofHom k)) :=
  cokernel.map _ _
    (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (TopCat.ofHom a))
    (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (TopCat.ofHom b)) (by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).congr_map
        (congrArg TopCat.ofHom w))

/-- The native relative map induces the original absolute singular-chain map. -/
@[reassoc]
lemma singularChainSquareCokernelMap_quotient
    (j : C(X₀, X₁)) (k : C(Y₀, Y₁)) (a : C(X₀, Y₀)) (b : C(X₁, Y₁))
    (w : b.comp j = k.comp a) (V : ModuleCat.{u} ℤ) :
    cokernel.π (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (TopCat.ofHom j)) ≫
        singularChainSquareCokernelMap j k a b w V =
      ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (TopCat.ofHom b) ≫
        cokernel.π (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (TopCat.ofHom k)) :=
  cokernel.π_desc _ _ _

/-- Constant-coefficient conversion commutes with the original map of relative pairs. -/
@[reassoc]
lemma constantChainCokernelIso_naturality
    (j : C(X₀, X₁)) (k : C(Y₀, Y₁)) (a : C(X₀, Y₀)) (b : C(X₁, Y₁))
    (w : b.comp j = k.comp a) (V : ModuleCat.{u} ℤ) :
    embeddingSquareCokernelMap j k a b w (constant Y₁ V) ≫
        (constantChainCokernelIso k V).hom =
      (constantChainCokernelIso j V).hom ≫ singularChainSquareCokernelMap j k a b w V := by
  apply (cancel_epi (cokernel.π (pushforwardChainMap j (pullback b (constant Y₁ V))))).mp
  simp only [embeddingSquareCokernelMap_quotient_assoc, constantChainCokernelIso_quotient]
  change _ = cokernel.π (pushforwardChainMap j (constant X₁ V)) ≫
    (constantChainCokernelIso j V).hom ≫ singularChainSquareCokernelMap j k a b w V
  rw [constantChainCokernelIso_quotient_assoc, singularChainSquareCokernelMap_quotient]
  exact constantChainComplexIso_naturality_assoc b V _

/-- A relative quasi-isomorphism of the actual constant local chains is one for
Mathlib's singular chains, along the same square. -/
lemma quasiIso_singularChainSquareCokernelMap
    (j : C(X₀, X₁)) (k : C(Y₀, Y₁)) (a : C(X₀, Y₀)) (b : C(X₁, Y₁))
    (w : b.comp j = k.comp a) (V : ModuleCat.{u} ℤ)
    (h : QuasiIso (embeddingSquareCokernelMap j k a b w (constant Y₁ V))) :
    QuasiIso (singularChainSquareCokernelMap j k a b w V) := by
  have : QuasiIso ((constantChainCokernelIso j V).hom ≫
      singularChainSquareCokernelMap j k a b w V) := by
    rw [← constantChainCokernelIso_naturality]
    infer_instance
  exact quasiIso_of_comp_left (constantChainCokernelIso j V).hom _

/-- The original parameterized cell map satisfies excision in Mathlib's actual
singular-chain model with constant integral-module coefficients. -/
theorem simplexAttachment_singularChainSquareCokernelMap_quasiIso
    (P : TopCat.{u}) (n : ℕ) {B D : TopCat.{u}}
    {f : TopCat.of (P × Convexity.StdSimplex.boundary n) ⟶ B}
    {g : TopCat.of (P × Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : B ⟶ D}
    (sq : IsPushout (TopCat.parameterizedSimplexBoundaryInclusion P n) f g j)
    (V : ModuleCat.{u} ℤ) :
    QuasiIso (singularChainSquareCokernelMap
      (TopCat.parameterizedSimplexBoundaryInclusion P n).hom j.hom f.hom g.hom
      (congrArg TopCat.Hom.hom sq.w) V) :=
  quasiIso_singularChainSquareCokernelMap _ _ _ _ _ V
    (simplexAttachment_embeddingSquareCokernelMap_quasiIso P n sq (constant D V))

end FundamentalGroupoid.LocalCoefficients

namespace SSet

open FundamentalGroupoid.LocalCoefficients

variable {A B C D : SSet.{u}}

private def simplicialChainSquareCokernelMap
    (i : A ⟶ B) (j : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (w : i ≫ b = a ≫ j) (V : ModuleCat.{u} ℤ) :
    cokernel (chainComplexMap i V) ⟶ cokernel (chainComplexMap j V) :=
  cokernel.map _ _ (chainComplexMap a V) (chainComplexMap b V) (by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact ((chainComplexFunctor (ModuleCat.{u} ℤ)).obj V).congr_map w)

@[reassoc]
private lemma simplicialChainSquareCokernelMap_quotient
    (i : A ⟶ B) (j : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (w : i ≫ b = a ≫ j) (V : ModuleCat.{u} ℤ) :
    cokernel.π (chainComplexMap i V) ≫ simplicialChainSquareCokernelMap i j a b w V =
      chainComplexMap b V ≫ cokernel.π (chainComplexMap j V) :=
  cokernel.π_desc _ _ _

private lemma realizedSquare
    (i : A ⟶ B) (j : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (w : i ≫ b = a ≫ j) :
    (SSet.toTop.map b).hom.comp (SSet.toTop.map i).hom =
      (SSet.toTop.map j).hom.comp (SSet.toTop.map a).hom := by
  change (SSet.toTop.map i ≫ SSet.toTop.map b).hom =
    (SSet.toTop.map a ≫ SSet.toTop.map j).hom
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, w]

private def realizationSingularCokernelMap
    (i : A ⟶ B) (j : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (w : i ≫ b = a ≫ j) (V : ModuleCat.{u} ℤ) :=
  singularChainSquareCokernelMap (SSet.toTop.map i).hom (SSet.toTop.map j).hom
    (SSet.toTop.map a).hom (SSet.toTop.map b).hom (realizedSquare i j a b w) V

@[reassoc]
private lemma realizationSingularCokernelMap_quotient
    (i : A ⟶ B) (j : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (w : i ≫ b = a ≫ j) (V : ModuleCat.{u} ℤ) :
    cokernel.π (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (SSet.toTop.map i)) ≫
        realizationSingularCokernelMap i j a b w V =
      ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (SSet.toTop.map b) ≫
        cokernel.π (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map
          (SSet.toTop.map j)) :=
  singularChainSquareCokernelMap_quotient _ _ _ _ _ _

private lemma realizationRelativeChainComparison_square
    (i : A ⟶ B) (j : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (w : i ≫ b = a ≫ j) (V : ModuleCat.{u} ℤ) :
    simplicialChainSquareCokernelMap i j a b w V ≫ realizationRelativeChainComparison j V =
      realizationRelativeChainComparison i V ≫ realizationSingularCokernelMap i j a b w V := by
  apply (cancel_epi (cokernel.π (chainComplexMap i V))).mp
  rw [simplicialChainSquareCokernelMap_quotient_assoc,
    realizationRelativeChainComparison_quotient,
    realizationRelativeChainComparison_quotient_assoc,
    realizationSingularCokernelMap_quotient]
  exact realizationChainComparison_naturality_assoc b V _

/-- The relative unit comparison passes across an actual simplicial pushout when
its corresponding singular relative map satisfies excision. -/
private lemma quasiIso_realizationRelativeChainComparison_of_pushout
    (i : A ⟶ B) (j : C ⟶ D) (a : A ⟶ C) (b : B ⟶ D)
    (sq : IsPushout i a b j) (V : ModuleCat.{u} ℤ)
    (hi : QuasiIso (realizationRelativeChainComparison i V))
    (hs : QuasiIso (realizationSingularCokernelMap i j a b sq.w V)) :
    QuasiIso (realizationRelativeChainComparison j V) := by
  let hC : PreservesColimitsOfShape WalkingSpan
      ((chainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj V) :=
    chainComplexFunctorObj_preservesColimitsOfShape V WalkingSpan
  have : IsIso (simplicialChainSquareCokernelMap i j a b sq.w V) :=
    isIso_cokernel_map_of_isPushout (sq.map ((chainComplexFunctor (ModuleCat.{u} ℤ)).obj V))
  have : QuasiIso (simplicialChainSquareCokernelMap i j a b sq.w V ≫
      realizationRelativeChainComparison j V) := by
    rw [realizationRelativeChainComparison_square]
    infer_instance
  exact quasiIso_of_comp_left (simplicialChainSquareCokernelMap i j a b sq.w V) _

/-- Transport the actual unit comparison along a simplicial isomorphism. -/
lemma quasiIso_realizationChainComparison_of_iso (e : A ≅ B) (V : ModuleCat.{u} ℤ)
    (h : QuasiIso (realizationChainComparison A V)) :
    QuasiIso (realizationChainComparison B V) := by
  have : QuasiIso (chainComplexMap e.hom V ≫ realizationChainComparison B V) := by
    rw [realizationChainComparison_naturality]
    infer_instance
  exact quasiIso_of_comp_left (chainComplexMap e.hom V) _

/-- A dimension bound makes the corresponding simplicial skeleton exhaustive. -/
lemma skeleton_eq_top_of_hasDimensionLT (X : SSet.{u}) (n : ℕ) [X.HasDimensionLT n] :
    X.skeleton n = ⊤ := by
  apply le_antisymm le_top
  rw [Subcomplex.le_iff_contains_nonDegenerate]
  intro d x _
  exact X.mem_skeleton x.val (X.dim_lt_of_nonDegenerate x n)

end SSet

namespace SSet

open FundamentalGroupoid.LocalCoefficients

private lemma quasiIso_realizationSingularCokernelMap_skeletal
    {A X : SSet.{u}} (i : A ⟶ X) (n : ℕ) (V : ModuleCat.{u} ℤ) :
    QuasiIso (realizationSingularCokernelMap
      (relativeCellComplexOfMono.l i n) (relativeCellComplexOfMono.r i n)
      (relativeCellComplexOfMono.t i n) (relativeCellComplexOfMono.b i n)
      (relativeCellComplexOfMono.isPushout i n).flip.w V) := by
  let F := (singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V
  let p := TopCat.parameterizedSimplexBoundaryInclusion (skeletalCellIndex i n) n
  let eA := F.mapIso (realizedSkeletalBoundariesIso i n)
  let eB := F.mapIso (realizedSkeletalCellsIso i n)
  have hw : F.map (SSet.toTop.map (relativeCellComplexOfMono.l i n)) ≫ eB.hom =
      eA.hom ≫ F.map p := by
    change F.map (SSet.toTop.map (relativeCellComplexOfMono.l i n)) ≫
        F.map (realizedSkeletalCellsIso i n).hom =
      F.map (realizedSkeletalBoundariesIso i n).hom ≫ F.map p
    rw [← F.map_comp, ← F.map_comp]
    exact F.congr_map (realizedSkeletalBoundary_square i n)
  let eS := cokernel.mapIso
    (F.map (SSet.toTop.map (relativeCellComplexOfMono.l i n))) (F.map p) eA eB hw
  let sq := realizedSkeletal_isPushout i n
  let φ := singularChainSquareCokernelMap p.hom
    (SSet.toTop.map (relativeCellComplexOfMono.r i n)).hom
    (realizedSkeletalAttaching i n).hom (realizedSkeletalCharacteristic i n).hom
    (congrArg TopCat.Hom.hom sq.w) V
  have : QuasiIso φ :=
    simplexAttachment_singularChainSquareCokernelMap_quasiIso (skeletalCellIndex i n) n sq V
  have hES : cokernel.π (F.map (SSet.toTop.map (relativeCellComplexOfMono.l i n))) ≫
      eS.hom = F.map (realizedSkeletalCellsIso i n).hom ≫ cokernel.π (F.map p) :=
    cokernel.π_desc _ _ _
  have hφ : cokernel.π (F.map p) ≫ φ =
      F.map (realizedSkeletalCharacteristic i n) ≫
        cokernel.π (F.map (SSet.toTop.map (relativeCellComplexOfMono.r i n))) :=
    singularChainSquareCokernelMap_quotient p.hom
      (SSet.toTop.map (relativeCellComplexOfMono.r i n)).hom
      (realizedSkeletalAttaching i n).hom (realizedSkeletalCharacteristic i n).hom
      (congrArg TopCat.Hom.hom sq.w) V
  have hfac : eS.hom ≫ φ = realizationSingularCokernelMap
      (relativeCellComplexOfMono.l i n) (relativeCellComplexOfMono.r i n)
      (relativeCellComplexOfMono.t i n) (relativeCellComplexOfMono.b i n)
      (relativeCellComplexOfMono.isPushout i n).flip.w V := by
    apply (cancel_epi
      (cokernel.π (F.map (SSet.toTop.map (relativeCellComplexOfMono.l i n))))).mp
    rw [reassoc_of% hES, realizationSingularCokernelMap_quotient]
    rw [hφ]
    change F.map (realizedSkeletalCellsIso i n).hom ≫
        F.map (realizedSkeletalCharacteristic i n) ≫ _ = _
    rw [← F.map_comp_assoc]
    simp only [realizedSkeletalCharacteristic, Iso.hom_inv_id_assoc]
    rfl
  rw [← hfac]
  infer_instance

end SSet

namespace SSet

private lemma mono_chainComplexMap_of_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (V : ModuleCat.{u} ℤ) : Mono (chainComplexMap i V) :=
  inferInstanceAs (Mono (chainComplexMap (SSetPair.of i).hom V))

private lemma mono_singularChainMap_realization_of_mono {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (V : ModuleCat.{u} ℤ) :
    Mono (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (SSet.toTop.map i)) := by
  have : Mono (SSet.toTop.map i) :=
    (TopCat.mono_iff_injective _).2 (realization_mono_isClosedEmbedding i).injective
  infer_instance

private lemma quasiIso_realizationChainComparison_bot (X : SSet.{u}) (V : ModuleCat.{u} ℤ) :
    QuasiIso (realizationChainComparison ((⊥ : X.Subcomplex) : SSet.{u}) V) := by
  let B : SSet.{u} := (⊥ : X.Subcomplex)
  have (n : SimplexCategoryᵒᵖ) : IsIso ((sSetTopAdj.unit.app B).app n) := by
    apply (CategoryTheory.isIso_iff_bijective _).2
    constructor
    · intro a
      exact False.elim a.property
    · intro σ
      exact isEmptyElim ((TopCat.toSSetObjEquiv (SSet.toTop.obj B) n σ)
        (Convexity.StdSimplex.single 0))
  have : IsIso (sSetTopAdj.unit.app B) := NatIso.isIso_of_isIso_app _
  change QuasiIso (((chainComplexFunctor (ModuleCat.{u} ℤ)).obj V).map (sSetTopAdj.unit.app B))
  infer_instance

private lemma quasiIso_realizationChainComparison_skeleton_succ
    (X : SSet.{u}) (n : ℕ) (V : ModuleCat.{u} ℤ)
    (hprev : QuasiIso (realizationChainComparison (X.skeleton n : SSet.{u}) V))
    (hboundary : QuasiIso (realizationChainComparison (∂Δ[n] : SSet.{u}) V)) :
    QuasiIso (realizationChainComparison (X.skeleton (n + 1) : SSet.{u}) V) := by
  let i := (⊥ : X.Subcomplex).ι
  let T := relativeCellComplexOfMono.Cell i n
  let hC : PreservesColimitsOfShape (Discrete T)
      ((chainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj V) :=
    chainComplexFunctorObj_preservesColimitsOfShape V (Discrete T)
  have hb : QuasiIso (realizationChainComparison (relativeCellComplexOfMono.sigmaBoundary i n) V) :=
    quasiIso_realizationChainComparison_of_coproduct V
      (Discrete.functor (fun _ : T ↦ (∂Δ[n] : SSet.{u})))
      (colimit.cocone _) (colimit.isColimit _) (fun _ ↦ hboundary)
  have hc : QuasiIso (realizationChainComparison
      (relativeCellComplexOfMono.sigmaStdSimplex i n) V) :=
    quasiIso_realizationChainComparison_of_coproduct V
      (Discrete.functor (fun _ : T ↦ (Δ[n] : SSet.{u})))
      (colimit.cocone _) (colimit.isColimit _)
      (fun _ ↦ quasiIso_realizationChainComparison_stdSimplex n V)
  have : Mono (relativeCellComplexOfMono.l i n) :=
    (relativeCellComplexOfMono.isPullback i n).mono_snd_of_mono
  have := mono_chainComplexMap_of_mono (relativeCellComplexOfMono.l i n) V
  have := mono_singularChainMap_realization_of_mono (relativeCellComplexOfMono.l i n) V
  have hrel := quasiIso_realizationRelativeChainComparison (relativeCellComplexOfMono.l i n) V hb hc
  have hr := quasiIso_realizationRelativeChainComparison_of_pushout
    (relativeCellComplexOfMono.l i n) (relativeCellComplexOfMono.r i n)
    (relativeCellComplexOfMono.t i n) (relativeCellComplexOfMono.b i n)
    (relativeCellComplexOfMono.isPushout i n).flip V hrel
    (quasiIso_realizationSingularCokernelMap_skeletal i n V)
  have := mono_chainComplexMap_of_mono (relativeCellComplexOfMono.r i n) V
  have := mono_singularChainMap_realization_of_mono (relativeCellComplexOfMono.r i n) V
  have hp : QuasiIso (realizationChainComparison (skeletonOfMono i n : SSet.{u}) V) := by
    exact quasiIso_realizationChainComparison_of_iso
      (Subcomplex.eqToIso (skeletonOfMono_bot X n)).symm V hprev
  have h := quasiIso_realizationChainComparison_of_relative
    (relativeCellComplexOfMono.r i n) V hp hr
  exact quasiIso_realizationChainComparison_of_iso
    (Subcomplex.eqToIso (skeletonOfMono_bot X (n + 1))) V h

/-- The actual unit comparison is a quasi-isomorphism on every finite skeletal stage. -/
theorem quasiIso_realizationChainComparison_skeleton (n : ℕ) (X : SSet.{u})
    (V : ModuleCat.{u} ℤ) :
    QuasiIso (realizationChainComparison (X.skeleton n : SSet.{u}) V) := by
  induction n generalizing X with
  | zero =>
      exact quasiIso_realizationChainComparison_of_iso (Subcomplex.eqToIso X.skeleton_zero).symm V
        (quasiIso_realizationChainComparison_bot X V)
  | succ n ih =>
      apply quasiIso_realizationChainComparison_skeleton_succ X n V (ih X)
      let e : ((∂Δ[n] : SSet.{u}).skeleton n : SSet.{u}) ≅ (∂Δ[n] : SSet.{u}) :=
        Subcomplex.eqToIso (skeleton_eq_top_of_hasDimensionLT _ n) ≪≫ Subcomplex.topIso _
      exact quasiIso_realizationChainComparison_of_iso e V (ih (∂Δ[n] : SSet.{u}))

/-- The actual simplicial-to-singular unit comparison is a quasi-isomorphism
for arbitrary simplicial sets and constant integral-module coefficients. -/
theorem quasiIso_realizationChainComparison (X : SSet.{u}) (V : ModuleCat.{u} ℤ) :
    QuasiIso (realizationChainComparison X V) := by
  let R := relativeCellComplex X
  let c : Cocone R.F := { pt := X, ι := R.incl }
  let hC : PreservesColimitsOfShape ℕ
      ((chainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj V) :=
    @chainComplexFunctorObj_preservesColimitsOfShape (ModuleCat.{u} ℤ) _ _ _ V ℕ _
      (inferInstance : HasColimitsOfShape ℕ (Type u))
  apply quasiIso_realizationChainComparison_of_filteredColimit V R.F c R.isColimit
  intro n
  change QuasiIso (realizationChainComparison
    (skeletonOfMono (⊥ : X.Subcomplex).ι n : SSet.{u}) V)
  exact quasiIso_realizationChainComparison_of_iso
    (Subcomplex.eqToIso (skeletonOfMono_bot X n)).symm V
    (quasiIso_realizationChainComparison_skeleton n X V)

attribute [colib_tag "COL-1013"] quasiIso_realizationChainComparison
attribute [colib_ref "May1967SimplicialObjects" "Section 16, Proposition 16.2(i), p. 63"
  "background" "The integral instance of the original realization-unit comparison"]
  quasiIso_realizationChainComparison

end SSet
