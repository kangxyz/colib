/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.AffineWeilDescent
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.FiniteScalarAffineWitness
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.OriginalOpenRefinement
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange.FiniteScalarOpenFactor

/-!
# Descent of two scalar boundary corrections

Restrict the two scalar affine corrections over one actual open of the
original base. The affine Weil refinement and the coprime extension
degrees give a witness in the original boundary image sieve.

Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/FinitePolynomialImage.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `ce22a1b5db4fcfe761f9e3150b18cc475d20f1bc`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k]

/-- The scalar correction over an open containing the whole marked scalar fiber. -/
structure ProducedScalarCorrection
    (P : PresheafWithTransfers.{u + 1} k) (L : Type u) [Field L] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    {V Y D A : SmoothSite (Spec (.of k))} (w : V.left)
    (q₀ : Y ⟶ SmoothSite.Contraction.affineLineCylinder.obj V) (z₀ : V ⟶ Y)
    (δ : D ⟶ A) (e₀ : Y ⟶ A) (s : sections P (Cor.mk D)) where
  /-- The open scalar neighborhood containing the entire fiber over `w`. -/
  B : SmoothSite (Spec (.of L))
  /-- The inclusion of `B` into the scalar extension of `V`. -/
  i : B ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj V
  open_i : IsOpenImmersion i.left
  fiber : (SmoothSite.finiteScalarProjection (E := L) V).left ⁻¹' {w} ⊆ Set.range i.left
  /-- The affine étale neighborhood over the scalar extension of the original chart `Y`. -/
  E : SmoothSite (Spec (.of L))
  affine_E : IsAffine E.left
  /-- The étale map from `E` to the scalar extension of `Y`. -/
  η : E ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj Y
  etale_η : Etale η.left
  /-- The affine-line parameter map over `B`, compatible with the original map `q₀`. -/
  q : E ⟶ SmoothSite.Contraction.affineLineCylinder.obj B
  base_eq : η ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map q₀ ≫
    (SmoothSite.fieldBaseChangeA1Iso (L := L) V).hom = q ≫
      SmoothSite.Contraction.affineLineCylinder.map i
  /-- The lift of the scalar extension of the marked map `z₀` restricted to `B`. -/
  ζ : B ⟶ E
  mark_eq : ζ ≫ η = i ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map z₀
  /-- The overlap obtained by pulling back the torus cylinder along `q`. -/
  O : SmoothSite (Spec (.of L))
  /-- The projection from the overlap to the affine correction neighborhood. -/
  α : O ⟶ E
  /-- The projection from the overlap to the torus cylinder over `B`. -/
  β : O ⟶ SmoothSite.Contraction.torusCylinder.obj B
  square : IsPullback β.left α.left (SmoothSite.Contraction.openInclusion.app B).left q.left
  /-- The map from the overlap to the scalar extension of `D` used to restrict `s`. -/
  φ : O ⟶ (SmoothSite.fieldBaseChange (algebraMap k L)).obj D
  ambient_eq : φ ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map δ =
    α ≫ η ≫ (SmoothSite.fieldBaseChange (algebraMap k L)).map e₀
  /-- The Laurent section on the torus cylinder over `B` in the scalar extension of `P`. -/
  a : sections (finiteSeparableExtension L P) (Cor.mk (SmoothSite.Contraction.torusCylinder.obj B))
  /-- The section on `E` in the scalar extension of `P`, subtracted after restriction to `O`. -/
  c : sections (finiteSeparableExtension L P) (Cor.mk E)
  relation : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map β) a -
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map α) c =
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map φ)
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L) D)) s)

/-- Two actual corrections over coprime finite separable extensions give an
image witness after restricting to a common original affine neighborhood. -/
theorem exists_boundary_image_neighborhood_of_scalar_corrections
    (X : SmoothSite (Spec (.of k))) (P : PresheafWithTransfers.{u + 1} k)
    (W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
    (R : Type u) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (w : Spec (.of R))
    {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (q₀ : Y ⟶ SmoothSite.Contraction.affineLineCylinder.obj (SmoothSite.affineSite k R))
    [Etale q₀.left]
    (z₀ : SmoothSite.affineSite k R ⟶ Y)
    (hz₀ : z₀ ≫ q₀ = SmoothSite.Contraction.nativeAffineSection (.of k)
      (SmoothSite.affineSite k R) 0)
    (v₀ : SmoothSite.affineSite k R ⟶
      (toSmoothSite X).obj ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
        0).left).obj W))
    [IsOpenImmersion v₀.left]
    (e₀ : Y ⟶ (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj W)
    (hp : q₀ ≫
      SmoothSite.Contraction.affineLineCylinder.map
        (v₀ ≫ toBase X ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
          0).left).obj W)) =
      e₀ ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W)
    (hmark : z₀.left ≫ e₀.left = v₀.left ≫
      pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left)
    (d : ((PresheafWithTransfers.toPresheaf k).obj P).obj (op
      ((toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).obj
        ((baseChange (SmoothSite.Contraction.openInclusion.app X).left).obj W))))
    {L₁ L₂ : Type u} [Field L₁] [Field L₂] [Algebra k L₁] [Algebra k L₂]
    [Module.Finite k L₁] [Module.Finite k L₂]
    [Algebra.IsSeparable k L₁] [Algebra.IsSeparable k L₂]
    (c₁ : ProducedScalarCorrection P L₁ w q₀ z₀
      ((restrictionProjection (SmoothSite.Contraction.openInclusion.app X)).app W) e₀ d)
    (c₂ : ProducedScalarCorrection P L₂ w q₀ z₀
      ((restrictionProjection (SmoothSite.Contraction.openInclusion.app X)).app W) e₀ d)
    (hdegrees : (Module.finrank k L₁).Coprime (Module.finrank k L₂)) :
    ∃ (V : EtaleSeparatedFiniteType X.left)
      (v : V ⟶ (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W),
      IsOpenImmersion v.left ∧ v₀.left w ∈ Set.range v.left ∧
      Presheaf.imageSieve (contractionToBoundary X P).hom
        ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
          (SmoothSite.Contraction.openInclusion.app X)
          (SmoothSite.Contraction.nativeAffineSection (.of k) X 0)).app (op W) d) v := by
  let V₀ := SmoothSite.affineSite k R
  let δ := (restrictionProjection (SmoothSite.Contraction.openInclusion.app X)).app W
  let := c₁.open_i
  let := c₂.open_i
  obtain ⟨U₀, hU₀, hwU, b₁, b₂, hb₁, hb₂⟩ :=
    SmoothSite.exists_common_affine_scalar_open_factor V₀ w c₁.i c₂.i c₁.fiber c₂.fiber
  let : IsAffine U₀.toScheme := hU₀
  let U₁ := SmoothSite.mk (U₀.ι ≫ V₀.hom)
  let j : U₁ ⟶ V₀ := SmoothSite.homMk U₀.ι rfl
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U₀.ι)
  let V := originalOpenBase X W v₀ j
  let eU := originalOpenBaseIso X W v₀ j
  let U := (toSmoothSite X).obj V
  let : IsAffine U.left := hU₀
  let j' : U ⟶ V₀ := eU.inv ≫ j
  let v := originalOpenBaseToZero X W v₀ j
  have hbase : j' ≫ v₀ ≫ toBase X
      ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W) =
        toBase X V := by
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 _ ≫ U₀.ι) ≫ v₀.left ≫ _ = _
    simp only [Category.id_comp]
    rfl
  let YU := SmoothSite.originalOpenRefinement q₀ j'
  let : IsAffine V₀.left := inferInstanceAs (IsAffine (Spec (.of R)))
  let : IsAffine YU.left := SmoothSite.originalOpenRefinement_affine q₀ j'
  let qU := SmoothSite.originalOpenRefinementCylinder q₀ j'
  let : Etale qU.left := SmoothSite.originalOpenRefinementCylinder_etale q₀ j'
  let r := SmoothSite.originalOpenRefinementAmbient q₀ j'
  let zU := SmoothSite.originalOpenRefinementZero q₀ j' z₀ hz₀
  let φU := originalOpenRefinementToPunctured X W v₀ j' q₀ e₀ hp
  have hφU : φU ≫ δ = SmoothSite.etalePullbackFst qU
      (SmoothSite.Contraction.openInclusion.app U) ≫ r ≫ e₀ := by
    apply MorphismProperty.Over.Hom.ext
    exact originalOpenRefinementToPunctured_fst X W v₀ j' q₀ e₀ hp
  have restrict (L : Type u) [Field L] [Algebra k L] [Module.Finite k L]
      [Algebra.IsSeparable k L]
      (c : ProducedScalarCorrection P L w q₀ z₀ δ e₀ d)
      (b : (SmoothSite.fieldBaseChange (algebraMap k L)).obj U₁ ⟶ c.B)
      (hb : b ≫ c.i = (SmoothSite.fieldBaseChange (algebraMap k L)).map j) :
      Nonempty (ScalarAffineWitness P L qU zU φU d) := by
    let F := SmoothSite.fieldBaseChange (algebraMap k L)
    let := c.affine_E
    let := c.etale_η
    let := c.open_i
    let : IsOpenImmersion (SmoothSite.Contraction.affineLineCylinder.map c.i).left := by
      exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) c.open_i
        (inferInstanceAs (IsOpenImmersion (𝟙 (SmoothSite.additiveGroupObject (Spec (.of L))).left)))
        (MorphismProperty.Over.w c.i).symm (Category.id_comp _).symm
    let : Mono (SmoothSite.Contraction.affineLineCylinder.map c.i) :=
      (SmoothSite.forgetScheme _).mono_of_mono_map
        (inferInstanceAs (Mono (SmoothSite.Contraction.affineLineCylinder.map c.i).left))
    let : IsOpenImmersion δ.left := inferInstanceAs
      (IsOpenImmersion (pullback.fst W.hom (SmoothSite.Contraction.openInclusion.app X).left))
    let : IsOpenImmersion (F.map δ).left := by
      let f := Spec.map (CommRingCat.ofHom (algebraMap k L))
      have heq : (F.map δ).left = pullback.map _ f _ f δ.left (𝟙 _) (𝟙 _)
          (by simp only [Category.comp_id, MorphismProperty.Over.w])
          (by simp only [Category.comp_id, Category.id_comp]) := by
        apply pullback.hom_ext <;> simp [F, SmoothSite.fieldBaseChange,
          SmoothSite.baseChange_map_fst, SmoothSite.baseChange_map_snd,
          pullback.map, f]
      rw [heq]
      infer_instance
    let : Mono (F.map δ) := (SmoothSite.forgetScheme _).mono_of_mono_map
      (inferInstanceAs (Mono (F.map δ).left))
    have hb' : (F.map eU.inv ≫ b) ≫ c.i = F.map j' := by
      rw [Category.assoc, hb, ← Functor.map_comp]
    exact restrictScalarAffineWitness P j' q₀ qU r
      (SmoothSite.originalOpenRefinement_condition q₀ j') z₀ zU
      (SmoothSite.originalOpenRefinementZero_ambient q₀ j' z₀ hz₀) e₀ δ φU hφU
      c.i (F.map eU.inv ≫ b) hb' c.η c.q c.base_eq c.ζ c.mark_eq
      c.α c.β c.square c.φ c.ambient_eq d c.a c.c c.relation
  obtain ⟨a₁⟩ := restrict L₁ c₁ b₁ hb₁
  obtain ⟨a₂⟩ := restrict L₂ c₂ b₂ hb₂
  let := a₁.affine
  let := a₂.affine
  let := a₁.etale
  let := a₂.etale
  let : Algebra k Γ(YU.left, ⊤) := sectionsAlgebra YU
  let : Algebra Γ(YU.left, ⊤) Γ(U.left, ⊤) := zU.left.appTop.hom.toAlgebra
  have he : YU.left.isoSpec.inv ≫ YU.hom = Spec.algebraMap k Γ(YU.left, ⊤) :=
    isoSpec_inv_base YU
  have hchart : U.left.isoSpec.inv ≫ zU.left =
      Spec.algebraMap Γ(YU.left, ⊤) Γ(U.left, ⊤) ≫ YU.left.isoSpec.inv :=
    (Scheme.isoSpec_inv_naturality zU.left).symm
  have hambient : (r ≫ e₀).left ≫ W.hom =
      qU.left ≫ ((cylinderNeighborhood X).obj V).hom := by
    have h := originalOpenRefinement_ambient X W v₀ j' q₀ e₀ hp
    rw [hbase] at h
    exact congrArg (fun f => f.left) h
  have hmarkU : zU.left ≫ (r ≫ e₀).left =
      v.left ≫ pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left
        := by
    have h := congrArg (fun f => f.left)
      (SmoothSite.originalOpenRefinementZero_ambient q₀ j' z₀ hz₀)
    change zU.left ≫ r.left = j'.left ≫ z₀.left at h
    change zU.left ≫ (r.left ≫ e₀.left) = (U₀.ι ≫ v₀.left) ≫ _
    rw [← Category.assoc, h, Category.assoc, hmark]
    change (𝟙 _ ≫ U₀.ι) ≫ v₀.left ≫ _ = _
    simp only [Category.id_comp, Category.assoc]
  have hφ₂ : φU.left ≫ pullback.snd W.hom
      (SmoothSite.Contraction.openInclusion.app X).left =
      (SmoothSite.etalePullbackSnd qU (SmoothSite.Contraction.openInclusion.app U)).left ≫
        (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of
          k))))).left := by
    have h := originalOpenRefinementToPunctured_snd X W v₀ j' q₀ e₀ hp
    rw [hbase] at h
    exact h
  refine ⟨V, v, inferInstance, originalOpenBaseToZero_retains X W v₀ j w
    ⟨⟨w, hwU⟩, rfl⟩, ?_⟩
  exact imageSieve_of_affine_weil_corrections
    (A := Γ(YU.left, ⊤)) (T := Γ(U.left, ⊤)) X P V YU qU zU
    (SmoothSite.originalOpenRefinementZero_cylinder q₀ j' z₀ hz₀)
    (r ≫ e₀) hambient v hmarkU YU.left.isoSpec.symm he U.left.isoSpec.symm hchart
    φU (originalOpenRefinementToPunctured_fst X W v₀ j' q₀ e₀ hp) hφ₂ d
    a₁.f a₁.mark a₁.mark_eq a₁.laurentSection a₁.ambientSection a₁.relation
    a₂.f a₂.mark a₂.mark_eq a₂.laurentSection a₂.ambientSection a₂.relation
    hdegrees

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
