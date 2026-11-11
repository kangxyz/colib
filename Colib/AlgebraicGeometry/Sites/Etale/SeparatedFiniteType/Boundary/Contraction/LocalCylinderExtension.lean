/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.WholeZeroRefinement
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.SheafKernel
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComplement

/-! # Pointed ambient extensions give genuine local cylinder extensions -/

/-!
Adapted from `Motivic/Cohomology/A1/Contraction/LocalCylinderExtension.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `e563edc589ba7718cb28e284e257381b6ca127ff`. The actual native cylinder, Laurent open,
whole closed fiber and original residue marking are retained.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k]

/-- An extension on an actual étale ambient neighborhood, marked over the original
residue field, extends over the entire cylinder after a residue-splitting base
neighborhood. The proof uses whole-zero refinement and ordinary Nisnevich gluing. -/
theorem exists_local_cylinder_extension_of_pointed_extension
    (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (X E : SmoothSite (Spec (.of k))) (f : E ⟶ Contraction.affineLineCylinder.obj X)
    [Etale f.left] (x : X.left)
    (c : Spec (X.left.residueField x) ⟶ E.left)
    (hc : c ≫ f.left = X.left.fromSpecResidueField x ≫ (Contraction.nativeAffineSection (.of k) X 0).left)
    (s : F.obj.obj (op (Contraction.torusCylinder.obj X))) (t : F.obj.obj (op E))
    (h : F.obj.map (etalePullbackFst f (Contraction.openInclusion.app X)).op t =
      F.obj.map (etalePullbackSnd f (Contraction.openInclusion.app X)).op s) :
    ∃ (V : EtaleSeparatedFiniteType X.left)
      (cV : Spec (X.left.residueField x) ⟶ V.left),
      cV ≫ V.hom = X.left.fromSpecResidueField x ∧
      ∃ a : F.obj.obj (op (Contraction.affineLineCylinder.obj ((EtaleSeparatedFiniteType.toSmoothSite X).obj V))),
        F.obj.map (Contraction.openInclusion.app ((EtaleSeparatedFiniteType.toSmoothSite X).obj V)).op a =
          F.obj.map (productMap (EtaleSeparatedFiniteType.toBase X V) (𝟙 (multiplicativeGroupObject (Spec (.of k))))).op s :=
              by
  let W : EtaleSeparatedFiniteType (Contraction.affineLineCylinder.obj X).left :=
    MorphismProperty.Over.mk ⊤ f.left ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let z := (Contraction.nativeAffineSection (.of k) X 0).left
  let c₀ : Spec (X.left.residueField x) ⟶
      ((EtaleSeparatedFiniteType.baseChange z).obj W).left :=
    pullback.lift c (X.left.fromSpecResidueField x) hc
  let ξ := IsLocalRing.closedPoint (X.left.residueField x)
  obtain ⟨V, v, hV, hv, hw, N, e, q, a, zV, hN, hq, hqc, hqs, H, haz, hzq, hze⟩ :=
    _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.exists_whole_zero_neighborhood_refinement X W (c₀ ξ)
  let : IsOpenImmersion v.left := hv
  have hretain : Set.range c₀ ⊆ Set.range v.left := by
    rintro _ ⟨η, rfl⟩
    simpa only [Subsingleton.elim η ξ] using hw
  let cV := IsOpenImmersion.lift v.left c₀ hretain
  have hcV : cV ≫ V.hom = X.left.fromSpecResidueField x := by
    rw [← MorphismProperty.Over.w v, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact pullback.lift_snd _ _ _
  let Y := (EtaleSeparatedFiniteType.toSmoothSite X).obj V
  let M := (EtaleSeparatedFiniteType.toSmoothSite (Contraction.affineLineCylinder.obj X)).obj N
  let p : M ⟶ Contraction.affineLineCylinder.obj Y :=
    (EtaleSeparatedFiniteType.toSmoothSite (Contraction.affineLineCylinder.obj X)).map q ≫
      (EtaleSeparatedFiniteType.parameterProductUnderlyingIso X (additiveGroupObject (Spec (.of k)))).hom.app V
  let e' : M ⟶ E := homMk e.left (by
    have he : e.left ≫ f.left = N.hom := MorphismProperty.Over.w e
    change e.left ≫ E.hom = N.hom ≫ (Contraction.affineLineCylinder.obj X).hom
    rw [← MorphismProperty.Over.w f, ← Category.assoc]
    exact congrArg (fun g => g ≫ (Contraction.affineLineCylinder.obj X).hom) he)
  let b : Y ⟶ X := EtaleSeparatedFiniteType.toBase X V
  have hp : p ≫ Contraction.affineLineCylinder.map b = e' ≫ f := by
    apply MorphismProperty.Over.Hom.ext
    change (q.left ≫ 𝟙 _) ≫ _ = e.left ≫ f.left
    rw [Category.comp_id]
    exact (MorphismProperty.Over.w q).trans (MorphismProperty.Over.w e).symm
  have : Etale p.left := by
    change Etale (q.left ≫ 𝟙 _)
    rw [Category.comp_id]
    exact hq
  have hpb : IsPullback a (𝟙 V.left) p.left (Contraction.nativeAffineSection (.of k) Y 0).left := by
    change IsPullback a (𝟙 V.left) (q.left ≫ 𝟙 _) _
    simpa only [Category.comp_id] using H
  have : IsIso (pullback.snd p.left (Contraction.nativeAffineSection (.of k) Y 0).left) := by
    have hi : IsIso (hpb.isoPullback.hom ≫
        pullback.snd p.left (Contraction.nativeAffineSection (.of k) Y 0).left) := by
      rw [hpb.isoPullback_hom_snd]
      infer_instance
    exact IsIso.of_isIso_comp_left hpb.isoPullback.hom _
  let j := Contraction.openInclusion.app Y
  let O := etalePullback j p
  let α : O ⟶ Contraction.torusCylinder.obj Y := etalePullbackFst j p
  let β : O ⟶ M := etalePullbackSnd j p
  have hO : IsPullback α β j p := IsPullback.of_isLimit (etalePullbackConeIsLimit j p)
  have hnat : j ≫ Contraction.affineLineCylinder.map b =
      productMap b (𝟙 (multiplicativeGroupObject (Spec (.of k)))) ≫ Contraction.openInclusion.app X := by
    simp only [j, Contraction.openInclusion, Contraction.parameterMap, Contraction.affineLineCylinder, Contraction.parameterProduct, ← productMap_comp,
      Category.comp_id, Category.id_comp]
  have hr : (β ≫ e') ≫ f =
      (α ≫ productMap b (𝟙 (multiplicativeGroupObject (Spec (.of k))))) ≫ Contraction.openInclusion.app X := by
    rw [Category.assoc, ← hp, ← Category.assoc β, ← hO.w,
      Category.assoc, hnat, ← Category.assoc]
  let H₀ := IsPullback.of_isLimit (etalePullbackConeIsLimit f (Contraction.openInclusion.app X))
  let r := H₀.lift (β ≫ e') (α ≫ productMap b (𝟙 (multiplicativeGroupObject (Spec (.of k))))) hr
  have heq : F.obj.map α.op
        (F.obj.map (productMap b (𝟙 (multiplicativeGroupObject (Spec (.of k))))).op s) =
      F.obj.map β.op (F.obj.map e'.op t) := by
    have hr₁ : r ≫ etalePullbackFst f (Contraction.openInclusion.app X) = β ≫ e' :=
      H₀.lift_fst _ _ _
    have hr₂ : r ≫ etalePullbackSnd f (Contraction.openInclusion.app X) =
        α ≫ productMap b (𝟙 (multiplicativeGroupObject (Spec (.of k)))) := H₀.lift_snd _ _ _
    have hm₁ : F.obj.map (etalePullbackFst f (Contraction.openInclusion.app X)).op ≫
        F.obj.map r.op = F.obj.map e'.op ≫ F.obj.map β.op := by
      rw [← F.obj.map_comp, ← op_comp, hr₁, op_comp, F.obj.map_comp]
    have hm₂ : F.obj.map (etalePullbackSnd f (Contraction.openInclusion.app X)).op ≫
        F.obj.map r.op = F.obj.map (productMap b (𝟙 (multiplicativeGroupObject (Spec (.of k))))).op ≫
          F.obj.map α.op := by
      rw [← F.obj.map_comp, ← op_comp, hr₂, op_comp, F.obj.map_comp]
    change (F.obj.map (productMap b (𝟙 (multiplicativeGroupObject (Spec (.of k))))).op ≫ F.obj.map α.op) s =
      (F.obj.map e'.op ≫ F.obj.map β.op) t
    rw [← hm₁, ← hm₂]
    exact (congrArg (F.obj.map r.op) h).symm
  let sq : Square (SmoothSite (Spec (.of k))) := ⟨α, β, j, p, hO.w⟩
  obtain ⟨a', ha', _⟩ := exists_extension_of_iso_complement_neighborhood F sq hO
    (Contraction.nativeAffineSection (.of k) Y 0).left (Contraction.range_nativeAffineSection_zero (.of k) Y)
    (F.obj.map (productMap b (𝟙 (multiplicativeGroupObject (Spec (.of k))))).op s) (F.obj.map e'.op t) heq
  exact ⟨V, cV, hcV, a', ha'⟩

end AlgebraicGeometry.Scheme.SmoothSite

