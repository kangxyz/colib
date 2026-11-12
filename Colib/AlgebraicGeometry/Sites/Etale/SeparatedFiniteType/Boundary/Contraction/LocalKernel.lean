/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.MarkedExtension
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.LocalCylinderExtension

/-! # Zero canonical boundary gives residue-splitting local contraction relations -/

/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Contraction/LocalKernel.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `80ad387804a70b876947bc0b61f03a298ca65af9`. The actual native cylinder, Laurent open,
whole closed fiber and original residue marking are retained.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)

/-- A zero Laurent boundary produces a genuine cylinder extension on a base
neighborhood retaining the original residue-field marking. -/
theorem exists_marked_cylinder_extension_of_boundary_zero
    (V : EtaleSeparatedFiniteType X.left) (v : V.left)
    (s : (((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.torusSections F.obj)).obj (op V)))
    (hs : (ambientCokernelToBoundary X F).app (op V)
      ((laurentToAmbientCokernel X F).app (op V) s) = 0) :
    ∃ (W : EtaleSeparatedFiniteType V.left)
      (c : Spec (V.left.residueField v) ⟶ W.left),
      c ≫ W.hom = V.left.fromSpecResidueField v ∧
      ∃ t : ((SheafWithTransfers.toSheaf k).obj F).obj.obj
          (op (SmoothSite.Contraction.affineLineCylinder.obj
            ((toSmoothSite ((toSmoothSite X).obj V)).obj W))),
        ((SheafWithTransfers.toSheaf k).obj F).obj.map
            (SmoothSite.Contraction.openInclusion.app
              ((toSmoothSite ((toSmoothSite X).obj V)).obj W)).op t =
          ((SheafWithTransfers.toSheaf k).obj F).obj.map
            (SmoothSite.productMap (toBase ((toSmoothSite X).obj V) W)
              (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k))))).op s := by
  let G := (SheafWithTransfers.toSheaf k).obj F
  let Y := (toSmoothSite X).obj V
  let jX := SmoothSite.Contraction.openInclusion.app X
  let jY := SmoothSite.Contraction.openInclusion.app Y
  obtain ⟨E, f, e, t, he, ht⟩ :=
    exists_pointed_extension_of_laurent_boundary_zero X F V v s hs
  obtain ⟨c, hc⟩ := exists_residue_lift_of_marked_zero_fiber X V v E f e he
  let M := (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj E
  let p : M ⟶ SmoothSite.Contraction.affineLineCylinder.obj Y :=
    (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).map f ≫
      (parameterProductUnderlyingIso X (SmoothSite.additiveGroupObject (Spec (.of k)))).hom.app V
  have : Etale f.left := by
    have : Etale (f.left ≫ ((cylinderNeighborhood X).obj V).hom) := by
      rw [MorphismProperty.Over.w]
      infer_instance
    exact Etale.of_comp f.left ((cylinderNeighborhood X).obj V).hom
  have : Etale p.left := by
    change Etale (f.left ≫ 𝟙 _)
    rw [Category.comp_id]
    infer_instance
  have hcp : c ≫ p.left =
      Y.left.fromSpecResidueField v ≫
        (SmoothSite.Contraction.nativeAffineSection (.of k) Y 0).left := by
    change c ≫ (f.left ≫ 𝟙 _) = _
    rw [Category.comp_id]
    exact hc
  let a₀ := (restrictionProjection jX).app E
  let b₀ := (toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).map
      ((baseChange jX.left).map f) ≫ puncturedProjection X V
  have h₀ : b₀ ≫ jY = a₀ ≫ p := by
    dsimp only [b₀, p]
    rw [Category.assoc, puncturedProjection_open, ← Category.assoc]
    exact (congrArg (fun g => g ≫
      (parameterProductUnderlyingIso X (SmoothSite.additiveGroupObject (Spec (.of k)))).hom.app V)
        ((restrictionProjection jX).naturality f)).trans (Category.assoc _ _ _)
  have ht' : G.obj.map a₀.op t = G.obj.map b₀.op s := by
    change G.obj.map a₀.op t = G.obj.map
      ((toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).map
        ((baseChange jX.left).map f)).op (G.obj.map (puncturedProjection X V).op s) at ht
    have hm : G.obj.map b₀.op = G.obj.map (puncturedProjection X V).op ≫
        G.obj.map ((toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).map
          ((baseChange jX.left).map f)).op := G.obj.map_comp _ _
    exact ht.trans (ConcreteCategory.congr_hom hm s).symm
  let b := toBase X V
  let p₀ := toBase (SmoothSite.Contraction.affineLineCylinder.obj X) E
  have hp : p ≫ SmoothSite.Contraction.affineLineCylinder.map b = p₀ := by
    apply MorphismProperty.Over.Hom.ext
    change (f.left ≫ 𝟙 _) ≫ ((cylinderNeighborhood X).obj V).hom = E.hom
    rw [Category.comp_id, MorphismProperty.Over.w]
  let O := SmoothSite.etalePullback p jY
  let α : O ⟶ M := SmoothSite.etalePullbackFst p jY
  let β : O ⟶ SmoothSite.Contraction.torusCylinder.obj Y := SmoothSite.etalePullbackSnd p jY
  have H : IsPullback α β p jY :=
    IsPullback.of_isLimit (SmoothSite.etalePullbackConeIsLimit p jY)
  have hnat : jY ≫ SmoothSite.Contraction.affineLineCylinder.map b =
      SmoothSite.productMap b (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k)))) ≫ jX := by
    simp only [jX, jY, SmoothSite.Contraction.openInclusion, SmoothSite.Contraction.parameterMap,
      SmoothSite.Contraction.parameterProduct,
      ← SmoothSite.productMap_comp, Category.comp_id, Category.id_comp]
  have hr : α ≫ p₀ =
      (β ≫ SmoothSite.productMap b (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k))))) ≫
        jX := by
    rw [← hp, ← Category.assoc, H.w, Category.assoc, hnat, ← Category.assoc]
  have : Etale p₀.left := inferInstanceAs (Etale E.hom)
  let H₀ := IsPullback.of_isLimit (SmoothSite.etalePullbackConeIsLimit p₀ jX)
  let r := H₀.lift α
    (β ≫ SmoothSite.productMap b (𝟙 (SmoothSite.multiplicativeGroupObject (Spec (.of k))))) hr
  have hra : r ≫ a₀ = α := H₀.lift_fst _ _ _
  have hrb : r ≫ b₀ = β := by
    apply (cancel_mono jY).mp
    rw [Category.assoc, h₀, ← Category.assoc, hra, H.w]
  have ht'' : G.obj.map α.op t = G.obj.map β.op s := by
    have hm₁ : G.obj.map a₀.op ≫ G.obj.map r.op = G.obj.map α.op := by
      rw [← G.obj.map_comp, ← op_comp, hra]
    have hm₂ : G.obj.map b₀.op ≫ G.obj.map r.op = G.obj.map β.op := by
      rw [← G.obj.map_comp, ← op_comp, hrb]
    exact (ConcreteCategory.congr_hom hm₁ t).symm.trans
      ((congrArg (G.obj.map r.op) ht').trans (ConcreteCategory.congr_hom hm₂ s))
  exact SmoothSite.exists_local_cylinder_extension_of_pointed_extension
    G Y M p v c hcp s t ht''

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
