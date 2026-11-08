/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.GroupMultiplication
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrack
public import Colib.Util.References

/-! # Original coproducts on compact families of based cubes

The actual product-realization comparison admits unique lifts of compact sources. Apply it
on the complete parameter and spatial cube before composing the canonically rebased coproduct.
Injectivity retains every supplied face and the whole chosen-zero boundary. No global inverse
to product realization or continuous multiplication on the raw delooping is asserted.
-/
/-! Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductCube.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original universes, canonical maps,
coordinates and boundaries are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology SSet
open CategoryTheory.Waldhausen.Product
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] (W : Structure C) (n : ℕ)

/-- Lift the entire original pair of finite cubes through the actual product comparison. -/
def productCubeLift
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    GenLoop (Fin (n + 1)) (productStructure W W).Delooping
      (productStructure W W).kBasepoint := by
  let f := p.val.prodMk q.val
  let g := Classical.choose (Product.deloopingComparison_compact_lifts W W _ f)
  have hg := Classical.choose_spec (Product.deloopingComparison_compact_lifts W W _ f)
  exact ⟨g, fun z hz ↦ Product.deloopingComparison_injective W W
    ((ContinuousMap.congr_fun hg z).trans
      ((_root_.Prod.ext (p.property z hz) (q.property z hz)).trans
        (Product.deloopingComparison_basepoint W W).symm))⟩

/-- Both original projections are retained at every spatial coordinate. -/
theorem productCubeLift_projection
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (z : Fin (n + 1) → unitInterval) :
    Product.deloopingComparison W W (productCubeLift W n p q z) = (p z, q z) := by
  unfold productCubeLift
  exact ContinuousMap.congr_fun (Classical.choose_spec
    (Product.deloopingComparison_compact_lifts W W _ (p.val.prodMk q.val))) z

/-- The actual projections determine the complete lift, including all supplied faces. -/
theorem productCubeLift_unique
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (g : GenLoop (Fin (n + 1)) (productStructure W W).Delooping
      (productStructure W W).kBasepoint)
    (hg : ∀ z, Product.deloopingComparison W W (g z) = (p z, q z)) :
    g = productCubeLift W n p q := by
  apply GenLoop.ext
  intro z
  exact Product.deloopingComparison_injective W W
    ((hg z).trans (productCubeLift_projection W n p q z).symm)

/-- The whole spatial boundary is the original product chosen zero. -/
theorem productCubeLift_boundary
    (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    productCubeLift W n p q z = (productStructure W W).kBasepoint :=
  (productCubeLift W n p q).property z hz

/-- Constant inputs have precisely the original constant lift. -/
theorem productCubeLift_const :
    productCubeLift W n GenLoop.const GenLoop.const = GenLoop.const := by
  symm
  exact productCubeLift_unique W n _ _ _ (fun _ ↦ Product.deloopingComparison_basepoint W W)

/-- Compact-family continuity comes from a lift of the entire parameter/spatial product. -/
theorem continuous_productCubeLift {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) :
    Continuous (fun t ↦ productCubeLift W n (p t) (q t)) := by
  let f : C(T × (Fin (n + 1) → unitInterval), W.Delooping × W.Delooping) :=
    ⟨fun z ↦ (p z.1 z.2, q z.1 z.2), by fun_prop⟩
  obtain ⟨g, hg⟩ := Product.deloopingComparison_compact_lifts W W _ f
  have he (t : T) (z : Fin (n + 1) → unitInterval) :
      productCubeLift W n (p t) (q t) z = g (t, z) :=
    Product.deloopingComparison_injective W W
      ((productCubeLift_projection W n (p t) (q t) z).trans
        (ContinuousMap.congr_fun hg (t, z)).symm)
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact g.continuous.congr (fun z ↦ (he z.1 z.2).symm)

/-- A continuous compact family of the unique original product lifts. -/
def productCubeFamily {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) :
    C(T, GenLoop (Fin (n + 1)) (productStructure W W).Delooping
      (productStructure W W).kBasepoint) :=
  ⟨fun t ↦ productCubeLift W n (p t) (q t), continuous_productCubeLift W n p q⟩

/-- Recover an existing entire face directly from its exact original projections. -/
theorem productCubeFamily_face {T S : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) (i : S → T)
    (g : S → GenLoop (Fin (n + 1)) (productStructure W W).Delooping
      (productStructure W W).kBasepoint)
    (hg : ∀ s z, Product.deloopingComparison W W (g s z) = (p (i s) z, q (i s) z))
    (s : S) : productCubeFamily W n p q (i s) = g s :=
  (productCubeLift_unique W n _ _ (g s) (hg s)).symm

variable [HasBinaryCoproducts C]

/-- The original canonical chosen-zero coproduct realization map. -/
def coproductBasedMap : C((productStructure W W).Delooping, W.Delooping) :=
  (deloopingMap (coproductFunctor_isExact W).rebase).hom

/-- The specified coproduct normalization preserves the original chosen zero. -/
theorem coproductBasedMap_basepoint :
    coproductBasedMap W (productStructure W W).kBasepoint = W.kBasepoint :=
  KMap_basepoint (coproductFunctor_isExact W)

/-- The actual quotient-first coproduct cube, using the unique compact lift. -/
def coproductCube (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :
    GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint :=
  GenLoop.postcomp (coproductBasedMap W) (coproductBasedMap_basepoint W)
    (productCubeLift W n p q)

/-- The original normalized coproduct is evaluated on the actual product lift. -/
theorem coproductCube_apply (p q : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)
    (z : Fin (n + 1) → unitInterval) :
    coproductCube W n p q z = coproductBasedMap W (productCubeLift W n p q z) := rfl

/-- Joint continuity for every compact family retains all supplied parameter times. -/
def coproductCubeFamily {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) :
    C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint) :=
  (genLoopPostcompContinuousMap (coproductBasedMap W) (coproductBasedMap_basepoint W)).comp
    (productCubeFamily W n p q)

/-- The compact family has exactly the original pointwise coproduct cube. -/
theorem coproductCubeFamily_apply {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) (t : T) :
    coproductCubeFamily W n p q t = coproductCube W n (p t) (q t) := rfl

/-- Every parameter slice retains the complete original spatial boundary. -/
theorem coproductCubeFamily_boundary {T : Type} [TopologicalSpace T] [CompactSpace T]
    (p q : C(T, GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint)) (t : T)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    coproductCubeFamily W n p q t z = W.kBasepoint :=
  (coproductCubeFamily W n p q t).property z hz

/-- The same whole compact construction yields an actual path of coproduct cubes. -/
def coproductCubePath
    {p₀ p₁ q₀ q₁ : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (P : Path p₀ p₁) (Q : Path q₀ q₁) :
    Path (coproductCube W n p₀ q₀) (coproductCube W n p₁ q₁) where
  toFun := coproductCubeFamily W n P.toContinuousMap Q.toContinuousMap
  continuous_toFun := (coproductCubeFamily W n P.toContinuousMap Q.toContinuousMap).continuous
  source' := congrArg₂ (coproductCube W n) P.source Q.source
  target' := congrArg₂ (coproductCube W n) P.target Q.target

/-- Both original path times are the displayed common compact-family parameter. -/
theorem coproductCubePath_apply
    {p₀ p₁ q₀ q₁ : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}
    (P : Path p₀ p₁) (Q : Path q₀ q₁) (t : unitInterval) :
    coproductCubePath W n P Q t = coproductCube W n (P t) (Q t) := rfl


attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductCube.lean:52-61" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  productCubeLift_unique

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductCube.lean:100-106" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  productCubeFamily_face

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductCube.lean:131-135" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductCubeFamily

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductCube.lean:143-147" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductCubeFamily_boundary

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductCube.lean:150-157" "adaptation"
    "Original compact-coproduct construction with every supplied parameter, boundary \
      and endpoint transport retained"]
  coproductCubePath

end CategoryTheory.Waldhausen.Additivity
