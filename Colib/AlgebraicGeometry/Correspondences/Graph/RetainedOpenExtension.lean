/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.OpenRestriction
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeSupport
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.OriginalRetainedProduct

/-!
# Postcomposition of a retained span with the original target inclusion
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The actual open extension identifies both legs of the whole retained support.
The target leg includes the specified original open inclusion. -/
theorem exists_retainedSupportOpenExtensionIso {S B C V Y : Scheme.{u}}
    (b : B ⟶ S) (π : C ⟶ S) (v : V ⟶ C) [IsOpenImmersion v]
    (j : Y ⟶ C) [IsOpenImmersion j] (u : V ⟶ Y) (hu : u ≫ j = v)
    (I : (pullback b π).IdealSheafData)
    (K : (retainedProduct b π v).IdealSheafData)
    (hK : K = I.comap (retainedProductInclusion b π v))
    (J : (retainedProduct b π j).IdealSheafData)
    (hJ : J = I.comap (retainedProductInclusion b π j))
    (hI : Set.range I.subschemeι ⊆ Set.range (retainedProductInclusion b π v)) :
    ∃ e : K.subscheme ≅ J.subscheme,
      e.hom ≫ J.subschemeι ≫ pullback.fst b (j ≫ π) =
        K.subschemeι ≫ pullback.fst b (v ≫ π) ∧
      e.hom ≫ J.subschemeι ≫ pullback.snd b (j ≫ π) =
        K.subschemeι ≫ pullback.snd b (v ≫ π) ≫ u := by
  let m := retainedProductOpenFactor b π v j u hu
  have hm : m ≫ retainedProductInclusion b π j = retainedProductInclusion b π v :=
    retainedProductOpenFactor_inclusion b π v j u hu
  have hK' : K = J.comap m := by
    rw [hK, hJ, ← Scheme.IdealSheafData.comap_comp, hm]
  have hJ' : Set.range J.subschemeι ⊆ Set.range m := by
    rw [hJ]
    apply comap_whole_support_subset_of_open_factor (retainedProductInclusion b π j) m I
    rwa [hm]
  obtain ⟨e, he⟩ := exists_openSupportIso m J K hK' hJ'
  refine ⟨e, ?_, ?_⟩
  · rw [← Category.assoc, he, Category.assoc]
    exact congrArg (fun f => K.subschemeι ≫ f) (retainedProductOpenFactor_fst b π v j u hu)
  · rw [← Category.assoc, he, Category.assoc]
    exact congrArg (fun f => K.subschemeι ≫ f) (retainedProductOpenFactor_snd b π v j u hu)

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme

/-- An isomorphism preserving the original source and the postcomposed target
leg identifies the extended span with postcomposition by the actual graph. -/
theorem ofFiniteFlatSpan_comp_graph_eq_of_iso {k : Type u} [Field k]
    {X Y Z : SmoothSite (Spec (.of k))} {D E : Scheme.{u}}
    (u : Y ⟶ Z) (e : D ≅ E) (f : D ⟶ X.left) [IsFinite f] [Flat f]
    (g : D ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom)
    (f' : E ⟶ X.left) [IsFinite f'] [Flat f']
    (g' : E ⟶ Z.left) (h' : f' ≫ X.hom = g' ≫ Z.hom)
    (hf : e.hom ≫ f' = f) (hg : e.hom ≫ g' = g ≫ u.left) :
    ofFiniteFlatSpan f g h ≫ (graphFunctor k).map u = ofFiniteFlatSpan f' g' h' := by
  rw [ofFiniteFlatSpan_comp_graph]
  exact ofFiniteFlatSpan_eq_of_iso e f (g ≫ u.left) _ f' g' h' hf hg

/-- Postcomposition identifies the raw scheme spans with the same original
closed supports and finite-flat legs. -/
theorem ofFiniteFlatSpanRaw_comp_graph_eq_of_iso {k : Type u} [Field k]
    {X Y Z : SmoothSite (Spec (.of k))} {D E : Scheme.{u}}
    (u : Y ⟶ Z) (e : D ≅ E) (f : D ⟶ X.left) [IsFinite f] [Flat f]
    (g : D ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom)
    (f' : E ⟶ X.left) [IsFinite f'] [Flat f']
    (g' : E ⟶ Z.left) (h' : f' ≫ X.hom = g' ≫ Z.hom)
    (hf : e.hom ≫ f' = f) (hg : e.hom ≫ g' = g ≫ u.left) :
    letI : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
    let C : Cor.mk X ⟶ Cor.mk Y := ofFiniteFlatSpanRaw X.hom Y.hom f g h
    let C' : Cor.mk X ⟶ Cor.mk Z := ofFiniteFlatSpanRaw X.hom Z.hom f' g' h'
    C ≫ (graphFunctor k).map u = C' :=
  ofFiniteFlatSpan_comp_graph_eq_of_iso u e f g h f' g' h' hf hg

/-- The two whole spans and their exact support isomorphism over graph postcomposition. -/
structure SpanGraphIsomorphismData {k : Type u} [Field k]
    (X Y Z : SmoothSite (Spec (.of k))) (u : Y ⟶ Z) (D E : Scheme.{u}) where
  /-- The finite flat source leg from the first support `D` to `X`. -/
  source : D ⟶ X.left
  sourceFinite : IsFinite source
  sourceFlat : Flat source
  /-- The target leg from `D` to `Y` before postcomposition with `u`. -/
  target : D ⟶ Y.left
  overBase : source ≫ X.hom = target ≫ Y.hom
  /-- The finite flat source leg from the comparison support `E` to `X`. -/
  originalSource : E ⟶ X.left
  originalFinite : IsFinite originalSource
  originalFlat : Flat originalSource
  /-- The target leg from `E` to `Z`, identified with `target ≫ u.left` on `D`. -/
  originalTarget : E ⟶ Z.left
  originalOverBase : originalSource ≫ X.hom = originalTarget ≫ Z.hom
  /-- The support isomorphism preserving the source leg and the postcomposed target leg. -/
  supportIso : D ≅ E
  source_eq : supportIso.hom ≫ originalSource = source
  target_eq : supportIso.hom ≫ originalTarget = target ≫ u.left

/-- The raw comparison of the two whole spans specified by these legs. -/
@[no_expose]
abbrev SpanGraphIsomorphismData.compGraphProof {k : Type u} [Field k]
    {X Y Z : SmoothSite (Spec (.of k))} {D E : Scheme.{u}} {u : Y ⟶ Z}
    (d : SpanGraphIsomorphismData (k := k) X Y Z u D E) :=
  @ofFiniteFlatSpanRaw_comp_graph_eq_of_iso k ‹Field k› X Y Z D E u d.supportIso
    d.source d.sourceFinite d.sourceFlat d.target d.overBase
    d.originalSource d.originalFinite d.originalFlat d.originalTarget d.originalOverBase
    d.source_eq d.target_eq

/-- The graph composite has the whole original support, with its two actual legs. -/
theorem SpanGraphIsomorphismData.comp_graph_eq {k : Type u} [Field k]
    {X Y Z : SmoothSite (Spec (.of k))} {D E : Scheme.{u}} {u : Y ⟶ Z}
    (d : SpanGraphIsomorphismData (k := k) X Y Z u D E) :
    type_of% (SpanGraphIsomorphismData.compGraphProof (k := k) d) :=
  SpanGraphIsomorphismData.compGraphProof (k := k) d

end AlgebraicGeometry.Cor
