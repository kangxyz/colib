/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceSimplex

/-!
# Both whiskerings of a family of full reference nodes

The family records exact functors and their comparison isomorphisms. Equality
of one complete node identifies the reference isomorphisms and therefore all
nodes. Adapted from `ReferenceRowTransport.lean` and
`ReferenceWhiskeringFamily.lean` in the original BoundedFlat Bass proof
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
open SmallWaldhausenCategory
universe u v
namespace CategoryTheory.Waldhausen.IteratedS.ModelSimplex
section ReferenceNodes

variable {V W T : WideSubcategory preservesZero.{u}}

/-- Postcompose the full dependent reference node using the specified reference comparison. -/
def postReferenceNode (F : V ⟶ T) (J : W ⟶ T) {H : V ⟶ W}
    (ρ : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor)
    (N : Σ G : V ⟶ W, H.hom.toFunctor ≅ G.hom.toFunctor) :
    Σ G : V ⟶ T, F.hom.toFunctor ≅ G.hom.toFunctor :=
  ⟨N.1 ≫ J, ρ ≪≫ isoWhiskerRight N.2 J.hom.toFunctor⟩

/-- Precompose the full dependent reference node using the specified reference comparison. -/
def preReferenceNode (F : V ⟶ T) (P : V ⟶ W) {H : W ⟶ T}
    (ρ : F.hom.toFunctor ≅ (P ≫ H).hom.toFunctor)
    (N : Σ G : W ⟶ T, H.hom.toFunctor ≅ G.hom.toFunctor) :
    Σ G : V ⟶ T, F.hom.toFunctor ≅ G.hom.toFunctor :=
  ⟨P ≫ N.1, ρ ≪≫ isoWhiskerLeft P.hom.toFunctor N.2⟩

end ReferenceNodes

variable {V₀ W₀ V W : WideSubcategory preservesZero.{u}} {I : Type v}
  (F : V ⟶ W) (P : V ⟶ V₀) (J : W₀ ⟶ W) (H : V₀ ⟶ W₀)
  (D : I → Σ G : V₀ ⟶ W₀, H.hom.toFunctor ≅ G.hom.toFunctor)

/-- Both fixed original maps are retained around every full input reference node. -/
def prePostNodes (ρ : F.hom.toFunctor ≅ (P ≫ H ≫ J).hom.toFunctor) (i : I) :
    Σ G : V ⟶ W, F.hom.toFunctor ≅ G.hom.toFunctor :=
  ⟨P ≫ (D i).1 ≫ J,
    ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (isoWhiskerRight (D i).2 J.hom.toFunctor)⟩

/-- Literal interchange of the two fixed functor whiskerings. -/
theorem whisker_iso_interchange {G : V₀ ⟶ W₀} (ν : H.hom.toFunctor ≅ G.hom.toFunctor) :
    isoWhiskerRight (isoWhiskerLeft P.hom.toFunctor ν) J.hom.toFunctor =
      isoWhiskerLeft P.hom.toFunctor (isoWhiskerRight ν J.hom.toFunctor) := by
  apply Iso.ext
  ext X
  rfl

/-- Postcompose an original precomposed node; only its genuine reference association changes. -/
theorem post_pre_node {K : V ⟶ W₀}
    (ρ : K.hom.toFunctor ≅ (P ≫ H).hom.toFunctor)
    (η : F.hom.toFunctor ≅ (K ≫ J).hom.toFunctor)
    (i : I) :
    postReferenceNode F J η (preReferenceNode K P ρ (D i)) =
      prePostNodes F P J H D (η ≪≫ isoWhiskerRight ρ J.hom.toFunctor) i := by
  have hF : ((P ≫ (D i).1) ≫ J).hom.toFunctor = (P ≫ (D i).1 ≫ J).hom.toFunctor := rfl
  apply reference_node_eq hF
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change η ≪≫
      isoWhiskerRight (ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (D i).2) J.hom.toFunctor =
    (η ≪≫ isoWhiskerRight ρ J.hom.toFunctor) ≪≫
      isoWhiskerLeft P.hom.toFunctor (isoWhiskerRight (D i).2 J.hom.toFunctor)
  rw [isoWhiskerRight_trans, whisker_iso_interchange, Iso.trans_assoc]

/-- Precompose an original postcomposed node with the same two actual fixed maps. -/
theorem pre_post_node {K : V₀ ⟶ W}
    (ρ : K.hom.toFunctor ≅ (H ≫ J).hom.toFunctor)
    (η : F.hom.toFunctor ≅ (P ≫ K).hom.toFunctor)
    (i : I) :
    preReferenceNode F P η (postReferenceNode K J ρ (D i)) =
      prePostNodes F P J H D (η ≪≫ isoWhiskerLeft P.hom.toFunctor ρ) i := by
  have hF : (P ≫ (D i).1 ≫ J).hom.toFunctor = (P ≫ (D i).1 ≫ J).hom.toFunctor := rfl
  apply reference_node_eq hF
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change η ≪≫
      isoWhiskerLeft P.hom.toFunctor (ρ ≪≫ isoWhiskerRight (D i).2 J.hom.toFunctor) =
    (η ≪≫ isoWhiskerLeft P.hom.toFunctor ρ) ≪≫
      isoWhiskerLeft P.hom.toFunctor (isoWhiskerRight (D i).2 J.hom.toFunctor)
  rw [isoWhiskerLeft_trans, Iso.trans_assoc]

/-- A full shared node determines this fixed reference family by iso cancellation. -/
theorem prePost_eq_of_node
    {ρ σ : F.hom.toFunctor ≅ (P ≫ H ≫ J).hom.toFunctor} (j : I)
    (he : prePostNodes F P J H D ρ j = prePostNodes F P J H D σ j) (i : I) :
    prePostNodes F P J H D ρ i = prePostNodes F P J H D σ i := by
  have hs : (prePostNodes F P J H D ρ j).2 = (prePostNodes F P J H D σ j).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  change ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (isoWhiskerRight (D j).2 J.hom.toFunctor) =
    σ ≪≫ isoWhiskerLeft P.hom.toFunctor (isoWhiskerRight (D j).2 J.hom.toFunctor) at hs
  have hc := congrArg
    (fun η ↦ η ≪≫
      (isoWhiskerLeft P.hom.toFunctor (isoWhiskerRight (D j).2 J.hom.toFunctor)).symm) hs
  have hρ : ρ = σ := by simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc
  exact congrArg (fun η ↦ prePostNodes F P J H D η i) hρ

/-- Two actual row representations with one full shared node retain every member of the family. -/
theorem prePost_families_match
    {N M : I → Σ G : V ⟶ W, F.hom.toFunctor ≅ G.hom.toFunctor}
    {ρ σ : F.hom.toFunctor ≅ (P ≫ H ≫ J).hom.toFunctor}
    (hN : ∀ i, N i = prePostNodes F P J H D ρ i)
    (hM : ∀ i, M i = prePostNodes F P J H D σ i)
    (j : I) (he : N j = M j) (i : I) : N i = M i :=
  (hN i).trans ((prePost_eq_of_node F P J H D j
    ((hN j).symm.trans (he.trans (hM j))) i).trans (hM i).symm)

section DoublePostcomposition

variable {U₀ U₁ U₂ U₃ : WideSubcategory preservesZero.{u}} {A : Type v}

/-- Two actual fixed postcompositions retain the original family and canonical association. -/
theorem post_post_node (F : U₀ ⟶ U₃) (J : U₁ ⟶ U₂) (K : U₂ ⟶ U₃)
    (H : U₀ ⟶ U₁) {L : U₀ ⟶ U₂}
    (ρ : L.hom.toFunctor ≅ (H ≫ J).hom.toFunctor)
    (η : F.hom.toFunctor ≅ (L ≫ K).hom.toFunctor)
    (N : Σ G : U₀ ⟶ U₁, H.hom.toFunctor ≅ G.hom.toFunctor) :
    postReferenceNode F K η (postReferenceNode L J ρ N) =
      postReferenceNode F (J ≫ K) (η ≪≫ isoWhiskerRight ρ K.hom.toFunctor) N := by
  rcases N with ⟨G, σ⟩
  have hf : ((G ≫ J) ≫ K).hom.toFunctor = (G ≫ (J ≫ K)).hom.toFunctor := rfl
  apply reference_node_eq hf
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change η ≪≫ isoWhiskerRight (ρ ≪≫ isoWhiskerRight σ J.hom.toFunctor) K.hom.toFunctor =
    (η ≪≫ isoWhiskerRight ρ K.hom.toFunctor) ≪≫ isoWhiskerRight σ (J ≫ K).hom.toFunctor
  have hw : isoWhiskerRight (isoWhiskerRight σ J.hom.toFunctor) K.hom.toFunctor =
      isoWhiskerRight σ (J ≫ K).hom.toFunctor := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    rfl
  rw [isoWhiskerRight_trans, Iso.trans_assoc, hw]

variable (F : U₀ ⟶ U₂) (J : U₁ ⟶ U₂) (H : U₀ ⟶ U₁)
  (D : A → Σ G : U₀ ⟶ U₁, H.hom.toFunctor ≅ G.hom.toFunctor)

/-- One full node cancels the genuine reference iso for every fixed postcomposed node. -/
theorem post_eq_of_node {ρ σ : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor} (j : A)
    (he : postReferenceNode F J ρ (D j) = postReferenceNode F J σ (D j)) (i : A) :
    postReferenceNode F J ρ (D i) = postReferenceNode F J σ (D i) := by
  have hs : (postReferenceNode F J ρ (D j)).2 = (postReferenceNode F J σ (D j)).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  change ρ ≪≫ isoWhiskerRight (D j).2 J.hom.toFunctor =
    σ ≪≫ isoWhiskerRight (D j).2 J.hom.toFunctor at hs
  have hc := congrArg (fun ν ↦ ν ≪≫ (isoWhiskerRight (D j).2 J.hom.toFunctor).symm) hs
  have hρ : ρ = σ := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc
  exact congrArg (fun η ↦ postReferenceNode F J η (D i)) hρ

/-- Full native row representations and one full shared node determine the whole row. -/
theorem post_families_match
    {N M : A → Σ G : U₀ ⟶ U₂, F.hom.toFunctor ≅ G.hom.toFunctor}
    {ρ σ : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor}
    (hN : ∀ i, N i = postReferenceNode F J ρ (D i))
    (hM : ∀ i, M i = postReferenceNode F J σ (D i))
    (j : A) (he : N j = M j) (i : A) : N i = M i :=
  (hN i).trans ((post_eq_of_node F J H D j
    ((hN j).symm.trans (he.trans (hM j))) i).trans (hM i).symm)

end DoublePostcomposition

section DoublePrecomposition

variable {U V W T : WideSubcategory preservesZero.{u}} {I : Type v}

/-- Two original fixed precompositions retain their actual full reference association. -/
theorem pre_pre_node (F : U ⟶ T) (P : U ⟶ V) (Q : V ⟶ W) (H : W ⟶ T) {L : V ⟶ T}
    (ρ : L.hom.toFunctor ≅ (Q ≫ H).hom.toFunctor)
    (η : F.hom.toFunctor ≅ (P ≫ L).hom.toFunctor)
    (N : Σ G : W ⟶ T, H.hom.toFunctor ≅ G.hom.toFunctor) :
    preReferenceNode F P η (preReferenceNode L Q ρ N) =
      preReferenceNode F (P ≫ Q) (η ≪≫ isoWhiskerLeft P.hom.toFunctor ρ) N := by
  rcases N with ⟨G, σ⟩
  have hf : (P ≫ Q ≫ G).hom.toFunctor = ((P ≫ Q) ≫ G).hom.toFunctor := rfl
  apply reference_node_eq hf
  simp only [eqToHom_refl, Category.comp_id]
  apply congrArg Iso.hom
  change η ≪≫ isoWhiskerLeft P.hom.toFunctor (ρ ≪≫ isoWhiskerLeft Q.hom.toFunctor σ) =
    (η ≪≫ isoWhiskerLeft P.hom.toFunctor ρ) ≪≫ isoWhiskerLeft (P ≫ Q).hom.toFunctor σ
  have hw : isoWhiskerLeft P.hom.toFunctor (isoWhiskerLeft Q.hom.toFunctor σ) =
      isoWhiskerLeft (P ≫ Q).hom.toFunctor σ := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    rfl
  rw [isoWhiskerLeft_trans, Iso.trans_assoc, hw]

variable (F : V ⟶ T) (P : V ⟶ W) (H : W ⟶ T)
  (D : I → Σ G : W ⟶ T, H.hom.toFunctor ≅ G.hom.toFunctor)

/-- A full shared node determines the unchanged precomposed family through iso cancellation. -/
theorem pre_eq_of_node {ρ σ : F.hom.toFunctor ≅ (P ≫ H).hom.toFunctor} (j : I)
    (he : preReferenceNode F P ρ (D j) = preReferenceNode F P σ (D j)) (i : I) :
    preReferenceNode F P ρ (D i) = preReferenceNode F P σ (D i) := by
  have hs : (preReferenceNode F P ρ (D j)).2 = (preReferenceNode F P σ (D j)).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  change ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (D j).2 =
    σ ≪≫ isoWhiskerLeft P.hom.toFunctor (D j).2 at hs
  have hc := congrArg (fun ν ↦ ν ≪≫ (isoWhiskerLeft P.hom.toFunctor (D j).2).symm) hs
  have hρ : ρ = σ := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc
  exact congrArg (fun η ↦ preReferenceNode F P η (D i)) hρ

/-- A full common node determines both actual precomposed row representations. -/
theorem pre_families_match
    {N M : I → Σ G : V ⟶ T, F.hom.toFunctor ≅ G.hom.toFunctor}
    {ρ σ : F.hom.toFunctor ≅ (P ≫ H).hom.toFunctor}
    (hN : ∀ i, N i = preReferenceNode F P ρ (D i))
    (hM : ∀ i, M i = preReferenceNode F P σ (D i))
    (j : I) (he : N j = M j) (i : I) : N i = M i :=
  (hN i).trans ((pre_eq_of_node F P H D j
    ((hN j).symm.trans (he.trans (hM j))) i).trans (hM i).symm)

/-- The same matching argument applies when the two precomposition maps agree by transport. -/
theorem pre_families_match_maps {Q : V ⟶ W}
    (hPQ : P = Q)
    {N M : I → Σ G : V ⟶ T, F.hom.toFunctor ≅ G.hom.toFunctor}
    {ρ : F.hom.toFunctor ≅ (P ≫ H).hom.toFunctor}
    {σ : F.hom.toFunctor ≅ (Q ≫ H).hom.toFunctor}
    (hN : ∀ i, N i = preReferenceNode F P ρ (D i))
    (hM : ∀ i, M i = preReferenceNode F Q σ (D i))
    (j : I) (he : N j = M j) (i : I) : N i = M i := by
  subst Q
  exact pre_families_match F P H D hN hM j he i

end DoublePrecomposition

end CategoryTheory.Waldhausen.IteratedS.ModelSimplex
