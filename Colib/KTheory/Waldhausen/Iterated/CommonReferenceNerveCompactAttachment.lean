/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNervePointwiseFamily
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceWhiskering
public import Colib.KTheory.Waldhausen.Iterated.SimplexWhiskering

/-!
# Compact evaluation of the original common-reference attachments

The finite representatives are the existing characteristic simplices of the same nerve.
Whiskering and reanchoring their full nodes preserves their evaluation at that exact
simplex point and at every native level.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor Convexity
open scoped Simplicial Topology

universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve

open SmallWaldhausenCategory

variable {U V W T : WideSubcategory preservesZero.{u}}
variable {P : Type v} [TopologicalSpace P] [CompactSpace P]

/-- Postcomposition retains the complete original compact family. -/
theorem compactPrespectrumFamily_attachPostcomp
    (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
    (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)
    (p : C(P, |nerve (Codiscrete (Node F))|)) (n : ℕ) (t : P)
    (x : (prespectrum V).space n) :
    compactPrespectrumFamily G ((mapParameter (attachPostcompNode F J G ε)).comp p)
        n (t, x) =
      (prespectrumMap J).map n (compactPrespectrumFamily F p n (t, x)) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (p t)
  have hp : ((mapParameter (attachPostcompNode F J G ε)).comp p) t =
      parameter G (fun i ↦ attachPostcompNode F J G ε (N i)) z := by
    change mapParameter (attachPostcompNode F J G ε) (p t) = _
    rw [← hz, mapParameter_parameter]
  rw [compactPrespectrumFamily_eq_simplex G _ _ t z hp n x,
    compactPrespectrumFamily_eq_simplex F p N t z hz.symm n x]
  exact simplexFamily_attachPostcomp F J G ε N n z x

/-- The actual precomposed node retains its prescribed reference isomorphism. -/
def attachPrecompNode (F : V ⟶ W) (J : U ⟶ V) (G : U ⟶ W)
    (ε : G.hom.toFunctor ≅ (J ≫ F).hom.toFunctor) (N : Node F) : Node G :=
  ⟨J ≫ N.1, ε ≪≫ isoWhiskerLeft J.hom.toFunctor N.2⟩

/-- Strict precomposition of the identity-anchored source retains its entire reference. -/
theorem attachPrecompNode_source (F : V ⟶ W) (J : U ⟶ V) (G : U ⟶ W)
    (ε : G.hom.toFunctor ≅ (J ≫ F).hom.toFunctor) :
    attachPrecompNode F J G ε ⟨F, Iso.refl _⟩ = ⟨J ≫ F, ε⟩ := by
  have h : ε ≪≫ isoWhiskerLeft J.hom.toFunctor (Iso.refl F.hom.toFunctor) = ε := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    change ε.hom.app X ≫ 𝟙 _ = ε.hom.app X
    exact Category.comp_id _
  exact congrArg (fun σ : G.hom.toFunctor ≅ (J ≫ F).hom.toFunctor ↦
    (⟨J ≫ F, σ⟩ : Node G)) h

/-- Reanchoring and precomposition leave the simplex parameter unchanged. -/
theorem simplexFamily_attachPrecomp
    (F : V ⟶ W) (J : U ⟶ V) (G : U ⟶ W)
    (ε : G.hom.toFunctor ≅ (J ≫ F).hom.toFunctor) {k : ℕ}
    (N : Fin (k + 1) → Node F) (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (prespectrum U).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos G
        (fun i ↦ (attachPrecompNode F J G ε (N i)).1)
        (fun i ↦ (attachPrecompNode F J G ε (N i)).2)) n (z, x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos F
        (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n (z, (prespectrumMap J).map n x) := by
  change prespectrumSimplexFamily
    (ModelSimplex.reanchorSimplex ε (fun i ↦
      ⟨J ≫ (N i).1, isoWhiskerLeft J.hom.toFunctor (N i).2⟩)) n (z, x) = _
  rw [ModelSimplex.reanchorSimplex_eq, ← ModelSimplex.ofIsos_precomp]
  exact prespectrumSimplexFamily_precomp _ J n z x

/-- Precomposition changes only the original native input of the compact family. -/
theorem compactPrespectrumFamily_attachPrecomp
    (F : V ⟶ W) (J : U ⟶ V) (G : U ⟶ W)
    (ε : G.hom.toFunctor ≅ (J ≫ F).hom.toFunctor)
    (p : C(P, |nerve (Codiscrete (Node F))|)) (n : ℕ) (t : P)
    (x : (prespectrum U).space n) :
    compactPrespectrumFamily G ((mapParameter (attachPrecompNode F J G ε)).comp p)
        n (t, x) =
      compactPrespectrumFamily F p n (t, (prespectrumMap J).map n x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (p t)
  have hp : ((mapParameter (attachPrecompNode F J G ε)).comp p) t =
      parameter G (fun i ↦ attachPrecompNode F J G ε (N i)) z := by
    change mapParameter (attachPrecompNode F J G ε) (p t) = _
    rw [← hz, mapParameter_parameter]
  rw [compactPrespectrumFamily_eq_simplex G _ _ t z hp n x,
    compactPrespectrumFamily_eq_simplex F p N t z hz.symm n ((prespectrumMap J).map n x)]
  exact simplexFamily_attachPrecomp F J G ε N n z x

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
