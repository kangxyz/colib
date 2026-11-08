/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentEuler
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapComponent

/-!
# The full image-component exterior is the actual remaining support product

The closure of an original image point inside the whole scheme-theoretic image
is identified with its closure in the original adjacent product by the native
closed-immersion component comparison. Base change by the fixed third support
then identifies the full image-component exterior with the actual remaining
correspondence support product. Both maps into the remaining fourfold ambient
are preserved. Neither exterior product is reduced, and the proof imposes no
field, flatness, irreducibility, or equidimensionality hypothesis on the ambient
schemes. The integral point closures are the existing native ones.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "r" => correspondenceIncidenceMap f g h z w
local notation3 (prettyPrint := false) "J" => correspondenceIntermediateImage f g h z w
local notation3 (prettyPrint := false) "F" => integralComponentAt ((r).toImage t)
local notation3 (prettyPrint := false) "G" => integralComponentAt (r t)
local notation3 (prettyPrint := false) "V" => integralComponentAt v
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" => ((V).subschemeι ≫ pullback.fst h i) ≫ h
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "π'" =>
  correspondenceLeftImageExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct f h i (r t) v
local notation3 (prettyPrint := false) "j" => correspondenceLeftImageProductInclusion f g h i z w v
local notation3 (prettyPrint := false) "ι" => correspondenceSupportProductInclusion f h i (r t) v

/-- The same image-point closure, read inside the whole intermediate image or inside the
original adjacent product, is canonically isomorphic over that adjacent product. -/
theorem exists_correspondenceRemainingImagePointIso :
    ∃ e : (F).subscheme ≅ (G).subscheme,
      e.hom ≫ (G).subschemeι = (F).subschemeι ≫ (r).imageι := by
  have H := exists_iso_integralComponentAt_comp (r).imageι ((r).toImage t)
  have hp : (r).imageι ((r).toImage t) = r t := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
  let pointStatement (a : pullback (C := Scheme) f h) : Prop :=
    ∃ e : (F).subscheme ≅ (integralComponentAt a).subscheme,
      e.hom ≫ (integralComponentAt a).subschemeι = (F).subschemeι ≫ (r).imageι
  have H' : pointStatement ((r).imageι ((r).toImage t)) := H
  exact (hp ▸ H' : pointStatement (r t))

/-- The actual full nonreduced inverse image of the original image closure is the actual
remaining support product, compatibly with the original fourfold ambient inclusion. -/
theorem exists_correspondenceRemainingImageComponentSupportIso :
    ∃ e : (D).subscheme ≅ P, e.hom ≫ ι = (D).subschemeι ≫ j := by
  obtain ⟨e₀, he₀⟩ := exists_correspondenceRemainingImagePointIso f g h z w t
  have hinv : e₀.inv ≫ (F).subschemeι ≫ (r).imageι = (G).subschemeι := by
    rw [← he₀]
    simp
  let b : (G).subscheme ⟶ J := e₀.inv ≫ (F).subschemeι
  have hb : b ≫ sJ = (G).subschemeι ≫ pullback.snd f h ≫ h := by
    simpa only [b, correspondenceIntermediateImageTarget, Category.assoc] using
      congrArg (fun m => m ≫ pullback.snd f h ≫ h) hinv
  let a : P ⟶ T := pullback.map _ _ _ _ b (𝟙 (V).subscheme) (𝟙 S)
    (by simpa only [Category.comp_id] using hb.symm) (by simp)
  have haπ : a ≫ π' = pullback.fst _ _ ≫ b := by
    simp [a, correspondenceLeftImageExteriorProjection]
  have haj : a ≫ j = ι := by
    apply pullback.hom_ext
    · simp only [Category.assoc, correspondenceLeftImageProductInclusion,
        correspondenceSupportProductInclusion, a, pullback.map, pullback.lift_fst_assoc,
        pullback.lift_fst, Category.comp_id]
      simpa only [b, Category.assoc] using
        congrArg (fun m => pullback.fst _ _ ≫ m) hinv
    · simp [a, correspondenceLeftImageProductInclusion,
        correspondenceSupportProductInclusion, pullback.map]
  have hp : IsPullback (pullback.fst _ _) (a ≫ pullback.snd _ _) (b ≫ sJ) sV := by
    have hsnd : a ≫ pullback.snd _ _ =
        pullback.snd ((G).subschemeι ≫ pullback.snd f h ≫ h)
          ((V).subschemeι ≫ pullback.fst h i ≫ h) := by
      simp [a, pullback.map]
    rw [hsnd, hb]
    convert IsPullback.of_hasPullback ((G).subschemeι ≫ pullback.snd f h ≫ h)
      ((V).subschemeι ≫ pullback.fst h i ≫ h) using 1
    simp only [Category.assoc]
  have ha : IsPullback a (pullback.fst _ _) π' b :=
    (hp.of_bot haπ.symm (IsPullback.of_hasPullback sJ sV)).flip
  have : IsClosedImmersion b := by dsimp only [b]; infer_instance
  have : IsClosedImmersion a := MorphismProperty.of_isPullback ha.flip inferInstance
  have hker : a.ker = D := by
    rw [← ha.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    simp only [b, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
  obtain ⟨e, he⟩ := exists_iso_of_ker_eq (D).subschemeι a
    ((Scheme.IdealSheafData.ker_subschemeι D).trans hker.symm)
  refine ⟨e, ?_⟩
  rw [← haj, ← Category.assoc, he]

end Stacks.Chow
