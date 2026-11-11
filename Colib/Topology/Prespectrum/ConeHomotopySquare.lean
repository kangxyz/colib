/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.HomotopyLoop
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.MappingCone

/-!
# Mapping-cone maps from whole homotopy squares

A specified coherent based homotopy-commuting square gives an actual map of the original reduced
mapping-cone prespectra. Its cylinder first traverses the supplied square homotopy in the target
and then the original target cone cylinder. The target inclusion commutes literally, and the whole
square track is retained, not replaced by its endpoints or a homotopy class.

This construction does not assert stable cofiber exactness, invariance under stable equivalences,
or functoriality of a Bass tower. The concatenated map need not equal the existing strict-square
cone map literally, even when the supplied square homotopy is constant.
-/

/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeHomotopySquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and independent parameters
are retained using native Colib and Mathlib objects. -/
@[expose] public section

noncomputable section


open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Topology.LoopPrespectrum

variable {E F E' F' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (a : E ⟶ E') (b : F ⟶ F')
  (H : Homotopy (f ≫ b) (a ≫ g))

/-- The whole square track followed by the actual target cone nullhomotopy. -/
def mappingConeSquareNullHomotopy :
    Homotopy (f ≫ (b ≫ mappingConeInclusion g)) (zeroHom E (mappingCone g)) :=
  ((H.postcomp (mappingConeInclusion g)).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)).trans
      ((Homotopy.precomp a (mappingConeHomotopy g)).cast rfl
        (show a ≫ zeroHom E' (mappingCone g) = zeroHom E (mappingCone g) from rfl))

/-- A genuinely homotopy-commuting square gives an actual reduced cone prespectrum map. -/
def mappingConeSquareMap : mappingCone f ⟶ mappingCone g :=
  mappingConeDesc f (b ≫ mappingConeInclusion g) (mappingConeSquareNullHomotopy f g a b H)

/-- The original target endpoint square commutes literally. -/
@[simp]
theorem mappingConeSquareMap_inclusion :
    mappingConeInclusion f ≫ mappingConeSquareMap f g a b H = b ≫ mappingConeInclusion g :=
  mappingConeInclusion_desc f _ _

/-- Every value of the original cone cylinder retains the full concatenated square track. -/
@[simp]
theorem mappingConeSquareMap_cylinder (n : ℕ) (s : unitInterval) (x : E.space n) :
    (mappingConeSquareMap f g a b H).map n
      (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) =
        (mappingConeSquareNullHomotopy f g a b H).level n (s, x) := rfl

/-- The first half retains every value of the supplied whole square homotopy. -/
theorem mappingConeSquareMap_first_half (n : ℕ) (t : unitInterval) (x : E.space n) :
    (mappingConeSquareMap f g a b H).map n
      (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n)
        (⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x)) =
      (mappingConeInclusion g).map n (H.level n (t, x)) := by
  change ((((H.postcomp (mappingConeInclusion g)).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)).levelHomotopy n).trans
    (((Homotopy.precomp a (mappingConeHomotopy g)).cast rfl
      (show a ≫ zeroHom E' (mappingCone g) = zeroHom E (mappingCone g) from rfl)).levelHomotopy
        n)) (⟨(t : ℝ) / 2, _⟩, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change (mappingConeInclusion g).map n (H.level n (⟨2 * ((t : ℝ) / 2), _⟩, x)) = _
    congr 2
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      ring
    · rfl
  · rename_i ht
    exfalso
    apply ht
    change (t : ℝ) / 2 ≤ 1 / 2
    linarith [t.2.2]

/-- The second half is the actual target cone coordinate on the original source image. -/
theorem mappingConeSquareMap_second_half (n : ℕ) (t : unitInterval) (x : E.space n) :
    (mappingConeSquareMap f g a b H).map n
      (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n)
        (⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x)) =
      ReducedMappingCone.cylinder (E'.point n) (F'.point n) (g.map n) (t, a.map n x) := by
  change ((((H.postcomp (mappingConeInclusion g)).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)).levelHomotopy n).trans
    (((Homotopy.precomp a (mappingConeHomotopy g)).cast rfl
      (show a ≫ zeroHom E' (mappingCone g) = zeroHom E (mappingCone g) from rfl)).levelHomotopy n))
      (⟨((t : ℝ) + 1) / 2, _⟩, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i ht
    have ht0 : t = 0 := by
      apply Subtype.ext
      change (t : ℝ) = 0
      have hh : ((t : ℝ) + 1) / 2 ≤ 1 / 2 := ht
      linarith [t.2.1]
    subst t
    have hs : (⟨2 * (((0 : ℝ) + 1) / 2), by norm_num⟩ : unitInterval) = 1 := by
      apply Subtype.ext
      norm_num
    change (mappingConeInclusion g).map n
      (H.level n ((⟨2 * (((0 : ℝ) + 1) / 2), by norm_num⟩ : unitInterval), x)) = _
    rw [hs, H.at_one]
    exact (ReducedMappingCone.cylinder_zero (E'.point n) (F'.point n) (g.map n)
      (a.map n x)).symm
  · change ReducedMappingCone.cylinder (E'.point n) (F'.point n) (g.map n)
      (⟨2 * (((t : ℝ) + 1) / 2) - 1, _⟩, a.map n x) = _
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      ring
    · rfl

/-- Parameter-correct looping retains the literal target inclusion square. -/
theorem mappingConeSquareMap_parameterLooping_inclusion :
    parameterLoopingMap (mappingConeInclusion f) ≫
        parameterLoopingMap (mappingConeSquareMap f g a b H) =
      parameterLoopingMap b ≫ parameterLoopingMap (mappingConeInclusion g) := by
  change parameterLoopingFunctor.map (mappingConeInclusion f) ≫
      parameterLoopingFunctor.map (mappingConeSquareMap f g a b H) =
    parameterLoopingFunctor.map b ≫ parameterLoopingFunctor.map (mappingConeInclusion g)
  rw [← Functor.map_comp, mappingConeSquareMap_inclusion, Functor.map_comp]

end Topology.LoopPrespectrum

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/ConeHomotopySquare.lean:43-130"
  "adaptation" "Actual cone map retaining supplied square on its first half and target cylinder \
    on its second"]
  Topology.LoopPrespectrum.mappingConeSquareMap
