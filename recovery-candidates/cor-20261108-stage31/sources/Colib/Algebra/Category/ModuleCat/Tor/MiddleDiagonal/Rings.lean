/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Literal middle-diagonal coordinate rings

For arbitrary commutative `k`-algebras `A`, `B`, `C`, the ambient ring is
`(A ⊗[k] B) ⊗[k] (B ⊗[k] C)` and the triple ring is literally
`(A ⊗[k] B) ⊗[k] C`. The quotient map multiplies the two middle `B`
coordinates. The map from the ambient ring to the tensor square of the triple
ring composes with the full diagonal to this actual quotient map.

Over a field the two adjacent inclusions and their tensor product are flat.
The quotient map itself is only shown surjective, never assumed flat.

This supplies actual ring maps for the native middle-diagonal Tor comparison.
Unlike the balanced tensor presentation in `motivic_source_a6805c4`,
`AlgebraicGeometry/Diagonal/AffineMiddleScalars.lean`, the triple ring here is
the requested literal three-factor tensor ring, not an identified synonym.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

universe u

namespace Algebra.TensorProduct.MiddleDiagonal

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra k B] [Algebra k C]

/-- The four-factor ring, retaining both middle coordinates. -/
abbrev ambientRing := (A ⊗[k] B) ⊗[k] (B ⊗[k] C)

/-- The literal three-factor ring. -/
abbrev tripleRing := (A ⊗[k] B) ⊗[k] C

/-- The first adjacent coordinate inclusion. -/
def leftMap : A ⊗[k] B →ₐ[k] tripleRing k A B C := includeLeft

/-- The second adjacent coordinate inclusion. -/
def rightMap : B ⊗[k] C →ₐ[k] tripleRing k A B C :=
  Algebra.TensorProduct.map (includeRight : B →ₐ[k] A ⊗[k] B) (AlgHom.id k C)

/-- The actual quotient map identifying the two middle coordinates. -/
def quotientMap : ambientRing k A B C →ₐ[k] tripleRing k A B C :=
  lift (leftMap k A B C) (rightMap k A B C) (fun _ _ => Commute.all _ _)

/-- The comparison to the full tensor square of the actual triple ring. -/
def fullDiagonalMap : ambientRing k A B C →ₐ[k]
    (tripleRing k A B C) ⊗[k] (tripleRing k A B C) :=
  Algebra.TensorProduct.map (leftMap k A B C) (rightMap k A B C)

/-- The literal middle-diagonal formula on pure tensors. -/
@[simp]
theorem quotientMap_tmul_tmul (a : A) (b b' : B) (c : C) :
    quotientMap k A B C ((a ⊗ₜ[k] b) ⊗ₜ[k] (b' ⊗ₜ[k] c)) =
      (a ⊗ₜ[k] (b * b')) ⊗ₜ[k] c := by
  simp [quotientMap, leftMap, rightMap, Algebra.TensorProduct.tmul_mul_tmul]

/-- The full diagonal after the comparison is exactly the middle-diagonal quotient. -/
theorem fullDiagonal_comp :
    (lmul' k (S := tripleRing k A B C)).comp (fullDiagonalMap k A B C) =
      quotientMap k A B C := by
  ext <;> simp [fullDiagonalMap, quotientMap]

/-- The middle-diagonal map is an actual ring quotient. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap k A B C) := by
  intro q
  induction q using TensorProduct.inductionOn with
  | tmul p c =>
    exact ⟨p ⊗ₜ[k] ((1 : B) ⊗ₜ[k] c), by
      simp [quotientMap, leftMap, rightMap, Algebra.TensorProduct.tmul_mul_tmul,
        ← Algebra.TensorProduct.one_def]⟩
  | add q q' hq hq' =>
    obtain ⟨p, rfl⟩ := hq
    obtain ⟨p', rfl⟩ := hq'
    exact ⟨p + p', map_add _ _ _⟩

/-- The outer `C` coordinate makes the first adjacent inclusion flat over every field. -/
theorem leftMap_flat : (leftMap k A B C).Flat := by
  change (algebraMap (A ⊗[k] B) ((A ⊗[k] B) ⊗[k] C)).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The outer `A` coordinate makes the second adjacent inclusion flat over every field. -/
theorem rightMap_flat : (rightMap k A B C).Flat := by
  have hbase : (algebraMap B (B ⊗[k] A)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hcomm : (Algebra.TensorProduct.comm k B A).toRingEquiv.toRingHom.Flat :=
    RingHom.Flat.of_bijective (Algebra.TensorProduct.comm k B A).bijective
  have hincl : (includeRight : B →ₐ[k] A ⊗[k] B).Flat := by
    convert hbase.comp hcomm using 1
    ext b
    simp
  exact hincl.tensorProductMap (RingHom.Flat.id (R := C))

/-- The ambient-to-full-diagonal comparison is flat; no support module is assumed flat. -/
theorem fullDiagonalMap_flat :
    RingHom.Flat (R := ambientRing k A B C)
      (S := tripleRing k A B C ⊗[k] tripleRing k A B C)
      (fullDiagonalMap k A B C).toRingHom :=
  (leftMap_flat k A B C).tensorProductMap (rightMap_flat k A B C)

end Algebra.TensorProduct.MiddleDiagonal
