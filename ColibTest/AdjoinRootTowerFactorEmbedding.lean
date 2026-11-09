module

import Colib.RingTheory.AdjoinRoot.TowerFactorEmbedding

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

variable {k : Type*} [Field k] (a p h : k[X])
  [Fact (Irreducible a)] [Fact (Irreducible p)] [Fact (Irreducible h)]
  (g : AdjoinRoot a →ₐ[k] AdjoinRoot p)
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "A" => AdjoinRoot a
local notation "E" => AdjoinRoot p
local notation "qP" => towerFactor a p g
local notation "qH" => towerFactor a h (f.comp g)
local notation "pA" => poly qP.1.2
local notation "hA" => poly qH.1.2
local notation "PA" => AdjoinRoot pA
local notation "HA" => AdjoinRoot hA

/-- The actual native factors retain the original divisibility witnesses. -/
example : pA ∣ p.map (algebraMap k A) := qP.2

example : hA ∣ h.map (algebraMap k A) := qH.2

/-- The ring homomorphism is literally the conjugate of the original field map. -/
example : towerFactorEmbeddingRingHom a p h g f =
    (towerFactorRingEquiv a h (f.comp g)).symm.toRingHom.comp
      (f.toRingHom.comp (towerFactorRingEquiv a p g).toRingHom) := rfl

/-- This is an actual algebra embedding over the original lower root field. -/
example : PA →ₐ[A] HA := towerFactorEmbeddingAlgHom a p h g f

example : Function.Injective (towerFactorEmbeddingAlgHom a p h g f) :=
  towerFactorEmbeddingAlgHom_injective a p h g f

example (x : A) : towerFactorEmbeddingAlgHom a p h g f (algebraMap A PA x) =
    algebraMap A HA x := (towerFactorEmbeddingAlgHom a p h g f).commutes x

example : (towerFactorEmbeddingAlgHom a p h g f).toRingHom =
    towerFactorEmbeddingRingHom a p h g f :=
  towerFactorEmbeddingAlgHom_toRingHom a p h g f

example (x : PA) :
    towerFactorRingEquiv a h (f.comp g) (towerFactorEmbeddingAlgHom a p h g f x) =
      f (towerFactorRingEquiv a p g x) :=
  towerFactorEmbeddingAlgHom_apply a p h g f x

example : (towerFactorRingEquiv a h (f.comp g)).toRingHom.comp
      (towerFactorEmbeddingAlgHom a p h g f).toRingHom =
    f.toRingHom.comp (towerFactorRingEquiv a p g).toRingHom :=
  towerFactorEmbeddingAlgHom_comp_towerFactorRingEquiv a p h g f

example (b : E) : towerFactorEmbeddingAlgHom a p h g f
      (AdjoinRoot.map (algebraMap k A) p pA qP.2 b) =
    AdjoinRoot.map (algebraMap k A) h hA qH.2 (f b) :=
  towerFactorEmbeddingAlgHom_map a p h g f b

example : (towerFactorEmbeddingAlgHom a p h g f).toRingHom.comp
      (AdjoinRoot.map (algebraMap k A) p pA qP.2) =
    (AdjoinRoot.map (algebraMap k A) h hA qH.2).comp f.toRingHom :=
  towerFactorEmbeddingAlgHom_comp_adjoinRootMap a p h g f

example : towerFactorEmbeddingAlgHom a p h g f (root pA) =
    AdjoinRoot.map (algebraMap k A) h hA qH.2 (f (root p)) :=
  towerFactorEmbeddingAlgHom_root a p h g f

example : towerFactorRingEquiv a h (f.comp g)
      (towerFactorEmbeddingAlgHom a p h g f (root pA)) = f (root p) :=
  towerFactorEmbeddingAlgHom_root_apply a p h g f

end
