module

import Colib.RingTheory.AdjoinRoot.TowerFactorAssoc

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

variable {k : Type*} [Field k] (a p h : k[X])
  [Fact (Irreducible a)] [Fact (Irreducible p)] [Fact (Irreducible h)]
  (g : AdjoinRoot a →ₐ[k] AdjoinRoot p)
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "A" => AdjoinRoot a
local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "qP" => towerFactor a p g
local notation "qH" => towerFactor a h (f.comp g)
local notation "pA" => poly qP.1.2
local notation "hA" => poly qH.1.2
local notation "PA" => AdjoinRoot pA
local notation "HA" => AdjoinRoot hA

local instance : Fact (Irreducible pA) := ⟨irreducible qP.1.2⟩
local instance : Fact (Irreducible hA) := ⟨irreducible qH.1.2⟩

local notation "fA" => towerFactorEmbeddingAlgHom a p h g f
local notation "qR" => towerFactor pA hA fA
local notation "qD" => towerFactor p h f
local notation "QR" => AdjoinRoot (poly qR.1.2)
local notation "QD" => AdjoinRoot (poly qD.1.2)

/-- The iterated factor is selected from the actual relative embedding. -/
example : poly qR.1.2 ∣ (hA).map (algebraMap A PA) := qR.2

example : poly qD.1.2 ∣ h.map (algebraMap k E) := qD.2

example : QR ≃+* QD := towerFactorAssocRingEquiv a p h g f

/-- The equivalence literally passes through the original top field. -/
example : towerFactorAssocRingEquiv a p h g f =
    ((towerFactorRingEquiv pA hA fA).trans
      (towerFactorRingEquiv a h (f.comp g))).trans (towerFactorRingEquiv p h f).symm := rfl

example (x : QR) :
    towerFactorRingEquiv p h f (towerFactorAssocRingEquiv a p h g f x) =
      towerFactorRingEquiv a h (f.comp g) (towerFactorRingEquiv pA hA fA x) :=
  towerFactorAssocRingEquiv_apply a p h g f x

example : (towerFactorRingEquiv p h f).toRingHom.comp
      (towerFactorAssocRingEquiv a p h g f).toRingHom =
    (towerFactorRingEquiv a h (f.comp g)).toRingHom.comp
      (towerFactorRingEquiv pA hA fA).toRingHom :=
  towerFactorAssocRingEquiv_comp_towerFactorRingEquiv a p h g f

example (x : PA) : towerFactorAssocRingEquiv a p h g f (algebraMap PA QR x) =
    algebraMap E QD (towerFactorRingEquiv a p g x) :=
  towerFactorAssocRingEquiv_algebraMap a p h g f x

example : (towerFactorAssocRingEquiv a p h g f).toRingHom.comp (algebraMap PA QR) =
    (algebraMap E QD).comp (towerFactorRingEquiv a p g).toRingHom :=
  towerFactorAssocRingEquiv_comp_algebraMap a p h g f

/-- The original-base algebra structures are the existing iterated quotient structures. -/
example : QR ≃ₐ[k] QD := towerFactorAssocAlgEquiv a p h g f

example (c : k) : towerFactorAssocAlgEquiv a p h g f (algebraMap k QR c) =
    algebraMap k QD c := (towerFactorAssocAlgEquiv a p h g f).commutes c

example : (towerFactorAssocAlgEquiv a p h g f).toRingEquiv =
    towerFactorAssocRingEquiv a p h g f := towerFactorAssocAlgEquiv_toRingEquiv a p h g f

example : towerFactorAssocRingEquiv a p h g f (root (poly qR.1.2)) =
    root (poly qD.1.2) := towerFactorAssocRingEquiv_root a p h g f

example (b : HA) : towerFactorAssocRingEquiv a p h g f
      (AdjoinRoot.map (algebraMap A PA) hA (poly qR.1.2) qR.2 b) =
    AdjoinRoot.map (algebraMap k E) h (poly qD.1.2) qD.2
      (towerFactorRingEquiv a h (f.comp g) b) :=
  towerFactorAssocRingEquiv_map a p h g f b

example : (towerFactorAssocRingEquiv a p h g f).toRingHom.comp
      (AdjoinRoot.map (algebraMap A PA) hA (poly qR.1.2) qR.2) =
    (AdjoinRoot.map (algebraMap k E) h (poly qD.1.2) qD.2).comp
      (towerFactorRingEquiv a h (f.comp g)).toRingHom :=
  towerFactorAssocRingEquiv_comp_adjoinRootMap a p h g f

example (b : H) : towerFactorAssocRingEquiv a p h g f
      (AdjoinRoot.map (algebraMap A PA) hA (poly qR.1.2) qR.2
        (AdjoinRoot.map (algebraMap k A) h hA qH.2 b)) =
    AdjoinRoot.map (algebraMap k E) h (poly qD.1.2) qD.2 b :=
  towerFactorAssocRingEquiv_map_map a p h g f b

example : (towerFactorAssocRingEquiv a p h g f).toRingHom.comp
      ((AdjoinRoot.map (algebraMap A PA) hA (poly qR.1.2) qR.2).comp
        (AdjoinRoot.map (algebraMap k A) h hA qH.2)) =
    AdjoinRoot.map (algebraMap k E) h (poly qD.1.2) qD.2 :=
  towerFactorAssocRingEquiv_comp_adjoinRootMap_comp_adjoinRootMap a p h g f

/-- The compared monic polynomials are equal, rather than merely associated. -/
example : (poly qR.1.2).map (towerFactorRingEquiv a p g).toRingHom = poly qD.1.2 :=
  towerFactorAssoc_poly_map a p h g f

/-- The comparison's underlying map is the native coefficient-change quotient map itself. -/
example : (towerFactorAssocRingEquiv a p h g f).toRingHom =
    AdjoinRoot.map (towerFactorRingEquiv a p g).toRingHom
      (poly qR.1.2) (poly qD.1.2) (by rw [towerFactorAssoc_poly_map]) :=
  towerFactorAssocRingEquiv_toRingHom a p h g f

/-- The inverse sends the original direct coefficient-factor image to the iterated image. -/
example (b : H) : (towerFactorAssocRingEquiv a p h g f).symm
      (AdjoinRoot.map (algebraMap k E) h (poly qD.1.2) qD.2 b) =
    AdjoinRoot.map (algebraMap A PA) hA (poly qR.1.2) qR.2
      (AdjoinRoot.map (algebraMap k A) h hA qH.2 b) := by
  rw [← towerFactorAssocRingEquiv_map_map a p h g f b]
  exact (towerFactorAssocRingEquiv a p h g f).symm_apply_apply _

end
