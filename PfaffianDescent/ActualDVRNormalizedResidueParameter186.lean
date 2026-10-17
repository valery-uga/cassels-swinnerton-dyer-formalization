import PfaffianDescent.ActualKaehlerResidueBasisParameter186
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! SOURCE ONLY / UNVERIFIED. A derived normalized residue differential
forces a genuine DVR uniformizer. This local algebra helper preserves the
literal IsLocalRing.residue; it makes no global trace assertion. -/
noncomputable section
namespace PfaffianDescent
open IsLocalRing KaehlerDifferential
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma dvr_residueDerivation_normalizedParameter186
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra k R] [Algebra k (ResidueField R)] [IsScalarTower k R (ResidueField R)]
    (d : Derivation k R (ResidueField R)) (t : R)
    (ht : residue R t = 0) (hd : d t = 1) :
    maximalIdeal R = Ideal.span ({t} : Set R) := by
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible R
  have htmem : t ∈ maximalIdeal R := (residue_eq_zero_iff t).mp ht
  rw [hpi.maximalIdeal_eq] at htmem
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp htmem
  have hpi0 : residue R pi = 0 := (residue_eq_zero_iff pi).mpr
    (hpi.maximalIdeal_eq.symm ▸ Ideal.mem_span_singleton_self pi)
  have hbunit : IsUnit b := by
    apply (residue_ne_zero_iff_isUnit b).mp
    intro hb0
    have hdtzero : d (pi * b) = 0 := by
      rw [d.leibniz]
      change residue R pi * d b + residue R b * d pi = 0
      rw [hpi0, hb0, zero_mul, zero_mul, add_zero]
    exact zero_ne_one (hdtzero.symm.trans ((congrArg d hb).symm.trans hd))
  calc
    maximalIdeal R = Ideal.span ({pi} : Set R) := hpi.maximalIdeal_eq
    _ = Ideal.span ({pi * b} : Set R) :=
      (Ideal.span_singleton_mul_right_unit hbunit pi).symm
    _ = Ideal.span ({t} : Set R) := congrArg (fun z : R => Ideal.span ({z} : Set R)) hb.symm

/-- The normalization and the maximal-ideal generator are both derived
from the original basis and the literal separable residue map. -/
theorem dvrKaehlerResidueBasis_exists_normalizedUniformizer186
    {k R : Type u} [Field k] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra k R] [Algebra k (ResidueField R)] [IsScalarTower k R (ResidueField R)]
    [Algebra.IsSeparable k (ResidueField R)]
    (b : Module.Basis Unit R (KaehlerDifferential k R)) :
    ∃ t : R, residue R t = 0 ∧ maximalIdeal R = Ideal.span ({t} : Set R) ∧
      (1 ⊗ₜ[R] KaehlerDifferential.D k R t :
        (ResidueField R) ⊗[R] KaehlerDifferential k R) = 1 ⊗ₜ[R] b () := by
  let F := ResidueField R
  let q := actualKaehlerResidueBasisCoordinate186 (F := F) b
  have hq : Function.Bijective q := actualKaehlerResidueBasisCoordinate_bijective186 b
  obtain ⟨t, ht, hd⟩ := actualKaehlerLine_exists_residueIdeal_derivative_one
    (residue_surjective : Function.Surjective (algebraMap R F)) q hq.2
  have ht' : residue R t = 0 := ht
  let d := actualKaehlerLineDerivation (k := k) (R := R) (L := ResidueField R) q
  have hd' : d t = 1 := hd
  have hspan : maximalIdeal R = Ideal.span ({t} : Set R) := by
    obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible R
    have htmem : t ∈ maximalIdeal R := (residue_eq_zero_iff t).mp ht'
    rw [hpi.maximalIdeal_eq] at htmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp htmem
    have hpi0 : residue R pi = 0 := (residue_eq_zero_iff pi).mpr
      (hpi.maximalIdeal_eq.symm ▸ Ideal.mem_span_singleton_self pi)
    have hcunit : IsUnit c := by
      apply (residue_ne_zero_iff_isUnit c).mp
      intro hc0
      have hdtzero : d (pi * c) = 0 := by
        have hLeibniz := @Derivation.leibniz' k R (ResidueField R)
          _ _ _ _
          (@Algebra.toModule R (ResidueField R) _ _ inferInstance)
          (@Algebra.toModule k (ResidueField R) _ _ inferInstance)
          d pi c
        change d (pi * c) = residue R pi * d c + residue R c * d pi at hLeibniz
        rw [hpi0, hc0, zero_mul, zero_mul, add_zero] at hLeibniz
        exact hLeibniz
      exact zero_ne_one (hdtzero.symm.trans ((congrArg d hc).symm.trans hd'))
    calc
      maximalIdeal R = Ideal.span ({pi} : Set R) := hpi.maximalIdeal_eq
      _ = Ideal.span ({pi * c} : Set R) :=
        (Ideal.span_singleton_mul_right_unit hcunit pi).symm
      _ = Ideal.span ({t} : Set R) :=
        congrArg (fun z : R => Ideal.span ({z} : Set R)) hc.symm
  refine ⟨t, ht', hspan, hq.1 ?_⟩
  exact hd.trans (actualKaehlerResidueBasisCoordinate_basisVector186 b).symm

end PfaffianDescent
