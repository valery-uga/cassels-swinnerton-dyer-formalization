import PfaffianDescent.TwoGeneratorKoszul
import PfaffianDescent.HomogeneousProjection
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]

abbrev PlaneHomogeneous (K : Type*) [Field K] (d : ℕ) := homogeneousSubmodule (Fin 3) K d

/-- Degree `d+5` part of the first Koszul map for a conic and a cubic. -/
noncomputable def conicCubicGradedFirst (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3) (d : ℕ) :
    PlaneHomogeneous K d →ₗ[K] PlaneHomogeneous K (d+3) × PlaneHomogeneous K (d+2) where
  toFun c :=
    (⟨-f*c.val, by
      change (-f*c.val).IsHomogeneous (d+3)
      rw [Nat.add_comm d 3]
      exact hf.neg.mul c.property⟩,
     ⟨q*c.val, by
      change (q*c.val).IsHomogeneous (d+2)
      rw [Nat.add_comm d 2]
      exact hq.mul c.property⟩)
  map_add' a b := by apply Prod.ext <;> apply Subtype.ext <;> simp [mul_add]
  map_smul' r a := by apply Prod.ext <;> apply Subtype.ext <;> simp [mul_smul_comm]

/-- Degree `d+5` part of the map to the ideal of the intersection. -/
noncomputable def conicCubicGradedLast (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3) (d : ℕ) :
    PlaneHomogeneous K (d+3) × PlaneHomogeneous K (d+2) →ₗ[K] PlaneHomogeneous K (d+5) where
  toFun v := ⟨q*v.1.val + f*v.2.val, by
    change (q*v.1.val + f*v.2.val).IsHomogeneous (d+5)
    apply IsHomogeneous.add
    · convert hq.mul v.1.property using 1 <;> omega
    · convert hf.mul v.2.property using 1 <;> omega⟩
  map_add' a b := by
    apply Subtype.ext
    change q*(a.1.val+b.1.val) + f*(a.2.val+b.2.val) =
      (q*a.1.val + f*a.2.val) + (q*b.1.val + f*b.2.val)
    ring
  map_smul' r a := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, RingHom.id_apply,
      mul_smul_comm, smul_add]

lemma conicCubicGradedFirst_injective (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3) (hq0 : q ≠ 0) (d : ℕ) :
    Function.Injective (conicCubicGradedFirst q f hq hf d) := by
  intro a b he
  have h := congrArg (fun v : PlaneHomogeneous K (d+3) × PlaneHomogeneous K (d+2) => v.2.val) he
  exact Subtype.ext (mul_left_cancel₀ hq0 h)

/-- The conic/cubic Koszul complex is exact in each degree at least five. -/
theorem conicCubicGraded_exact (q f : MvPolynomial (Fin 3) K)
    (hq : q.IsHomogeneous 2) (hf : f.IsHomogeneous 3)
    (hq0 : q ≠ 0) (hrel : IsRelPrime q f) (d : ℕ) :
    LinearMap.range (conicCubicGradedFirst q f hq hf d) =
      LinearMap.ker (conicCubicGradedLast q f hq hf d) := by
  apply le_antisymm
  · rintro v ⟨c, rfl⟩
    apply Subtype.ext
    change q*(-f*c.val) + f*(q*c.val) = 0
    ring
  · intro v hv
    have hv' : (v.1.val, v.2.val) ∈ LinearMap.ker (twoGeneratorLast q f) := by
      exact congrArg Subtype.val hv
    rw [← twoGenerator_exact hq0 hrel] at hv'
    obtain ⟨c, hc⟩ := hv'
    have hc1 : -f*c = v.1.val := congrArg Prod.fst hc
    have hc2 : q*c = v.2.val := congrArg Prod.snd hc
    have hch : c.IsHomogeneous d := homogeneous_of_mul_right hq hq0 (by
      rw [mul_comm, hc2]
      exact v.2.property)
    exact ⟨⟨c, hch⟩, Prod.ext (Subtype.ext hc1) (Subtype.ext hc2)⟩

end
end PfaffianDescent
