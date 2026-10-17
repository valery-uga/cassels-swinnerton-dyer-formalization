import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/- SOURCE ONLY / UNVERIFIED. The actual conormal exact sequence, with
principal kernel, identifies the differential relation internally. -/
noncomputable section
namespace PfaffianDescent
open TensorProduct KaehlerDifferential
open scoped TensorProduct
universe u v w
variable {k : Type u} {R : Type v} {A : Type w} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]

/-- This concerns the genuine canonical map on Kähler differentials; no
exactness or differential-kernel certificate is an input. -/
theorem principalPresentation_kaehler_mapBaseChange_ker
    (h : Function.Surjective (algebraMap R A)) (F : R)
    (hker : RingHom.ker (algebraMap R A) = Ideal.span ({F} : Set R)) :
    LinearMap.ker (mapBaseChange k R A) =
      Submodule.span A ({(1 : A) ⊗ₜ[R] D k R F} : Set (A ⊗[R] Ω[R⁄k])) := by
  have hF : algebraMap R A F = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton F)
  apply le_antisymm
  · intro y hy
    have hy' : y ∈ LinearMap.range (kerCotangentToTensor k R A) := by
      rw [range_kerCotangentToTensor k R A h]
      exact hy
    obtain ⟨z, hz⟩ := hy'
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ z
    have ha : a.val ∈ Ideal.span ({F} : Set R) := by
      rw [← hker]
      exact a.property
    obtain ⟨c, hval⟩ := dvd_def.mp (Ideal.mem_span_singleton.mp ha)
    rw [← hz, kerCotangentToTensor_toCotangent, hval,
      (D k R).leibniz, TensorProduct.tmul_add,
      ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
    simp only [Algebra.smul_def, mul_one, hF, TensorProduct.zero_tmul, zero_add]
    exact Submodule.mem_span_singleton.mpr ⟨algebraMap R A c, by
      simpa only [smul_eq_mul, mul_one] using
        (TensorProduct.smul_tmul' (algebraMap R A c) (1 : A) (D k R F))⟩
  · apply Submodule.span_le.mpr
    intro y hy
    have hy' : y = (1 : A) ⊗ₜ[R] D k R F := Set.mem_singleton_iff.mp hy
    subst y
    change mapBaseChange k R A ((1 : A) ⊗ₜ[R] D k R F) = 0
    have hm : mapBaseChange k R A ((1 : A) ⊗ₜ[R] D k R F) =
        (1 : A) • D k A (algebraMap R A F) :=
      (mapBaseChange_tmul k R A (1 : A) (D k R F)).trans
        (congrArg (fun w => (1 : A) • w) (map_D k k R A F))
    exact hm.trans (by rw [hF, map_zero, smul_zero])

/-- The actual differential module is the quotient by the single actual
relation differential. Surjectivity is derived from the conormal sequence. -/
def principalPresentationKaehlerQuotientEquiv
    (h : Function.Surjective (algebraMap R A)) (F : R)
    (hker : RingHom.ker (algebraMap R A) = Ideal.span ({F} : Set R)) :
    ((A ⊗[R] Ω[R⁄k]) ⧸
      Submodule.span A ({(1 : A) ⊗ₜ[R] D k R F} : Set (A ⊗[R] Ω[R⁄k]))) ≃ₗ[A]
      Ω[A⁄k] :=
  (Submodule.quotEquivOfEq _ _
    (principalPresentation_kaehler_mapBaseChange_ker (k := k) h F hker).symm) ≪≫ₗ
    (mapBaseChange k R A).quotKerEquivOfSurjective
      (mapBaseChange_surjective k R A h)

@[simp] lemma principalPresentationKaehlerQuotientEquiv_mk
    (h : Function.Surjective (algebraMap R A)) (F : R)
    (hker : RingHom.ker (algebraMap R A) = Ideal.span ({F} : Set R))
    (a : A) (r : R) :
    principalPresentationKaehlerQuotientEquiv (k := k) h F hker
      (Submodule.Quotient.mk (a ⊗ₜ[R] D k R r)) = a • D k A (algebraMap R A r) := by
  simp [principalPresentationKaehlerQuotientEquiv, mapBaseChange_tmul, map_D]

end PfaffianDescent
