import PfaffianDescent.AlgebraVectorIdeal

namespace PfaffianDescent
open MvPolynomial
section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

noncomputable def algebraLineDilation (u : A) : MvPolynomial Unit A →ₐ[A] MvPolynomial Unit A :=
  MvPolynomial.aeval (fun _ => C u * X ())

@[simp] lemma algebraLineDilation_C (u a : A) : algebraLineDilation u (C a) = C a := by
  simp [algebraLineDilation]

@[simp] lemma algebraLineDilation_X (u : A) (i : Unit) :
    algebraLineDilation u (X i) = C u * X () := aeval_X _ _

lemma algebraLineDilation_comp (u v : A) :
    (algebraLineDilation u).comp (algebraLineDilation v) = algebraLineDilation (u*v) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, algebraLineDilation_X, map_mul, algebraLineDilation_C]
  ring

lemma algebraLineDilation_one : algebraLineDilation (1 : A) = AlgHom.id A _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i
  simp only [algebraLineDilation_X, map_one, one_mul, AlgHom.id_apply]

lemma algebraLineDilation_injective (u : Aˣ) : Function.Injective (algebraLineDilation (u : A)) := by
  intro p q h
  have he := congrArg (algebraLineDilation (↑u⁻¹ : A)) h
  have hc : (algebraLineDilation (↑u⁻¹ : A)).comp (algebraLineDilation (u : A)) = AlgHom.id A _ := by
    rw [algebraLineDilation_comp, Units.inv_mul, algebraLineDilation_one]
  have hp := AlgHom.congr_fun hc p
  have hq := AlgHom.congr_fun hc q
  exact hp.symm.trans (he.trans hq)

lemma algebraLineDilation_line (u : A) (p : Vec A 4) :
    (algebraLineDilation u).toRingHom.comp (algebraLineHom (K := K) p).toRingHom =
      (algebraLineHom (K := K) (u • p)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      algebraLineHom_C, algebraLineDilation_C]
  · intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      algebraLineHom_X, map_mul, algebraLineDilation_C, algebraLineDilation_X, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- Multiplying all homogeneous coordinates by an algebra unit preserves their ideal. -/
theorem algebraVectorIdeal_unit_smul (u : Aˣ) (p : Vec A 4) :
    algebraVectorIdeal (K := K) ((u : A) • p) = algebraVectorIdeal (K := K) p := by
  ext f
  change algebraLineHom ((u : A) • p) f = 0 ↔ algebraLineHom p f = 0
  have h := DFunLike.congr_fun (algebraLineDilation_line (K := K) (u : A) p) f
  change algebraLineDilation (u : A) (algebraLineHom p f) = algebraLineHom ((u : A) • p) f at h
  rw [← h]
  exact (algebraLineDilation_injective u).eq_iff' (map_zero _)

end
end PfaffianDescent
