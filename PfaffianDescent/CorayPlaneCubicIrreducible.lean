import Mathlib.Algebra.MvPolynomial.PDeriv
import PfaffianDescent.CorayPlaneHomogeneousCommonZero
import PfaffianDescent.TopHomogeneousProduct
import AllCharacteristics.HomogeneousSpecialization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! SOURCE ONLY / UNVERIFIED150. Native Fin3 irreducibility from actual
normalized nonsingularity. Positive-degree factors have a genuine common
nonzero zero by the THREE-variable height argument, then are normalized at a
nonzero coordinate. The original generic-plane caller supplies the pointwise
nonsingularity internally from149, not as a final integrality premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
universe u

/-- Two positive-degree factors force a singular normalized point of their
product, contradicting the displayed normalized nonsingularity criterion. -/
theorem plane_false_of_homogeneous_factorization_and_normalized_nonsingular
    {K : Type u} [Field K] [IsAlgClosed K]
    (q a b : MvPolynomial (Fin 3) K) {m n : ℕ}
    (hfactor : q = a * b)
    (ha : a.IsHomogeneous m) (hb : b.IsHomogeneous n)
    (hm : 0 < m) (hn : 0 < n)
    (hregular : ∀ (y : Fin 3 → K) (j : Fin 3), y j = 1 →
      q.eval₂ (RingHom.id K) y = 0 →
      ∃ i : Fin 3, (pderiv i q).eval₂ (RingHom.id K) y ≠ 0) : False := by
  classical
  obtain ⟨x, hx, hax, hbx⟩ :=
    plane_exists_nonzero_common_zero_of_homogeneous_pos a b ha hb hm hn
  obtain ⟨j, hxj⟩ : ∃ j : Fin 3, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  let c : K := (x j)⁻¹
  let y : Fin 3 → K := c • x
  have hyj : y j = 1 := by
    simpa only [y, c, Pi.smul_apply, smul_eq_mul] using inv_mul_cancel₀ hxj
  have hax' : a.eval₂ (RingHom.id K) x = 0 := by
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, RingHom.id_apply] using hax
  have hbx' : b.eval₂ (RingHom.id K) x = 0 := by
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, RingHom.id_apply] using hbx
  have hay : a.eval₂ (RingHom.id K) y = 0 := by
    rw [show y = c • x from rfl, AllCharacteristics.eval₂_homogeneous_smul a ha, hax', mul_zero]
  have hby : b.eval₂ (RingHom.id K) y = 0 := by
    rw [show y = c • x from rfl, AllCharacteristics.eval₂_homogeneous_smul b hb, hbx', mul_zero]
  have hqy : q.eval₂ (RingHom.id K) y = 0 := by
    rw [hfactor, eval₂_mul, hay, zero_mul]
  have hdy (i : Fin 3) : (pderiv i q).eval₂ (RingHom.id K) y = 0 := by
    rw [hfactor, pderiv_mul, eval₂_add, eval₂_mul, eval₂_mul, hay, hby]
    simp
  obtain ⟨i, hi⟩ := hregular y j hyj hqy
  exact hi (hdy i)

/-- A nonzero plane cubic nonsingular at every normalized geometric point is
irreducible. This criterion is used only after its actual pointwise premise
has been internally constructed from the original smooth cubic. -/
theorem planeCubic_irreducible_of_normalizedPoints_algClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    (hregular : ∀ (y : Fin 3 → K) (j : Fin 3), y j = 1 →
      q.eval₂ (RingHom.id K) y = 0 →
      ∃ i : Fin 3, (pderiv i q).eval₂ (RingHom.id K) y ≠ 0) :
    Irreducible q := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · exact homogeneous_not_isUnit_of_pos_degree_of_eval_zero hq (by norm_num)
  · intro a b hfactor
    by_contra hunit
    push Not at hunit
    have ha0 : a ≠ 0 := by
      intro ha
      apply hq0
      rw [hfactor, ha, zero_mul]
    have hb0 : b ≠ 0 := by
      intro hb
      apply hq0
      rw [hfactor, hb, mul_zero]
    obtain ⟨ha, hb⟩ :=
      homogeneous_factor_of_homogeneous_product ha0 hb0 (hfactor ▸ hq)
    have hapos : 0 < a.totalDegree := by
      by_contra hnot
      have hzero : a.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hunit.1
      exact isUnit_of_homogeneous_zero (hzero ▸ ha) ha0
    have hbpos : 0 < b.totalDegree := by
      by_contra hnot
      have hzero : b.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
      apply hunit.2
      exact isUnit_of_homogeneous_zero (hzero ▸ hb) hb0
    exact plane_false_of_homogeneous_factorization_and_normalized_nonsingular
      q a b hfactor ha hb hapos hbpos hregular

/-- Every-extension normalized nonsingularity constructs irreducibility over
ANY coefficient field. The algebraic-closure step and reflection of homogeneous
unit factors are actual native polynomial constructions. -/
theorem planeCubic_irreducible_of_normalizedFieldPoints
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    (hpoint : ∀ (M : Type u) [Field M] [Algebra K M]
      (y : Fin 3 → M) (j : Fin 3), y j = 1 →
      q.eval₂ (algebraMap K M) y = 0 →
      ∃ i : Fin 3, (pderiv i q).eval₂ (algebraMap K M) y ≠ 0) :
    Irreducible q := by
  let L : Type u := AlgebraicClosure K
  letI : Field L := inferInstanceAs (Field (AlgebraicClosure K))
  letI : Algebra K L := inferInstanceAs (Algebra K (AlgebraicClosure K))
  letI : IsAlgClosed L := inferInstanceAs (IsAlgClosed (AlgebraicClosure K))
  have hmapinj : Function.Injective (MvPolynomial.map (algebraMap K L) :
      MvPolynomial (Fin 3) K → MvPolynomial (Fin 3) L) :=
    MvPolynomial.map_injective (algebraMap K L) (FaithfulSMul.algebraMap_injective K L)
  have hqmap0 : q.map (algebraMap K L) ≠ 0 := by
    intro h
    apply hq0
    exact hmapinj (by simpa using h)
  have hregularL : ∀ (y : Fin 3 → L) (j : Fin 3), y j = 1 →
      (q.map (algebraMap K L)).eval₂ (RingHom.id L) y = 0 →
      ∃ i : Fin 3, (pderiv i (q.map (algebraMap K L))).eval₂ (RingHom.id L) y ≠ 0 := by
    intro y j hyj hqy
    have hqy' : q.eval₂ (algebraMap K L) y = 0 := by
      simpa only [MvPolynomial.eval₂_map, RingHom.id_comp] using hqy
    obtain ⟨i, hi⟩ := hpoint L y j hyj hqy'
    exact ⟨i, by simpa only [MvPolynomial.pderiv_map, MvPolynomial.eval₂_map,
      RingHom.id_comp] using hi⟩
  have hirr : Irreducible (q.map (algebraMap K L)) :=
    planeCubic_irreducible_of_normalizedPoints_algClosed _ (hq.map _) hqmap0 hregularL
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · exact homogeneous_not_isUnit_of_pos_degree_of_eval_zero hq (by norm_num)
  · intro a b hfactor
    have hmapfactor : q.map (algebraMap K L) =
        a.map (algebraMap K L) * b.map (algebraMap K L) := by
      rw [← map_mul, ← hfactor]
    by_contra hunit
    push Not at hunit
    have ha0 : a ≠ 0 := by
      intro ha
      apply hq0
      rw [hfactor, ha, zero_mul]
    have hb0 : b ≠ 0 := by
      intro hb
      apply hq0
      rw [hfactor, hb, mul_zero]
    obtain ⟨ha, hb⟩ := homogeneous_factor_of_homogeneous_product ha0 hb0 (hfactor ▸ hq)
    rcases hirr.isUnit_or_isUnit hmapfactor with haunit | hbunit
    · have hapos : 0 < a.totalDegree := by
        by_contra hnot
        have hzero : a.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
        apply hunit.1
        exact isUnit_of_homogeneous_zero (hzero ▸ ha) ha0
      exact (homogeneous_not_isUnit_of_pos_degree_of_eval_zero (ha.map _) hapos) haunit
    · have hbpos : 0 < b.totalDegree := by
        by_contra hnot
        have hzero : b.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
        apply hunit.2
        exact isUnit_of_homogeneous_zero (hzero ▸ hb) hb0
      exact (homogeneous_not_isUnit_of_pos_degree_of_eval_zero (hb.map _) hbpos) hbunit

end PfaffianDescent.Coray
