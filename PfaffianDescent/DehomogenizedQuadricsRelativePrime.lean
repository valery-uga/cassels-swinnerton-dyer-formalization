import Mathlib.Algebra.MvPolynomial.Polynomial
import AllCharacteristics.PolynomialCoordinateOne
import PfaffianDescent.AffinePointExt
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import PfaffianDescent.QuarticHomogeneousJets
import PfaffianDescent.FrameResolution

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial
open scoped BigOperators

universe u
variable {K : Type u} [Field K]

/-- Homogenize an affine polynomial to a prescribed total degree in the chart `X₀ = 1`. -/
noncomputable def homogenizeAtZero (n : ℕ) (p : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K :=
  ∑ d ∈ Finset.range (n + 1), X 0 ^ (n - d) * MvPolynomial.rename Fin.succ
    (homogeneousComponent d p)

lemma homogenizeAtZero_isHomogeneous (n : ℕ) (p : MvPolynomial (Fin 3) K) :
    (homogenizeAtZero n p).IsHomogeneous n := by
  unfold homogenizeAtZero
  apply IsHomogeneous.sum
  intro d hd
  have hd' : d ≤ n := by
    simp only [Finset.mem_range] at hd
    omega
  have hX : ((X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^ (n - d)).IsHomogeneous (n - d) := by
    simpa using (isHomogeneous_X K (0 : Fin 4)).pow (n - d)
  have hp : (MvPolynomial.rename Fin.succ (homogeneousComponent d p)).IsHomogeneous d :=
    (homogeneousComponent_isHomogeneous d p).rename_isHomogeneous
  simpa [Nat.sub_add_cancel hd'] using hX.mul hp

lemma dehomogenizeAtZero_homogenizeAtZero (n : ℕ) (p : MvPolynomial (Fin 3) K)
    (hp : p.totalDegree ≤ n) :
    dehomogenizeAtZero (homogenizeAtZero n p) = p := by
  rw [homogenizeAtZero]
  simp only [map_sum, map_mul, map_pow, dehomogenizeAtZero_rename_succ]
  simp [dehomogenizeAtZero]
  exact homogeneousComponent_sum_of_bound p (n + 1) (by omega)

lemma dehomogenizeAtZero_eq_finSuccEval (Q : MvPolynomial (Fin 4) K) :
    dehomogenizeAtZero Q = Polynomial.eval 1 (MvPolynomial.finSuccEquiv K 3 Q) := by
  have hmap : (dehomogenizeAtZero (k := K)).toRingHom =
      (Polynomial.evalRingHom (1 : MvPolynomial (Fin 3) K)).comp
        (MvPolynomial.finSuccEquiv K 3).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dehomogenizeAtZero, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [dehomogenizeAtZero, MvPolynomial.finSuccEquiv_apply]
      · change dehomogenizeAtZero (X k.succ) =
          Polynomial.eval 1 (MvPolynomial.finSuccEquiv K 3 (X k.succ))
        rw [MvPolynomial.finSuccEquiv_X_succ]
        simp [dehomogenizeAtZero]
        have hvec : (![X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) K) =
            fun t => X t := by
          funext t
          fin_cases t <;> rfl
        rw [hvec]
  exact DFunLike.congr_fun hmap Q

lemma totalDegree_dehomogenizeAtZero_le (Q : MvPolynomial (Fin 4) K) :
    (dehomogenizeAtZero Q).totalDegree ≤ Q.totalDegree := by
  rw [dehomogenizeAtZero_eq_finSuccEval]
  let P := MvPolynomial.finSuccEquiv K 3 Q
  change (Polynomial.eval 1 P).totalDegree ≤ Q.totalDegree
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [one_pow, mul_one]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  by_cases hzero : P.coeff i = 0
  · rw [hzero]
    exact Nat.zero_le _
  · exact (Nat.le_add_right _ _).trans
      (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le Q i hzero)

end QuarticNet
end PfaffianDescent

namespace PfaffianDescent.QuarticNet

universe u
variable {K : Type u} [Field K]
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.HomogeneousProjective
open MvPolynomial

noncomputable def finThreeSuccComplement : Fin 3 ≃ {i : Fin 4 // i ≠ 0} :=
  Equiv.ofBijective (fun k => ⟨k.succ, Fin.succ_ne_zero k⟩) ⟨by
    intro a b hab
    exact Fin.succ_inj.mp (congrArg Subtype.val hab), by
    intro i
    refine ⟨i.val.pred i.property, ?_⟩
    apply Subtype.ext
    exact Fin.succ_pred i.val i.property⟩

lemma finThreeSuccComplement_apply (k : Fin 3) :
    finThreeSuccComplement k = ⟨k.succ, Fin.succ_ne_zero k⟩ := rfl

lemma dehomogenizeAtZero_eq_rename_coordinateOneEvaluation (Q : MvPolynomial (Fin 4) K) :
    dehomogenizeAtZero Q =
      (MvPolynomial.renameEquiv K finThreeSuccComplement.symm)
        (coordinateOneEvaluation 0 Q) := by
  have hmap : (dehomogenizeAtZero (k := K)).toRingHom =
      (MvPolynomial.renameEquiv K finThreeSuccComplement.symm).toRingEquiv.toRingHom.comp
        (coordinateOneEvaluation 0).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dehomogenizeAtZero, coordinateOneEvaluation]
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [dehomogenizeAtZero, coordinateOneEvaluation]
      · change dehomogenizeAtZero (X k.succ) =
          (MvPolynomial.renameEquiv K finThreeSuccComplement.symm)
            (coordinateOneEvaluation 0 (X k.succ))
        simp [dehomogenizeAtZero, coordinateOneEvaluation]
        have hk : (⟨k.succ, Fin.succ_ne_zero k⟩ : {i : Fin 4 // i ≠ 0}) =
            finThreeSuccComplement k := rfl
        rw [show (⟨k.succ, _⟩ : {i : Fin 4 // i ≠ 0}) =
          finThreeSuccComplement k by exact hk]
        rw [finThreeSuccComplement.symm_apply_apply]
        fin_cases k <;> rfl
  exact DFunLike.congr_fun hmap Q

lemma dehomogenizeAtZero_ne_zero_of_homogeneous
    {Q : MvPolynomial (Fin 4) K} {n : ℕ} (hQ : Q.IsHomogeneous n) (hQ0 : Q ≠ 0) :
    dehomogenizeAtZero Q ≠ 0 := by
  intro hzero
  apply coordinateOneEvaluation_ne_zero_of_homogeneous hQ hQ0 0
  apply (MvPolynomial.renameEquiv K finThreeSuccComplement.symm).injective
  rw [← dehomogenizeAtZero_eq_rename_coordinateOneEvaluation]
  exact hzero

lemma dehomogenizeAtZero_injective_on_homogeneous
    {Q Q' : MvPolynomial (Fin 4) K} {n : ℕ}
    (hQ : Q.IsHomogeneous n) (hQ' : Q'.IsHomogeneous n)
    (heq : dehomogenizeAtZero Q = dehomogenizeAtZero Q') : Q = Q' := by
  apply sub_eq_zero.mp
  by_contra hzero
  apply dehomogenizeAtZero_ne_zero_of_homogeneous (hQ.sub hQ') hzero
  rw [map_sub, heq, sub_self]

lemma homogenizeAtZero_dehomogenizeAtZero_of_homogeneous
    {Q : MvPolynomial (Fin 4) K} {n : ℕ} (hQ : Q.IsHomogeneous n) :
    homogenizeAtZero n (dehomogenizeAtZero Q) = Q := by
  apply dehomogenizeAtZero_injective_on_homogeneous
  · exact homogenizeAtZero_isHomogeneous n _
  · exact hQ
  rw [dehomogenizeAtZero_homogenizeAtZero _ _
    ((totalDegree_dehomogenizeAtZero_le Q).trans hQ.totalDegree_le)]


lemma homogenizeAtZero_raise (m n : ℕ) (p : MvPolynomial (Fin 3) K)
    (hp : p.totalDegree ≤ m) (hmn : m ≤ n) :
    homogenizeAtZero n p =
      (X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^ (n - m) * homogenizeAtZero m p := by
  apply dehomogenizeAtZero_injective_on_homogeneous
  · exact homogenizeAtZero_isHomogeneous _ _
  · have hX : ((X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^ (n - m)).IsHomogeneous
        (n - m) := by
      simpa using (isHomogeneous_X K (0 : Fin 4)).pow (n - m)
    simpa [Nat.sub_add_cancel hmn] using hX.mul (homogenizeAtZero_isHomogeneous m p)
  rw [map_mul,
    dehomogenizeAtZero_homogenizeAtZero _ _ (hp.trans hmn),
    dehomogenizeAtZero_homogenizeAtZero _ _ hp]
  simp [dehomogenizeAtZero]

lemma homogenizeAtZero_mul (m n : ℕ) (p q : MvPolynomial (Fin 3) K)
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) :
    homogenizeAtZero (m + n) (p * q) =
      homogenizeAtZero m p * homogenizeAtZero n q := by
  apply dehomogenizeAtZero_injective_on_homogeneous
  · exact homogenizeAtZero_isHomogeneous _ _
  · exact (homogenizeAtZero_isHomogeneous m p).mul (homogenizeAtZero_isHomogeneous n q)
  rw [map_mul,
    dehomogenizeAtZero_homogenizeAtZero _ _ hp,
    dehomogenizeAtZero_homogenizeAtZero _ _ hq,
    dehomogenizeAtZero_homogenizeAtZero _ _]
  exact (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq)


theorem dehomogenizeAtZero_isRelPrime_of_homogeneous_isRelPrime
    {Q₁ Q₂ : MvPolynomial (Fin 4) K} {n₁ n₂ : ℕ}
    (hQ₁ : Q₁.IsHomogeneous n₁) (hQ₂ : Q₂.IsHomogeneous n₂) (hn₁ : 0 < n₁)
    (hQ₁0 : Q₁ ≠ 0)
    (hrel : IsRelPrime Q₁ Q₂) :
    IsRelPrime (dehomogenizeAtZero Q₁) (dehomogenizeAtZero Q₂) := by
  intro d hd₁ hd₂
  obtain ⟨a, ha⟩ := hd₁
  obtain ⟨b, hb⟩ := hd₂
  have hq₁0 : dehomogenizeAtZero Q₁ ≠ 0 :=
    dehomogenizeAtZero_ne_zero_of_homogeneous hQ₁ hQ₁0
  have hda0 : d * a ≠ 0 := by simpa [ha] using hq₁0
  have hd0 : d ≠ 0 := left_ne_zero_of_mul hda0
  have ha0 : a ≠ 0 := right_ne_zero_of_mul hda0
  have hQ₂0 : Q₂ ≠ 0 := by
    intro hzero
    apply homogeneous_not_isUnit_of_pos_degree_of_eval_zero hQ₁ hn₁
    rw [hzero] at hrel
    exact isRelPrime_zero_right.mp hrel
  have hq₂0 : dehomogenizeAtZero Q₂ ≠ 0 :=
    dehomogenizeAtZero_ne_zero_of_homogeneous hQ₂ hQ₂0
  have hdb0 : d * b ≠ 0 := by simpa [hb] using hq₂0
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hdb0
  have hdeg : d.totalDegree + a.totalDegree ≤ n₁ := by
    rw [← totalDegree_mul_of_isDomain hd0 ha0, ← ha]
    exact (totalDegree_dehomogenizeAtZero_le Q₁).trans hQ₁.totalDegree_le
  let D := homogenizeAtZero d.totalDegree d
  let A := homogenizeAtZero a.totalDegree a
  let B := homogenizeAtZero b.totalDegree b
  have hQ₁fac : Q₁ = (X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^
      (n₁ - (d.totalDegree + a.totalDegree)) * (D * A) := by
    rw [← homogenizeAtZero_dehomogenizeAtZero_of_homogeneous hQ₁, ha,
      homogenizeAtZero_raise (d.totalDegree + a.totalDegree) n₁ (d * a)
        (MvPolynomial.totalDegree_mul d a) hdeg,
      homogenizeAtZero_mul d.totalDegree a.totalDegree d a le_rfl le_rfl]
  have hQ₂fac : Q₂ = (X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^
      (n₂ - (d.totalDegree + b.totalDegree)) * (D * B) := by
    rw [← homogenizeAtZero_dehomogenizeAtZero_of_homogeneous hQ₂, hb,
      homogenizeAtZero_raise (d.totalDegree + b.totalDegree) n₂ (d * b)
        (MvPolynomial.totalDegree_mul d b) (by
          rw [← totalDegree_mul_of_isDomain hd0 hb0, ← hb]
          exact (totalDegree_dehomogenizeAtZero_le Q₂).trans hQ₂.totalDegree_le),
      homogenizeAtZero_mul d.totalDegree b.totalDegree d b le_rfl le_rfl]
  have hD₁ : D ∣ Q₁ := by
    refine ⟨(X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^
      (n₁ - (d.totalDegree + a.totalDegree)) * A, ?_⟩
    rw [hQ₁fac]
    ring
  have hD₂ : D ∣ Q₂ := by
    refine ⟨(X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^
      (n₂ - (d.totalDegree + b.totalDegree)) * B, ?_⟩
    rw [hQ₂fac]
    ring
  have hDunit : IsUnit D := hrel hD₁ hD₂
  have hdunit := IsUnit.map (dehomogenizeAtZero (k := K)).toMonoidHom hDunit
  simpa [D, dehomogenizeAtZero_homogenizeAtZero _ _ le_rfl] using hdunit

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

noncomputable def coordinateComplementEquiv (j : Fin 4) :
    {i : Fin 4 // i ≠ j} ≃ Fin 3 :=
  ((Equiv.swap (0 : Fin 4) j).subtypeEquiv (fun i => by
    have hswap : Equiv.swap (0 : Fin 4) j j = 0 := Equiv.swap_apply_right _ _
    constructor
    · intro hi hzero
      apply hi
      apply (Equiv.swap (0 : Fin 4) j).injective
      exact hzero.trans hswap.symm
    · intro hi hij
      apply hi
      rw [hij]
      exact hswap)).trans
      finThreeSuccComplement.symm

lemma coordinateComplementEquiv_apply (j : Fin 4) (i : {i : Fin 4 // i ≠ j}) :
    coordinateComplementEquiv j i = finThreeSuccComplement.symm
      ⟨Equiv.swap (0 : Fin 4) j i.val, by
        intro h
        apply i.property
        have hswap : Equiv.swap (0 : Fin 4) j j = 0 := Equiv.swap_apply_right _ _
        rw [← (Equiv.swap (0 : Fin 4) j).apply_eq_iff_eq]
        rw [h, hswap]⟩ := rfl

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

universe u
variable {K : Type u} [Field K]
open MvPolynomial
open AllCharacteristics.HomogeneousProjective

lemma dehomogenizeAtZero_rename_swap_eq_rename_coordinateOneEvaluation
    (j : Fin 4) (Q : MvPolynomial (Fin 4) K) :
    dehomogenizeAtZero (MvPolynomial.rename (Equiv.swap (0 : Fin 4) j) Q) =
      (MvPolynomial.renameEquiv K (coordinateComplementEquiv j))
        (coordinateOneEvaluation j Q) := by
  have hmap : (dehomogenizeAtZero (k := K)).toRingHom.comp
      (MvPolynomial.rename (Equiv.swap (0 : Fin 4) j)).toRingHom =
      (MvPolynomial.renameEquiv K (coordinateComplementEquiv j)).toRingEquiv.toRingHom.comp
        (coordinateOneEvaluation j).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dehomogenizeAtZero, coordinateOneEvaluation]
    · intro i
      change dehomogenizeAtZero (MvPolynomial.rename (Equiv.swap (0 : Fin 4) j) (X i)) =
        (MvPolynomial.renameEquiv K (coordinateComplementEquiv j))
          (coordinateOneEvaluation j (X i))
      rw [MvPolynomial.rename_X]
      by_cases hij : i = j
      · subst i
        simp [dehomogenizeAtZero, coordinateOneEvaluation,
          MvPolynomial.renameEquiv_apply, Equiv.swap_apply_right]
      · have hswap0 : Equiv.swap (0 : Fin 4) j i ≠ 0 := by
          intro hzero
          apply hij
          apply (Equiv.swap (0 : Fin 4) j).injective
          exact hzero.trans (Equiv.swap_apply_right _ _).symm
        let k : Fin 3 := (Equiv.swap (0 : Fin 4) j i).pred hswap0
        have hsucc : k.succ = Equiv.swap (0 : Fin 4) j i :=
          Fin.succ_pred _ hswap0
        have hE : coordinateComplementEquiv j ⟨i, hij⟩ = k := by
          rw [coordinateComplementEquiv_apply]
          apply finThreeSuccComplement.injective
          rw [finThreeSuccComplement.apply_symm_apply]
          apply Subtype.ext
          exact hsucc.symm
        simp only [coordinateOneEvaluation, aeval_X, dif_neg hij,
          MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
        rw [hE]
        rw [← hsucc]
        simp [dehomogenizeAtZero]
        have hvec : (![X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) K) =
            fun t => X t := by
          funext t
          fin_cases t <;> rfl
        rw [hvec]
  exact DFunLike.congr_fun hmap Q

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

universe u
variable {K : Type u} [Field K]
open MvPolynomial

lemma isRelPrime_rename_equiv (e : Fin 4 ≃ Fin 4)
    {Q₁ Q₂ : MvPolynomial (Fin 4) K} (hrel : IsRelPrime Q₁ Q₂) :
    IsRelPrime (MvPolynomial.rename e Q₁) (MvPolynomial.rename e Q₂) := by
  intro d hd₁ hd₂
  have hd₁' := map_dvd (MvPolynomial.rename e.symm) hd₁
  have hd₂' := map_dvd (MvPolynomial.rename e.symm) hd₂
  rw [MvPolynomial.rename_rename] at hd₁' hd₂'
  have hcomp : (e.symm : Fin 4 → Fin 4) ∘ e = id := by
    funext x
    exact e.symm_apply_apply x
  rw [hcomp, MvPolynomial.rename_id] at hd₁' hd₂'
  have hu : IsUnit (MvPolynomial.rename e.symm d) := hrel hd₁' hd₂'
  have hu' := IsUnit.map (MvPolynomial.renameEquiv K e).toMonoidHom hu
  simpa [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename] using hu' 

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

universe u
variable {K : Type u} [Field K]
open MvPolynomial
open AllCharacteristics.HomogeneousProjective

theorem coordinateOneEvaluation_isRelPrime_of_homogeneous_isRelPrime
    {Q₁ Q₂ : MvPolynomial (Fin 4) K} {n₁ n₂ : ℕ}
    (hQ₁ : Q₁.IsHomogeneous n₁) (hQ₂ : Q₂.IsHomogeneous n₂) (hn₁ : 0 < n₁)
    (hQ₁0 : Q₁ ≠ 0)
    (hrel : IsRelPrime Q₁ Q₂) (j : Fin 4) :
    IsRelPrime (coordinateOneEvaluation j Q₁) (coordinateOneEvaluation j Q₂) := by
  let e : Fin 4 ≃ Fin 4 := Equiv.swap 0 j
  have hQ₁' : (MvPolynomial.rename e Q₁).IsHomogeneous n₁ := hQ₁.rename_isHomogeneous
  have hQ₂' : (MvPolynomial.rename e Q₂).IsHomogeneous n₂ := hQ₂.rename_isHomogeneous
  have hQ₁0' : MvPolynomial.rename e Q₁ ≠ 0 :=
    (MvPolynomial.renameEquiv K e).injective.ne_iff.mpr hQ₁0
  have hrel' : IsRelPrime (MvPolynomial.rename e Q₁) (MvPolynomial.rename e Q₂) :=
    isRelPrime_rename_equiv e hrel
  have hstandard := dehomogenizeAtZero_isRelPrime_of_homogeneous_isRelPrime
    hQ₁' hQ₂' hn₁ hQ₁0' hrel'
  apply IsRelPrime.of_map (MvPolynomial.renameEquiv K (coordinateComplementEquiv j))
  rw [← dehomogenizeAtZero_rename_swap_eq_rename_coordinateOneEvaluation j Q₁,
    ← dehomogenizeAtZero_rename_swap_eq_rename_coordinateOneEvaluation j Q₂]
  exact hstandard

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet

open MvPolynomial
open scoped BigOperators

universe u
variable {K : Type u} [Field K]

lemma homogenizeAtZero_add (n : ℕ) (p q : MvPolynomial (Fin 3) K) :
    homogenizeAtZero n (p + q) = homogenizeAtZero n p + homogenizeAtZero n q := by
  unfold homogenizeAtZero
  simp only [map_add]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

/-- A homogeneous relation in the normalized `X₀ = 1` chart lifts to a
multiple of the original homogeneous relation. -/
lemma power_mul_mem_span_of_dehomogenizeAtZero_mem_span
    {p q F : MvPolynomial (Fin 4) K} {n₁ n₂ m : ℕ}
    (hp : p.IsHomogeneous n₁) (hq : q.IsHomogeneous n₂) (hF : F.IsHomogeneous m)
    (hmem : dehomogenizeAtZero F ∈ Ideal.span
      ({dehomogenizeAtZero p, dehomogenizeAtZero q} : Set (MvPolynomial (Fin 3) K))) :
    ∃ N : ℕ, (X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^ N * F ∈
      Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
  let N := max m (max (n₁ + a.totalDegree) (n₂ + b.totalDegree))
  have hmN : m ≤ N := le_max_left _ _
  have haN : a.totalDegree ≤ N - n₁ := by
    dsimp [N]
    omega
  have hbN : b.totalDegree ≤ N - n₂ := by
    dsimp [N]
    omega
  have hn₁N : n₁ ≤ N := by
    dsimp [N]
    omega
  have hn₂N : n₂ ≤ N := by
    dsimp [N]
    omega
  have hFp : homogenizeAtZero N (dehomogenizeAtZero F) =
      (X (0 : Fin 4) : MvPolynomial (Fin 4) K) ^ (N-m) * F := by
    rw [homogenizeAtZero_raise m N (dehomogenizeAtZero F)
      ((totalDegree_dehomogenizeAtZero_le F).trans hF.totalDegree_le) hmN,
      homogenizeAtZero_dehomogenizeAtZero_of_homogeneous hF]
  have hpp : homogenizeAtZero n₁ (dehomogenizeAtZero p) = p :=
    homogenizeAtZero_dehomogenizeAtZero_of_homogeneous hp
  have hqq : homogenizeAtZero n₂ (dehomogenizeAtZero q) = q :=
    homogenizeAtZero_dehomogenizeAtZero_of_homogeneous hq
  have hpa : homogenizeAtZero N (a * dehomogenizeAtZero p) =
      homogenizeAtZero (N-n₁) a * p := by
    calc
      homogenizeAtZero N (a * dehomogenizeAtZero p) =
          homogenizeAtZero ((N-n₁)+n₁) (a * dehomogenizeAtZero p) := by
            rw [Nat.sub_add_cancel hn₁N]
      _ = homogenizeAtZero (N-n₁) a * homogenizeAtZero n₁ (dehomogenizeAtZero p) :=
        homogenizeAtZero_mul (N-n₁) n₁ a (dehomogenizeAtZero p) haN
          ((totalDegree_dehomogenizeAtZero_le p).trans hp.totalDegree_le)
      _ = homogenizeAtZero (N-n₁) a * p := by rw [hpp]
  have hqb : homogenizeAtZero N (b * dehomogenizeAtZero q) =
      homogenizeAtZero (N-n₂) b * q := by
    calc
      homogenizeAtZero N (b * dehomogenizeAtZero q) =
          homogenizeAtZero ((N-n₂)+n₂) (b * dehomogenizeAtZero q) := by
            rw [Nat.sub_add_cancel hn₂N]
      _ = homogenizeAtZero (N-n₂) b * homogenizeAtZero n₂ (dehomogenizeAtZero q) :=
        homogenizeAtZero_mul (N-n₂) n₂ b (dehomogenizeAtZero q) hbN
          ((totalDegree_dehomogenizeAtZero_le q).trans hq.totalDegree_le)
      _ = homogenizeAtZero (N-n₂) b * q := by rw [hqq]
  have hhom := congrArg (homogenizeAtZero N) hab
  rw [homogenizeAtZero_add, hpa, hqb, hFp] at hhom
  refine ⟨N-m, ?_⟩
  exact Ideal.mem_span_pair.mpr ⟨homogenizeAtZero (N-n₁) a,
    homogenizeAtZero (N-n₂) b, hhom⟩

end PfaffianDescent.QuarticNet
