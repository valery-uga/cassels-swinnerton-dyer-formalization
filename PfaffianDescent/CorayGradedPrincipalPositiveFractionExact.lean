import PfaffianDescent.CorayGradedPrincipalLocalExact
import PfaffianDescent.VoisinHypersurfacePositiveTwist

/-! SOURCE ONLY. Principal homogeneous quotient exactness on positive
fraction modules. The target may be nonreduced and need not be a domain. -/
noncomputable section
namespace PfaffianDescent.Coray
open scoped DirectSum Pointwise
open AlgebraicGeometry CategoryTheory DirectSum SetLike Localization
open ProjectiveNegativeTwist
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
variable (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A positive homogeneous fraction killed after localization has a
homogeneous annihilating multiplier outside the source prime. The numerator
and denominator may have different degrees. Nilpotents are retained. -/
theorem gradedPrincipal_positiveFraction_homogeneous_annihilator
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    (P : Ideal A) [P.IsPrime] (Q : HomogeneousIdeal ℬ) [Q.toIdeal.IsPrime]
    (hPQ : P = Ideal.comap f.toRingHom Q.toIdeal)
    {aDegree bDegree : ℕ} (a : 𝒜 aDegree) (b : 𝒜 bDegree)
    (hb : (b : A) ∈ P.primeCompl)
    (hzero : Localization.localRingHom P Q.toIdeal f.toRingHom hPQ
      (Localization.mk (a : A) ⟨(b : A), hb⟩) = 0) :
    ∃ (j : ℕ) (t : 𝒜 j), (t : A) ∈ P.primeCompl ∧ f ((t : A) * a) = 0 := by
  classical
  rw [Localization.localRingHom_mk, Localization.mk_eq_mk'] at hzero
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hzero
  change (c : B) * f a = 0 at hc
  have hex : ∃ j, (DirectSum.decompose ℬ (c : B) j : B) ∉ Q.toIdeal := by
    by_contra hn
    apply c.2
    apply Q.isHomogeneous.mem_iff.mpr
    intro j
    by_contra hj
    exact hn ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  obtain ⟨v, hv, hfv⟩ := gradedSurjective_homogeneous_lift f hf j
    (DirectSum.decompose ℬ (c : B) j) (DirectSum.decompose ℬ (c : B) j).2
  let t : 𝒜 j := ⟨v, hv⟩
  have ht : (t : A) ∈ P.primeCompl := by
    intro htP
    apply hj
    rw [hPQ] at htP
    change f v ∈ Q.toIdeal at htP
    rwa [hfv] at htP
  have hmul : (DirectSum.decompose ℬ (c : B) j : B) * f a = 0 := by
    calc
      _ = (DirectSum.decompose ℬ ((c : B) * f a) (j + aDegree) : B) :=
        (DirectSum.coe_decompose_mul_add_of_right_mem ℬ (f.map_mem a.property)).symm
      _ = 0 := by rw [hc]; simp
  refine ⟨j, t, ht, ?_⟩
  rw [map_mul]
  change f v * f a = 0
  rw [hfv]
  exact hmul

/-- Actual positive multiplication followed by actual positive homogeneous
restriction is exact for a surjective graded map with principal homogeneous
kernel. There is no target domain, reducedness, or local-exactness premise. -/
theorem gradedPrincipal_positiveFraction_exact
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {d : ℕ} (s : 𝒜 d)
    (hker : RingHom.ker f.toRingHom = Ideal.span ({(s : A)} : Set A))
    (m : ℕ) (y : ProjectiveSpectrum ℬ) :
    let h := gradedSurjective_irrelevant_le f hf
    let x := ProjectiveSpectrum.comap f h y
    Function.Exact (positiveMulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal s m)
      (gradedRingHomPositiveTwistStalkMap 𝒜 ℬ f h (m + d) y) := by
  dsimp only
  let h := gradedSurjective_irrelevant_le f hf
  let x := ProjectiveSpectrum.comap f h y
  letI : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let P := x.asHomogeneousIdeal.toIdeal
  let Q := y.asHomogeneousIdeal.toIdeal
  have hPQ : P = Ideal.comap f.toRingHom Q := rfl
  let F := positiveMulHomogeneousStalk 𝒜 P s m
  let G := gradedRingHomPositiveTwistStalkMap 𝒜 ℬ f h (m + d) y
  change Function.Exact F G
  intro z
  constructor
  · intro hz
    rcases z.property with hz0 | ⟨i, a, b, hb, hzrep⟩
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      change (F 0).val = z.val
      rw [map_zero, hz0]
      rfl
    · have hzmap : Localization.localRingHom P Q f.toRingHom hPQ
          (Localization.mk (a : A) ⟨(b : A), hb⟩) = 0 := by
        have hval := congrArg Subtype.val hz
        change Localization.localRingHom P Q f.toRingHom hPQ z.val = 0 at hval
        rwa [hzrep] at hval
      obtain ⟨j, t, ht, hta⟩ := gradedPrincipal_positiveFraction_homogeneous_annihilator
        𝒜 ℬ f hf P y.asHomogeneousIdeal hPQ a b hb hzmap
      let a' : 𝒜 (j + (m + d + i)) :=
        ⟨(t : A) * a, SetLike.mul_mem_graded t.property a.property⟩
      let b' : 𝒜 (j + i) :=
        ⟨(t : A) * b, SetLike.mul_mem_graded t.property b.property⟩
      have hb' : (b' : A) ∈ P.primeCompl := P.primeCompl.mul_mem ht hb
      have ha' : (a' : A) ∈ Ideal.span ({(s : A)} : Set A) := by
        rw [← hker]
        exact hta
      have hdi : d ≤ j + (m + d + i) := by omega
      obtain ⟨v, hv⟩ := (gradedPrincipal_homogeneous_factor 𝒜 s a' ha').1 hdi
      have hdeg : j + (m + d + i) - d = m + (j + i) := by omega
      let v' : 𝒜 (m + (j + i)) := ⟨v, by rw [← hdeg]; exact v.property⟩
      have hv' : (s : A) * v' = a' := hv
      have hclear : Localization.mk (a' : A) ⟨(b' : A), hb'⟩ = z.val := by
        rw [hzrep]
        simp only [Localization.mk_eq_mk']
        rw [IsLocalization.mk'_eq_iff_eq]
        congr 1
        dsimp only [a', b']
        ring
      let w : positiveStalkSubmodule 𝒜 P m :=
        ⟨Localization.mk (v' : A) ⟨(b' : A), hb'⟩,
          Or.inr ⟨j + i, v', b', hb', rfl⟩⟩
      refine ⟨w, ?_⟩
      apply Subtype.ext
      change algebraMap A (Localization P.primeCompl) (s : A) *
        Localization.mk (v' : A) ⟨(b' : A), hb'⟩ = z.val
      rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, hv']
      simpa only [one_mul] using hclear
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    change Localization.localRingHom P Q f.toRingHom hPQ
      (algebraMap A (Localization P.primeCompl) (s : A) * w.val) = 0
    rw [map_mul]
    have hs0 : f (s : A) = 0 := by
      change (s : A) ∈ RingHom.ker f.toRingHom
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hsmap : Localization.localRingHom P Q f.toRingHom hPQ
        (algebraMap A (Localization P.primeCompl) (s : A)) = 0 := by
      rw [← Localization.mk_one_eq_algebraMap]
      simp only [Localization.localRingHom_mk,
        GradedRingHom.toRingHom_eq_toRingHom, GradedRingHom.coe_toRingHom,
        hs0, Localization.mk_zero]
    rw [hsmap, zero_mul]

end PfaffianDescent.Coray
end
