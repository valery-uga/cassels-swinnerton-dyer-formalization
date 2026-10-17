import PfaffianDescent.FrameProjectivePoints

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def vectorLineVariable (v : Fin n → K) (i : Fin n) : MvPolynomial Unit K :=
  C (v i) * X ()

noncomputable def vectorLineHom (v : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial Unit K :=
  MvPolynomial.aeval (vectorLineVariable v)

@[simp] lemma vectorLineHom_X (v : Fin n → K) (i : Fin n) :
    vectorLineHom v (X i) = C (v i) * X () := MvPolynomial.aeval_X _ _

noncomputable def vectorLineGradedHom (v : Fin n → K) :
    homogeneousSubmodule (Fin n) K →+*ᵍ homogeneousSubmodule Unit K where
  __ := (vectorLineHom v).toRingHom
  map_mem := by
    intro d f hf
    change (MvPolynomial.aeval (vectorLineVariable v) f).IsHomogeneous d
    have h := hf.aeval (vectorLineVariable v) (fun i => isHomogeneous_C_mul_X (v i) ())
    simpa only [one_mul] using h

noncomputable def vectorLineIdeal (v : Fin n → K) :
    HomogeneousIdeal (homogeneousSubmodule (Fin n) K) :=
  (⊥ : HomogeneousIdeal (homogeneousSubmodule Unit K)).comap (vectorLineGradedHom v)

lemma mem_vectorLineIdeal (v : Fin n → K) (f : MvPolynomial (Fin n) K) :
    f ∈ vectorLineIdeal v ↔ vectorLineHom v f = 0 := Iff.rfl

instance vectorLineIdeal_prime (v : Fin n → K) : (vectorLineIdeal v).toIdeal.IsPrime := by
  change (Ideal.comap (vectorLineHom v).toRingHom (⊥ : Ideal (MvPolynomial Unit K))).IsPrime
  infer_instance

lemma vectorLineIdeal_not_irrelevant (v : Fin n → K) (hv : v ≠ 0) :
    ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin n) K) ≤ vectorLineIdeal v := by
  intro h
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv (funext hn)
  have hm : (X i : MvPolynomial (Fin n) K) ∈ vectorLineIdeal v :=
    h (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1) (isHomogeneous_X K i))
  have he := (mem_vectorLineIdeal v (X i)).mp hm
  rw [vectorLineHom_X] at he
  exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hi) (MvPolynomial.X_ne_zero ()) he

/-- A nonzero homogeneous vector gives an actual point of projective space. -/
noncomputable def projectiveVectorPoint (v : Fin n → K) (hv : v ≠ 0) :
    ProjectiveSpectrum (homogeneousSubmodule (Fin n) K) where
  asHomogeneousIdeal := vectorLineIdeal v
  isPrime := inferInstance
  not_irrelevant_le := vectorLineIdeal_not_irrelevant v hv

/-- Restricting a form to the line through `v` and evaluating at `1` recovers its
ordinary evaluation at `v`. -/
lemma vectorLineHom_eval_one (v : Fin n → K) (f : MvPolynomial (Fin n) K) :
    MvPolynomial.eval (fun _ : Unit => 1) (vectorLineHom v f) = MvPolynomial.eval v f := by
  change (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : Unit => 1))
      ((vectorLineHom v).toRingHom f) =
    (MvPolynomial.eval₂Hom (RingHom.id K) v) f
  have hcomp : (MvPolynomial.eval₂Hom (RingHom.id K) (fun _ : Unit => 1)).comp
      (vectorLineHom v).toRingHom = MvPolynomial.eval₂Hom (RingHom.id K) v := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp [vectorLineHom, vectorLineVariable]
  rw [← hcomp]
  rfl

lemma eval_zero_of_isHomogeneous_pos (q : MvPolynomial (Fin n) K) {d : ℕ}
    (hq : q.IsHomogeneous d) (hd : 0 < d) : MvPolynomial.eval (0 : Fin n → K) q = 0 := by
  rw [MvPolynomial.eval_zero]
  change MvPolynomial.coeff 0 q = 0
  apply hq.coeff_eq_zero
  exact Nat.ne_of_lt hd

theorem exists_vector_eval_ne_zero_of_homogeneous [Infinite K]
    (q : MvPolynomial (Fin n) K) {d : ℕ}
    (hq : q.IsHomogeneous d) (hq0 : q ≠ 0) :
    ∃ v : Fin n → K, MvPolynomial.eval v q ≠ 0 := by
  by_contra h
  push Not at h
  exact hq0 (hq.eq_zero_of_forall_eval_eq_zero h)

/-- A nonzero positive-degree homogeneous form over an infinite field omits a projective point. -/
theorem exists_projectiveVectorPoint_not_mem_of_homogeneous [Infinite K]
    (q : MvPolynomial (Fin n) K) {d : ℕ}
    (hq : q.IsHomogeneous d) (hd : 0 < d) (hq0 : q ≠ 0) :
    ∃ x : ProjectiveSpectrum (homogeneousSubmodule (Fin n) K),
      q ∉ x.asHomogeneousIdeal.toIdeal := by
  obtain ⟨v, hv⟩ := exists_vector_eval_ne_zero_of_homogeneous q hq hq0
  have hv0 : v ≠ 0 := by
    intro hvzero
    subst v
    apply hv
    exact eval_zero_of_isHomogeneous_pos q hq hd
  refine ⟨projectiveVectorPoint v hv0, ?_⟩
  change q ∉ vectorLineIdeal v
  rw [mem_vectorLineIdeal]
  intro hline
  apply hv
  rw [← vectorLineHom_eval_one]
  rw [hline]
  rfl

/-- A nonzero positive-degree homogeneous member of an ideal omits an actual
projective point which therefore does not contain that ideal. -/
theorem exists_projectiveVectorPoint_not_contains_of_nonzero_homogeneous_mem
    [Infinite K] (I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    (q : MvPolynomial (Fin n) K) {d : ℕ}
    (hqI : q ∈ I.toIdeal) (hq : q.IsHomogeneous d) (hd : 0 < d) (hq0 : q ≠ 0) :
    ∃ x : ProjectiveSpectrum (homogeneousSubmodule (Fin n) K),
      ¬ I ≤ x.asHomogeneousIdeal := by
  obtain ⟨x, hx⟩ := exists_projectiveVectorPoint_not_mem_of_homogeneous q hq hd hq0
  refine ⟨x, ?_⟩
  intro hI
  exact hx (hI hqI)

/-- A homogeneous ideal containing a nonzero positive-degree form has proper
projective zero locus over an infinite field. -/
theorem projective_zeroLocus_ne_univ_of_nonzero_homogeneous_mem
    [Infinite K] (I : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    (q : MvPolynomial (Fin n) K) {d : ℕ}
    (hqI : q ∈ I.toIdeal) (hq : q.IsHomogeneous d) (hd : 0 < d) (hq0 : q ≠ 0) :
    ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin n) K)
      (I : Set (MvPolynomial (Fin n) K)) ≠ Set.univ := by
  obtain ⟨x, hx⟩ :=
    exists_projectiveVectorPoint_not_contains_of_nonzero_homogeneous_mem I q hqI hq hd hq0
  intro htop
  apply hx
  exact (ProjectiveSpectrum.mem_zeroLocus (homogeneousSubmodule (Fin n) K) x
    (I : Set (MvPolynomial (Fin n) K))).mp (by rw [htop]; exact Set.mem_univ x)

noncomputable def lineDilation (c : K) : MvPolynomial Unit K →ₐ[K] MvPolynomial Unit K :=
  MvPolynomial.aeval (fun _ => C c * X ())

@[simp] lemma lineDilation_X (c : K) (i : Unit) : lineDilation c (X i) = C c * X () :=
  MvPolynomial.aeval_X _ _

lemma lineDilation_comp (c d : K) : (lineDilation c).comp (lineDilation d) = lineDilation (c*d) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, lineDilation_X, lineDilation_X]
  change MvPolynomial.aeval (fun _ : Unit => C c * X ()) (C d * X ()) = C (c*d) * X ()
  simp only [map_mul, aeval_C, MvPolynomial.algebraMap_eq, aeval_X]
  ring

lemma lineDilation_one : lineDilation (1 : K) = AlgHom.id K (MvPolynomial Unit K) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i
  change MvPolynomial.aeval (fun _ : Unit => C (1 : K) * X ()) (X ()) = X ()
  rw [aeval_X, map_one, one_mul]

noncomputable def lineDilationEquiv (c : K) (hc : c ≠ 0) :
    MvPolynomial Unit K ≃ₐ[K] MvPolynomial Unit K :=
  AlgEquiv.ofAlgHom (lineDilation c) (lineDilation c⁻¹)
    (by rw [lineDilation_comp, mul_inv_cancel₀ hc, lineDilation_one])
    (by rw [lineDilation_comp, inv_mul_cancel₀ hc, lineDilation_one])

lemma vectorLineHom_smul (c : K) (v : Fin n → K) :
    (lineDilation c).comp (vectorLineHom v) = vectorLineHom (c • v) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, vectorLineHom_X, vectorLineHom_X]
  change MvPolynomial.aeval (fun _ : Unit => C c * X ()) (C (v i) * X ()) = C (c*v i) * X ()
  simp only [map_mul, aeval_C, MvPolynomial.algebraMap_eq, aeval_X]
  ring

/-- Nonzero rescaling does not change the actual homogeneous prime ideal of a point. -/
theorem vectorLineIdeal_smul (c : K) (hc : c ≠ 0) (v : Fin n → K) :
    vectorLineIdeal (c • v) = vectorLineIdeal v := by
  apply HomogeneousIdeal.ext
  ext f
  change vectorLineHom (c • v) f = 0 ↔ vectorLineHom v f = 0
  have he := AlgHom.congr_fun (vectorLineHom_smul c v) f
  rw [← he]
  exact map_eq_zero_iff (lineDilationEquiv c hc) (lineDilationEquiv c hc).injective

/-- Restriction to a projective line commutes with a permutation of the
homogeneous variables. -/
lemma vectorLineHom_rename (e : Fin n ≃ Fin n) (v : Fin n → K) :
    (vectorLineHom v).comp (MvPolynomial.rename e) =
      vectorLineHom (fun i ↦ v (e i)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [vectorLineHom_X, MvPolynomial.rename_X]

/-- Renaming homogeneous variables transports a projective point ideal by
the inverse permutation of its coordinate vector. -/
lemma vectorLineIdeal_renameEquiv (e : Fin n ≃ Fin n) (v : Fin n → K) :
    (vectorLineIdeal v).toIdeal.map (MvPolynomial.renameEquiv K e).toRingHom =
      (vectorLineIdeal (fun k ↦ v (e.symm k))).toIdeal := by
  let w : Fin n → K := fun k ↦ v (e.symm k)
  let E := MvPolynomial.renameEquiv K e
  ext f
  change f ∈ Ideal.map E (vectorLineIdeal v).toIdeal ↔ _
  rw [Ideal.mem_map_of_equiv E]
  constructor
  · rintro ⟨g, hg, rfl⟩
    change vectorLineHom w (MvPolynomial.rename e g) = 0
    have he := AlgHom.congr_fun (vectorLineHom_rename e w) g
    rw [AlgHom.comp_apply] at he
    rw [he]
    change vectorLineHom v g = 0 at hg
    simpa [w] using hg
  · intro hf
    refine ⟨E.symm f, ?_, E.apply_symm_apply f⟩
    change vectorLineHom v (E.symm f) = 0
    have he := AlgHom.congr_fun (vectorLineHom_rename e w) (E.symm f)
    rw [AlgHom.comp_apply] at he
    have hw : (fun i ↦ w (e i)) = v := by
      funext i
      simp [w]
    rw [hw] at he
    rw [← he]
    change vectorLineHom w (E (E.symm f)) = 0
    rw [E.apply_symm_apply]
    exact hf

end
end PfaffianDescent
