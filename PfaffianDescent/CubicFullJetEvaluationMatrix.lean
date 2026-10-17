import PfaffianDescent.CubicVectorConfigurationWitness
import PfaffianDescent.HomogeneousMonomialEvaluationMinor

/-!
The literal monomial matrix for eleven values and six surface derivatives.
Its entries are polynomial values and directional partial derivatives, so
they can be transported to universal coordinate rings. Full first-jet
interpolation constructs an actual invertible seventeen-column minor.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.UniversalHomogeneous

universe u
set_option backward.isDefEq.respectTransparency false

abbrev CubicFullJetCondition := (Fin 11) ⊕ (Fin 3 × Fin 2)

noncomputable def homogeneousFullJetEvaluationMatrix
    {R : Type u} [CommRing R] (d : ℕ) (x : Fin 11 → Fin 4 → R)
    (v : Fin 3 → Fin 4 → Fin 2 → R) :
    Matrix CubicFullJetCondition (Monomials (Fin 4) d) R :=
  fun r m => match r with
    | Sum.inl i => (monomial m.1 (1 : R)).eval (x i)
    | Sum.inr it => ∑ j : Fin 4,
        (pderiv j (monomial m.1 (1 : R))).eval (x (it.1.castAdd 8)) * v it.1 j it.2

noncomputable def homogeneousFullJetEvaluationMinor
    {R : Type u} [CommRing R] {d : ℕ}
    (m : CubicFullJetCondition ↪ Monomials (Fin 4) d)
    (x : Fin 11 → Fin 4 → R) (v : Fin 3 → Fin 4 → Fin 2 → R) :
    Matrix CubicFullJetCondition CubicFullJetCondition R :=
  (homogeneousFullJetEvaluationMatrix d x v).submatrix id m

noncomputable def cubicElevenPointHermiteRestriction
    {K : Type u} [Field K] (x : Fin 11 → Fin 4 → K)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K) :
    homogeneousSubmodule (Fin 4) K 3 →ₗ[K] (CubicFullJetCondition → K) :=
  LinearMap.pi fun r => match r with
    | Sum.inl i => (aeval (x i)).toLinearMap.domRestrict _
    | Sum.inr it => (LinearMap.proj it.2).comp
        ((TrivSqZeroExt.sndHom K (Fin 2 → K)).comp
          ((aeval (J it.1)).toLinearMap.domRestrict _))

theorem cubicSurfaceFirstJet_snd_aeval
    {K : Type u} [Field K] (J : Fin 4 → CubicSurfaceFirstJet K)
    (q : MvPolynomial (Fin 4) K) (t : Fin 2) :
    (aeval J q).snd t = ∑ j : Fin 4,
      aeval (fun k => (J k).fst) (pderiv j q) * (J j).snd t := by
  have hJ : (fun j => TrivSqZeroExt.inl (J j).fst + TrivSqZeroExt.inr (J j).snd) = J := by
    funext j
    apply TrivSqZeroExt.ext <;> simp
  have h := cubicClosedPointSerreSurfaceJets_taylor
    (fun j => (J j).fst) (fun j => (J j).snd) q
  rw [hJ] at h
  have hs := congrArg (fun z : CubicSurfaceFirstJet K => z.snd t) h
  simpa [Finset.sum_apply, smul_eq_mul] using hs

theorem cubicElevenPointHermiteRestriction_surjective_of_fullJets
    {K : Type u} [Field K]
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J)) :
    Function.Surjective (cubicElevenPointHermiteRestriction x J) := by
  intro z
  obtain ⟨q, hq⟩ := hfull
    (fun i => TrivSqZeroExt.inl (z (Sum.inl (i.castAdd 8))) +
      TrivSqZeroExt.inr (fun t => z (Sum.inr (i, t))),
      fun i => z (Sum.inl (i.natAdd 3)))
  have hA := congrArg Prod.fst hq
  have hB := congrArg Prod.snd hq
  change (fun i => aeval (J i) q.1) =
    (fun i => TrivSqZeroExt.inl (z (Sum.inl (i.castAdd 8))) +
      TrivSqZeroExt.inr (fun t => z (Sum.inr (i, t)))) at hA
  change (fun i : Fin 8 => aeval (x (i.natAdd 3)) q.1) =
    (fun i : Fin 8 => z (Sum.inl (i.natAdd 3))) at hB
  refine ⟨q, ?_⟩
  funext r
  rcases r with i | ⟨i, t⟩
  · refine Fin.addCases (m := 3) (n := 8) ?_ ?_ i
    · intro j
      have h := congrArg TrivSqZeroExt.fst (congrFun hA j)
      rw [cubicSurfaceFirstJet_fst_aeval] at h
      simpa [cubicElevenPointHermiteRestriction, hresidue] using h
    · intro j
      exact congrFun hB j
  · have h := congrArg (fun w : CubicSurfaceFirstJet K => w.snd t) (congrFun hA i)
    simpa [cubicElevenPointHermiteRestriction] using h

theorem homogeneousFullJetEvaluationMatrix_entry_eq_restriction
    {K : Type u} [Field K]
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (r : CubicFullJetCondition) (m : Monomials (Fin 4) 3) :
    homogeneousFullJetEvaluationMatrix 3 x (fun i j => (J i j).snd) r m =
      cubicElevenPointHermiteRestriction x J
        ⟨monomial m.1 1, isHomogeneous_monomial 1 m.2⟩ r := by
  rcases r with i | ⟨i, t⟩
  · rfl
  · change (∑ j : Fin 4, aeval (x (i.castAdd 8)) (pderiv j (monomial m.1 1)) *
      (J i j).snd t) = (aeval (J i) (monomial m.1 1)).snd t
    rw [cubicSurfaceFirstJet_snd_aeval]
    simp_rw [hresidue]

theorem homogeneousFullJetEvaluationMatrix_surjective_of_fullJets
    {K : Type u} [Field K]
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J)) :
    Function.Surjective
      (Matrix.toLin' (homogeneousFullJetEvaluationMatrix 3 x (fun i j => (J i j).snd))) := by
  classical
  intro z
  obtain ⟨q, hq⟩ := cubicElevenPointHermiteRestriction_surjective_of_fullJets x J hresidue hfull z
  let b : Monomials (Fin 4) 3 → homogeneousSubmodule (Fin 4) K 3 :=
    fun m => ⟨monomial m.1 1, isHomogeneous_monomial 1 m.2⟩
  let c : Monomials (Fin 4) 3 → K := fun m => q.1.coeff m.1
  have hexp : ∑ m : Monomials (Fin 4) 3, c m • b m = q := by
    apply Subtype.ext
    simpa [b, c, MvPolynomial.smul_monomial] using sum_monomial_coeff_eq q.1 q.2
  refine ⟨c, ?_⟩
  funext r
  have h := congrFun (congrArg (cubicElevenPointHermiteRestriction x J) hexp) r
  rw [hq] at h
  simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_smul,
    homogeneousFullJetEvaluationMatrix_entry_eq_restriction x J hresidue,
    b, smul_eq_mul, mul_comm] using h

/-- A surjective finite matrix admits an invertible square column minor. -/
theorem exists_unit_columnMinor_of_surjective
    {K : Type u} [Field K] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ K) (hM : Function.Surjective (Matrix.toLin' M)) :
    ∃ m : ι ↪ κ, IsUnit (M.submatrix id m).det := by
  classical
  have hspan : Submodule.span K (Set.range M.col) = ⊤ := by
    rw [← Matrix.range_toLin']
    exact LinearMap.range_eq_top.mpr hM
  obtain ⟨τ, a, ha, hspan', hli⟩ := exists_linearIndependent' K M.col
  letI : Fintype τ := Fintype.ofInjective a ha
  have hselected : Submodule.span K (Set.range (M.col ∘ a)) = ⊤ := by
    rw [hspan', hspan]
  have hcard : Fintype.card τ = Fintype.card ι := by
    have hdim := finrank_span_eq_card hli
    rw [hselected, finrank_top, Module.finrank_pi] at hdim
    exact hdim.symm
  let e : ι ≃ τ := Fintype.equivOfCardEq hcard.symm
  let m : ι ↪ κ := ⟨a ∘ e, ha.comp e.injective⟩
  have hli_m : LinearIndependent K (fun j : ι => M.col (m j)) := hli.comp e e.injective
  have hli_minor : LinearIndependent K (M.submatrix id m).col := by
    convert hli_m using 1
    funext j i
    rfl
  exact ⟨m, (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hli_minor)⟩

theorem exists_unit_homogeneousFullJetEvaluationMinor_of_fullJets
    {K : Type u} [Field K]
    (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J)) :
    ∃ m : CubicFullJetCondition ↪ Monomials (Fin 4) 3,
      IsUnit (homogeneousFullJetEvaluationMinor m x (fun i j => (J i j).snd)).det :=
  exists_unit_columnMinor_of_surjective _
    (homogeneousFullJetEvaluationMatrix_surjective_of_fullJets x J hresidue hfull)

end PfaffianDescent
