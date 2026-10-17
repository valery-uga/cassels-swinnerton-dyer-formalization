import PfaffianDescent.QuarticAffineTangentSelection

/- SOURCE ONLY / UNVERIFIED. The actual affine trace construction retains
its quotient AND the jet it defines. No q/jet equality certificate is supplied. -/
namespace PfaffianDescent.QuarticNet
open MvPolynomial Module AlgebraicGeometry
universe u

/-- Strengthened selection: the very same q produces the displayed tangent
v via evalEquiv. Its trace equation is retained, rather than discarded. -/
theorem good_affine_tangent_direction_with_trace_quotient
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (b : Basis (Fin 4) K L) (hb : b 0 = 1) (F : AffineThreeRing K)
    (hF : affineDifferential (fun i : Fin 3 => b i.succ) F ≠ 0) :
    let p := fun i : Fin 3 => b i.succ
    let T := LinearMap.ker (affineDifferential p F)
    let phi := affineQuadricCotangentRestriction p F
    ∃ q : Module.Dual L T →ₗ[L] L,
      Function.Surjective q ∧
      (Algebra.trace K L).comp ((q.restrictScalars K).comp phi) = 0 ∧
      let v := (Module.evalEquiv L T).symm q
      v ≠ 0 ∧
      3 ≤ finrank K (LinearMap.ker ((q.restrictScalars K).comp phi)) ∧
      3 ≤ finrank K (affineJetQuadrics (k := K) p v.val) ∧
      ∀ Q : affineQuadricsThroughPoint (k := K) p,
        (affineFirstJet p v.val (affineQuadrics Q.val)).snd = q (phi Q) := by
  classical
  let p := fun i : Fin 3 => b i.succ
  let T := LinearMap.ker (affineDifferential p F)
  let phi := affineQuadricCotangentRestriction p F
  have hL : finrank K L = 4 := by simpa using finrank_eq_card_basis b
  have hE : finrank L (Module.Dual L T) = 2 := by
    rw [Subspace.dual_finrank_eq]
    exact affineTangentSpace_finrank p F hF
  obtain ⟨q, hq, htrace, hdim⟩ := quotient_with_large_kernel phi hL hE
    (affineQuadricsThroughPoint_finrank b hb)
  let v : T := (Module.evalEquiv L T).symm q
  have hv : v ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := hq 1
    have he := Module.apply_evalEquiv_symm_apply L T x q
    change x v = q x at he
    rw [hz, map_zero, hx] at he
    exact zero_ne_one he
  have hjet (Q : affineQuadricsThroughPoint (k := K) p) :
      (affineFirstJet p v.val (affineQuadrics Q.val)).snd = q (phi Q) := by
    have he : (phi Q) v = q (phi Q) := Module.apply_evalEquiv_symm_apply L T (phi Q) q
    rw [affineFirstJet_snd]
    exact he
  have hquad : 3 ≤ finrank K (affineJetQuadrics (k := K) p v.val) := by
    let g := (q.restrictScalars K).comp phi
    let inclusion : LinearMap.ker g →ₗ[K] affineJetQuadrics (k := K) p v.val :=
      { toFun Q := ⟨Q.val.val, by
          apply (affineFirstJet_eq_zero_iff p v.val (affineQuadrics Q.val.val)).mpr
          refine ⟨Q.val.property, ?_⟩
          have he : (phi Q.val) v = q (phi Q.val) :=
            Module.apply_evalEquiv_symm_apply L T (phi Q.val) q
          exact he.trans Q.property⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    have hinj : Function.Injective inclusion := by
      intro Q R h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : affineJetQuadrics (k := K) p v.val => z.val) h
    exact hdim.trans (LinearMap.finrank_le_finrank_of_injective hinj)
  exact ⟨q, hq, htrace, hv, hdim, hquad, hjet⟩

end PfaffianDescent.QuarticNet
