import AllCharacteristics.ResidualPointSmoothness
import AllCharacteristics.TangentHyperplaneGeneric
import PfaffianDescent.CubicLineResidualConjugate

/-!
# Actual universal tangent pairs at the two generic residual roots

The separable residual quadratic constructs the extension, its nontrivial
automorphism, both cubic points, and a valid tangent pivot.  Six independent
base-field parameters then give the conjugate tangent directions.  Every
resulting secant vector lies on the cubic and is anti-invariant.  Nonvanishing
and dominance are geometric conclusions still required of the universal map.
-/

namespace AllCharacteristics

open PfaffianDescent MvPolynomial Polynomial Module

universe u

variable {K : Type u} [Field K]

/-- An actual root-valued point of the residual line. -/
noncomputable def residualLineRootPoint
    (c : Cubic K 4) (p d : Fin 4 → K)
    [Fact (Irreducible (Cubic.lineResidualPolynomial c p d))] :
    Fin 4 → AdjoinRoot (Cubic.lineResidualPolynomial c p d) :=
  (fun i => algebraMap K _ (p i)) +
    AdjoinRoot.root (Cubic.lineResidualPolynomial c p d) •
      (fun i => algebraMap K _ (d i))

/-- The universal tangent direction at that residual point, using three
parameters and three root coefficients over the base field. -/
noncomputable def residualLineWeilTangentDirection
    (c : Cubic K 4) (p d : Fin 4 → K)
    [Fact (Irreducible (Cubic.lineResidualPolynomial c p d))]
    (k : Fin 4) (u v : Fin 3 → K) :
    Fin 4 → AdjoinRoot (Cubic.lineResidualPolynomial c p d) :=
  (hyperplaneInclusion
    (fun i => (MvPolynomial.pderiv i
      (c.map (algebraMap K (AdjoinRoot (Cubic.lineResidualPolynomial c p d)))).toMvPolynomial).eval
        (residualLineRootPoint c p d)) k).mulVec
    (fun j => algebraMap K _ (u j) +
      AdjoinRoot.root (Cubic.lineResidualPolynomial c p d) * algebraMap K _ (v j))

/-- The actual residual extension supplies smooth conjugate tangent centers
and universally valid six-parameter tangent and secant coordinates. -/
theorem exists_residualLine_universal_conjugate_tangent_pair
    (c : Cubic K 4) (p d : Fin 4 → K)
    (hp : c.eval p = 0) (hsec : c.mixed p d ≠ 0) (hdir : c.eval d ≠ 0)
    (hirr : Irreducible (Cubic.lineResidualPolynomial c p d))
    (hsep : (Cubic.lineResidualPolynomial c p d).Separable) :
    letI : Fact (Irreducible (Cubic.lineResidualPolynomial c p d)) := ⟨hirr⟩
    ∃ (σ : AdjoinRoot (Cubic.lineResidualPolynomial c p d) ≃ₐ[K]
        AdjoinRoot (Cubic.lineResidualPolynomial c p d)) (k : Fin 4),
      σ ≠ AlgEquiv.refl ∧
      (MvPolynomial.pderiv k
        (c.map (algebraMap K (AdjoinRoot (Cubic.lineResidualPolynomial c p d)))).toMvPolynomial).eval
          (residualLineRootPoint c p d) ≠ 0 ∧
      ∀ u v : Fin 3 → K,
        let cL := c.map (algebraMap K (AdjoinRoot (Cubic.lineResidualPolynomial c p d)))
        let x := residualLineRootPoint c p d
        let y := fun i => σ (x i)
        let dp := residualLineWeilTangentDirection c p d k u v
        let dq := fun i => σ (dp i)
        let r := Cubic.secantResidualPoint cL
          (Cubic.tangentResidualPoint cL x dp) (Cubic.tangentResidualPoint cL y dq)
        cL.mixed x dp = 0 ∧ cL.mixed y dq = 0 ∧
          cL.eval r = 0 ∧ ∀ i, σ (r i) = -(r i) := by
  let q := Cubic.lineResidualPolynomial c p d
  letI : Fact (Irreducible q) := ⟨hirr⟩
  let L := AdjoinRoot q
  letI : FiniteDimensional K L :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hirr.ne_zero).basis
  letI : Algebra.IsSeparable K L :=
    adjoinRoot_isSeparable_of_irreducible_separable q hirr hsep
  letI : IsGalois K L :=
    adjoinRoot_isGalois_of_irreducible_separable_natDegree_two hsep
      (Cubic.lineResidualPolynomial_natDegree_eq_two c p d hdir)
  have hdim : finrank K L = 2 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    exact Cubic.lineResidualPolynomial_natDegree_eq_two c p d hdir
  obtain ⟨σ, hσ⟩ := exists_nontrivial_galois_aut_of_finrank_two hdim
  let cL := c.map (algebraMap K L)
  let x : Fin 4 → L := residualLineRootPoint c p d
  have hroot : Polynomial.eval₂ (algebraMap K L) (AdjoinRoot.root q) q = 0 := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root q
  have hx : cL.eval x = 0 :=
    Cubic.eval_linePoint_of_lineResidual_root (algebraMap K L) c p d hp _ hroot
  have hxsmooth : IsSmoothCubicCoordinatePoint cL.toMvPolynomial x :=
    isSmoothCubicCoordinatePoint_of_separable_lineResidual_root
      (algebraMap K L) c p d hp hsec hsep _ hroot
  obtain ⟨_, _, k, hk⟩ := hxsmooth
  refine ⟨σ, k, hσ, hk, ?_⟩
  intro u v
  let dp : Fin 4 → L := residualLineWeilTangentDirection c p d k u v
  let y : Fin 4 → L := fun i => σ (x i)
  let dq : Fin 4 → L := fun i => σ (dp i)
  have hfixed : cL.map σ.toRingHom = cL := cubic_map_algebraMap_fixed_by_algEquiv c σ
  have hxy : (fun i => σ (x i)) = y := rfl
  have hσsq : σ.trans σ = AlgEquiv.refl := galois_involution_of_finrank_two σ hσ hdim
  have hyx : (fun i => σ (y i)) = x := by
    funext i
    exact DFunLike.congr_fun hσsq (x i)
  have hdd : (fun i => σ (dp i)) = dq := rfl
  have hdq : (fun i => σ (dq i)) = dp := by
    funext i
    exact DFunLike.congr_fun hσsq (dp i)
  have htan : cL.mixed x dp = 0 := by
    change cL.mixed x ((hyperplaneInclusion
      (fun i => (MvPolynomial.pderiv i cL.toMvPolynomial).eval x) k).mulVec
        (fun j => algebraMap K L (u j) + AdjoinRoot.root q * algebraMap K L (v j))) = 0
    have hid : cL.map (RingHom.id L) = cL := by
      funext i
      rfl
    have h := mixed_hyperplaneInclusion_zero (RingHom.id L) cL x
      (fun i => (MvPolynomial.pderiv i cL.toMvPolynomial).eval x)
      (fun _ => rfl) k hk
      (fun j => algebraMap K L (u j) + AdjoinRoot.root q * algebraMap K L (v j))
    simp only [RingHom.coe_id, Matrix.map_id, RingHom.id_apply] at h
    rw [hid] at h
    exact h
  have htq : cL.mixed y dq = 0 := by
    have hm := Cubic.mixed_map σ.toRingHom cL x dp
    rw [hfixed] at hm
    change cL.mixed (fun i => σ (x i)) (fun i => σ (dp i)) = σ (cL.mixed x dp) at hm
    rw [hxy, hdd, htan, map_zero] at hm
    exact hm
  have hy : cL.eval y = 0 := by
    have hm := Cubic.eval_map σ.toRingHom cL x
    rw [hfixed] at hm
    change cL.eval (fun i => σ (x i)) = σ (cL.eval x) at hm
    rw [hxy, hx, map_zero] at hm
    exact hm
  refine ⟨htan, htq, ?_, ?_⟩
  · exact Cubic.eval_secantResidualPoint cL _ _
      (Cubic.eval_tangentResidualPoint cL x dp hx htan)
      (Cubic.eval_tangentResidualPoint cL y dq hy htq)
  · intro i
    exact congrFun (Cubic.map_twoTangentSecantResidual_eq_neg_of_conjugate
      σ.toRingHom cL x y dp dq hfixed hxy hyx hdd hdq) i

end AllCharacteristics
