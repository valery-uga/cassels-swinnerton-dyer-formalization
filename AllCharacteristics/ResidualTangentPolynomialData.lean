import AllCharacteristics.UniversalConjugateTangentPair
import AllCharacteristics.UniversalSecantPolynomialDescent
import AllCharacteristics.UniversalSecantPolynomialCubic
import AllCharacteristics.PolynomialSecantDescentCubic

namespace AllCharacteristics

open PfaffianDescent MvPolynomial Polynomial Module

universe u

variable {K : Type u} [Field K]

/-- The fixed tangent matrix used for the raw universal polynomial at the
actual residual root point. -/
noncomputable def residualLineTangentMatrix
    (c : Cubic K 4) (p d : Fin 4 → K)
    [Fact (Irreducible (Cubic.lineResidualPolynomial c p d))] (k : Fin 4) :
    Matrix (Fin 4) (Fin 3) (AdjoinRoot (Cubic.lineResidualPolynomial c p d)) :=
  hyperplaneInclusion
    (fun i => (MvPolynomial.pderiv i
      (c.map (algebraMap K (AdjoinRoot (Cubic.lineResidualPolynomial c p d)))).toMvPolynomial).eval
        (residualLineRootPoint c p d)) k

/-- The canonical six-variable raw secant family for a chosen residual
involution and a nonzero gradient pivot. -/
noncomputable def residualLineUniversalSecantPolynomial
    (c : Cubic K 4) (p d : Fin 4 → K)
    [Fact (Irreducible (Cubic.lineResidualPolynomial c p d))]
    (σ : AdjoinRoot (Cubic.lineResidualPolynomial c p d) ≃ₐ[K]
      AdjoinRoot (Cubic.lineResidualPolynomial c p d)) (k : Fin 4) :
    Fin 4 → MvPolynomial ConjugateTangentParameterIndex
      (AdjoinRoot (Cubic.lineResidualPolynomial c p d)) :=
  universalTwoTangentSecantPolynomial
    (c.map (algebraMap K (AdjoinRoot (Cubic.lineResidualPolynomial c p d))))
    (residualLineRootPoint c p d) (fun i => σ (residualLineRootPoint c p d i))
    (residualLineTangentMatrix c p d k) ((residualLineTangentMatrix c p d k).map σ)
    (AdjoinRoot.root (Cubic.lineResidualPolynomial c p d))
    (σ (AdjoinRoot.root (Cubic.lineResidualPolynomial c p d)))

/-- Actual tangent columns for the explicitly solved gradient hyperplane. -/
theorem mixed_hyperplaneInclusion_column_eq_zero
    {L : Type u} [Field L] (c : Cubic L 4) (x : Fin 4 → L)
    (k : Fin 4) (hk : (MvPolynomial.pderiv k c.toMvPolynomial).eval x ≠ 0)
    (j : Fin 3) :
    c.mixed x (fun i => hyperplaneInclusion
      (fun l => (MvPolynomial.pderiv l c.toMvPolynomial).eval x) k i j) = 0 := by
  let g := fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval x
  have hid : c.map (RingHom.id L) = c := by funext i; rfl
  have h := mixed_hyperplaneInclusion_zero (RingHom.id L) c x g (fun _ => rfl)
    k hk (Pi.single j 1)
  simp only [RingHom.coe_id, Matrix.map_id, RingHom.id_apply] at h
  rw [hid] at h
  rw [Matrix.mulVec_single_one] at h
  change c.mixed x (fun i => hyperplaneInclusion
    (fun l => (MvPolynomial.pderiv l c.toMvPolynomial).eval x) k i j) = 0 at h
  exact h

/-- The actual residual Galois extension and a valid tangent pivot construct
the descended polynomial family over the generic line field.  Every scalar
and polynomial coefficient relation is retained; nonvanishing and dominance
are supplied separately by the geometric preimage argument. -/
theorem exists_descended_residualLineUniversalSecantPolynomial
    (c : Cubic K 4) (p d : Fin 4 → K)
    (hp : c.eval p = 0) (hdir : c.eval d ≠ 0)
    (hirr : Irreducible (Cubic.lineResidualPolynomial c p d))
    (hsep : (Cubic.lineResidualPolynomial c p d).Separable)
    [Fact (Irreducible (Cubic.lineResidualPolynomial c p d))]
    (σ : AdjoinRoot (Cubic.lineResidualPolynomial c p d) ≃ₐ[K]
      AdjoinRoot (Cubic.lineResidualPolynomial c p d)) (hσ : σ ≠ AlgEquiv.refl)
    (k : Fin 4)
    (hk : (MvPolynomial.pderiv k
      (c.map (algebraMap K (AdjoinRoot (Cubic.lineResidualPolynomial c p d)))).toMvPolynomial).eval
        (residualLineRootPoint c p d) ≠ 0) :
    ∃ (s : AdjoinRoot (Cubic.lineResidualPolynomial c p d))
      (R : Fin 4 → MvPolynomial ConjugateTangentParameterIndex K),
      s ≠ 0 ∧
      (∀ i, MvPolynomial.map (algebraMap K (AdjoinRoot (Cubic.lineResidualPolynomial c p d)))
        (R i) = MvPolynomial.C s * residualLineUniversalSecantPolynomial c p d σ k i) ∧
      (c.map MvPolynomial.C).eval R = 0 := by
  let q := Cubic.lineResidualPolynomial c p d
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
  let cL := c.map (algebraMap K L)
  let x : Fin 4 → L := residualLineRootPoint c p d
  let y : Fin 4 → L := fun i => σ (x i)
  let M := residualLineTangentMatrix c p d k
  let N := M.map σ
  let a : L := AdjoinRoot.root q
  let b : L := σ a
  let r := residualLineUniversalSecantPolynomial c p d σ k
  have hfixed : cL.map σ.toRingHom = cL := cubic_map_algebraMap_fixed_by_algEquiv c σ
  have hσsq : σ.trans σ = AlgEquiv.refl := galois_involution_of_finrank_two σ hσ hdim
  have hyx : (fun i => σ (y i)) = x := by
    funext i
    exact DFunLike.congr_fun hσsq (x i)
  have hNM : N.map σ = M := by
    ext i j
    exact DFunLike.congr_fun hσsq (M i j)
  have hba : σ b = a := DFunLike.congr_fun hσsq a
  have hroot : Polynomial.eval₂ (algebraMap K L) a q = 0 := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root q
  have hx : cL.eval x = 0 :=
    Cubic.eval_linePoint_of_lineResidual_root (algebraMap K L) c p d hp a hroot
  have hy : cL.eval y = 0 := by
    have h := Cubic.eval_map σ.toRingHom cL x
    rw [hfixed] at h
    change cL.eval y = σ (cL.eval x) at h
    rw [hx, map_zero] at h
    exact h
  have hM : ∀ j, cL.mixed x (fun i => M i j) = 0 := by
    intro j
    exact mixed_hyperplaneInclusion_column_eq_zero cL x k hk j
  have hN : ∀ j, cL.mixed y (fun i => N i j) = 0 := by
    intro j
    have h := Cubic.mixed_map σ.toRingHom cL x (fun i => M i j)
    rw [hfixed] at h
    change cL.mixed y (fun i => N i j) = σ (cL.mixed x (fun i => M i j)) at h
    rw [hM j, map_zero] at h
    exact h
  have hr : ((c.map (algebraMap K L)).map MvPolynomial.C).eval r = 0 :=
    eval_universalTwoTangentSecantPolynomial_eq_zero cL x y hx hy M N hM hN a b
  have hranti : ∀ i, MvPolynomial.map σ.toRingHom (r i) = -(r i) := by
    intro i
    exact congrFun (universalTwoTangentSecantPolynomial_antiInvariant σ cL x y M N a b
      hfixed rfl hyx rfl hNM rfl hba) i
  obtain ⟨s, R, hs, hR⟩ := exists_polynomial_vector_of_scaled_antiInvariant σ hσ hdim r hranti
  exact ⟨s, R, hs, hR, eval_descended_polynomial_cubic_point_eq_zero c r R s hR hr⟩

end AllCharacteristics
