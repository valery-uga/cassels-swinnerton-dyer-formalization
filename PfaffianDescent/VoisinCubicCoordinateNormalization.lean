import PfaffianDescent.VoisinGenericTransverseLine
import PfaffianDescent.PolynomialLinearChange
import AllCharacteristics.SmoothCubicTangent
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-!
# Normalizing a smooth cubic coordinate point

An invertible linear change sends the first and fourth coordinate vectors to
a smooth cubic point and a transverse direction.  This transports the
normalized generic-line theorem back to arbitrary coordinates.
-/

namespace PfaffianDescent

open MvPolynomial Polynomial
open AllCharacteristics

universe u

private abbrev e0 (K : Type u) [Field K] : Fin 4 → K := Pi.single 0 1
private abbrev e3 (K : Type u) [Field K] : Fin 4 → K := Pi.single 3 1

/-- Two independent target vectors can be prescribed as the first and fourth
columns of an invertible `4 × 4` matrix. -/
theorem exists_invertible_matrix_mulVec_e0_e3
    {K : Type u} [Field K] (p d : Fin 4 → K)
    (hpd : LinearIndependent K ![d, p]) :
    ∃ M : Matrix (Fin 4) (Fin 4) K,
      IsUnit M.det ∧ M.mulVec (e0 K) = p ∧ M.mulVec (e3 K) = d := by
  classical
  let source : Fin 2 → (Fin 4 → K) := ![e3 K, e0 K]
  have hs : LinearIndependent K source := by
    rw [linearIndependent_fin2]
    constructor
    · intro h
      have := congrFun h 0
      simpa [source, e0] using this
    · intro a h
      have := congrFun h 3
      simpa [source, e0, e3] using this
  let target : Fin 2 → (Fin 4 → K) := ![d, p]
  have ht : LinearIndependent K target := by simpa [target] using hpd
  let f := hs.linearCombinationEquiv.symm ≪≫ₗ ht.linearCombinationEquiv
  let W := Submodule.span K (Set.range source)
  let W' := Submodule.span K (Set.range target)
  have hfinite : FiniteDimensional K W := by
    exact FiniteDimensional.of_injective W.subtype Subtype.val_injective
  letI : FiniteDimensional K W := hfinite
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hsource0 : source 1 ∈ W := Submodule.subset_span (Set.mem_range_self 1)
  have hsource3 : source 0 ∈ W := Submodule.subset_span (Set.mem_range_self 0)
  have htarget0 : target 1 ∈ W' := Submodule.subset_span (Set.mem_range_self 1)
  have htarget3 : target 0 ∈ W' := Submodule.subset_span (Set.mem_range_self 0)
  have hcombSource0 :
      hs.linearCombinationEquiv (Finsupp.single 1 1) = ⟨source 1, hsource0⟩ := by
    apply Subtype.ext
    simp
  have hcombSource3 :
      hs.linearCombinationEquiv (Finsupp.single 0 1) = ⟨source 0, hsource3⟩ := by
    apply Subtype.ext
    simp
  have hcombTarget0 :
      ht.linearCombinationEquiv (Finsupp.single 1 1) = ⟨target 1, htarget0⟩ := by
    apply Subtype.ext
    simp
  have hcombTarget3 :
      ht.linearCombinationEquiv (Finsupp.single 0 1) = ⟨target 0, htarget3⟩ := by
    apply Subtype.ext
    simp
  have hf0 : f ⟨source 1, hsource0⟩ = ⟨target 1, htarget0⟩ := by
    rw [← hcombSource0, ← hcombTarget0]
    simp [f]
  have hf3 : f ⟨source 0, hsource3⟩ = ⟨target 0, htarget3⟩ := by
    rw [← hcombSource3, ← hcombTarget3]
    simp [f]
  have hg0 : g (e0 K) = p := by
    have h := hg ⟨source 1, hsource0⟩
    rw [hf0] at h
    simpa [source, target] using h.symm
  have hg3 : g (e3 K) = d := by
    have h := hg ⟨source 0, hsource3⟩
    rw [hf3] at h
    simpa [source, target] using h.symm
  let M := LinearMap.toMatrix' g.toLinearMap
  refine ⟨M, ?_, ?_, ?_⟩
  · simpa [M] using LinearEquiv.isUnit_det g (Pi.basisFun K (Fin 4))
      (Pi.basisFun K (Fin 4))
  · change (LinearMap.toMatrix' g.toLinearMap).mulVec (e0 K) = p
    rw [LinearMap.toMatrix'_mulVec]
    change g (e0 K) = p
    exact hg0
  · change (LinearMap.toMatrix' g.toLinearMap).mulVec (e3 K) = d
    rw [LinearMap.toMatrix'_mulVec]
    change g (e3 K) = d
    exact hg3

/-- A point with a nonzero tangent derivative and the chosen tangent direction
form an independent pair. -/
theorem linearIndependent_direction_point_of_mixed_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4) (p d : Fin 4 → K)
    (hp0 : p ≠ 0) (hp : c.eval p = 0) (hd : c.mixed p d ≠ 0) :
    LinearIndependent K ![d, p] := by
  rw [linearIndependent_fin2]
  refine ⟨hp0, ?_⟩
  intro a h
  change a • p = d at h
  apply hd
  rw [← h, Cubic.mixed_smul_right, Cubic.mixed_self_eq_three_eval, hp,
    mul_zero, mul_zero]

/-- The polynomial represented by a cubic tensor commutes with linear
coordinate substitution. -/
theorem Cubic.toMvPolynomial_compLinear
    {K : Type u} [Field K] [Infinite K]
    (c : Cubic K 4) (M : Matrix (Fin 4) (Fin 4) K) :
    (c.compLinear M).toMvPolynomial = linearSubstitution M c.toMvPolynomial := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x (c.compLinear M).toMvPolynomial =
    MvPolynomial.aeval x (linearSubstitution M c.toMvPolynomial)
  rw [linearSubstitution_eval]
  change MvPolynomial.eval₂ (RingHom.id K) x (c.compLinear M).toMvPolynomial = _
  rw [Cubic.eval_toMvPolynomial]
  have hmap : (c.compLinear M).map (RingHom.id K) = c.compLinear M := by
    funext i
    rfl
  rw [hmap, Cubic.eval_compLinear]
  symm
  change MvPolynomial.eval₂ (RingHom.id K) (M.mulVec x) c.toMvPolynomial =
    c.eval (M.mulVec x)
  have h := Cubic.eval_toMvPolynomial (RingHom.id K) c (M.mulVec x)
  have hmapc : c.map (RingHom.id K) = c := by funext i; rfl
  rwa [hmapc] at h

/-- Restriction of a cubic to a line commutes with a linear coordinate
change. -/
theorem cubicLinePolynomial_compLinear
    {K : Type u} [Field K] [Infinite K]
    (c : Cubic K 4) (M : Matrix (Fin 4) (Fin 4) K)
    (a b : Fin 4 → K) :
    AllCharacteristics.cubicLinePolynomial (c.compLinear M) a b =
      AllCharacteristics.cubicLinePolynomial c (M.mulVec a) (M.mulVec b) := by
  apply Polynomial.funext
  intro t
  change (AllCharacteristics.cubicLinePolynomial (c.compLinear M) a b).eval₂
      (RingHom.id K) t =
    (AllCharacteristics.cubicLinePolynomial c (M.mulVec a) (M.mulVec b)).eval₂
      (RingHom.id K) t
  rw [AllCharacteristics.cubicLinePolynomial_eval₂,
    AllCharacteristics.cubicLinePolynomial_eval₂,
    show Cubic.map (RingHom.id K) (c.compLinear M) = c.compLinear M by
      funext i; rfl,
    show Cubic.map (RingHom.id K) c = c by funext i; rfl,
    Cubic.eval_compLinear]
  congr 1
  simp [Matrix.mulVec_add, Matrix.mulVec_smul]

/-- An irreducible cubic with a smooth coordinate point has a transverse
affine line section, without any normalization hypothesis. -/
theorem exists_separable_cubic_line_of_irreducible_at_smooth_point
    {K : Type u} [Field K] [CharZero K] [Infinite K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    (hirrF : Irreducible F)
    (p : Fin 4 → K)
    (hs : IsSmoothCubicCoordinatePoint c.toMvPolynomial p) :
    ∃ a b : Fin 4 → K,
      c.eval a ≠ 0 ∧
        (AllCharacteristics.cubicLinePolynomial c a b).Separable := by
  classical
  obtain ⟨d, hd⟩ :=
    exists_tangent_direction_of_isSmoothCubicCoordinatePoint c p hs
  have hp : c.eval p = 0 := by
    have he := hs.2.1
    change MvPolynomial.eval₂ (RingHom.id K) p c.toMvPolynomial = 0 at he
    rw [Cubic.eval_toMvPolynomial] at he
    have hmap : c.map (RingHom.id K) = c := by funext i; rfl
    rwa [hmap] at he
  have hli : LinearIndependent K ![d, p] :=
    linearIndependent_direction_point_of_mixed_ne_zero c p d hs.1 hp hd
  obtain ⟨M, hM, hM0, hM3⟩ :=
    exists_invertible_matrix_mulVec_e0_e3 p d hli
  let c' := c.compLinear M
  let F' := linearSubstitution M F
  have hF' : F'.IsHomogeneous 3 := linearSubstitution_homogeneous M hF
  have hc' : c'.toMvPolynomial = F' := by
    rw [Cubic.toMvPolynomial_compLinear, hc]
  let E := linearSubstitutionEquiv M hM
  have hirrF' : Irreducible F' := by
    have h := hirrF.map E
    exact h
  have hMbase : M.mulVec (kollarBasePoint K) = p := by
    rw [show kollarBasePoint K = e0 K by
      funext i
      fin_cases i <;> simp [kollarBasePoint, e0]]
    exact hM0
  have hMdir :
      M.mulVec (kollarAffineLineDirection K (fun _ => 0)) = d := by
    rw [show kollarAffineLineDirection K (fun _ => 0) = e3 K by
      funext i
      fin_cases i <;> simp [kollarAffineLineDirection, e3]]
    exact hM3
  have hpoint : c'.eval (kollarBasePoint K) = 0 := by
    rw [Cubic.eval_compLinear, hMbase]
    exact hp
  have hsec : c'.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0 := by
    have hline := cubicLinePolynomial_compLinear c M
      (kollarBasePoint K) (kollarAffineLineDirection K (fun _ => 0))
    have hcoeff := congrArg (fun q : K[X] => q.coeff 2) hline
    have heq : c'.mixed (kollarBasePoint K)
        (kollarAffineLineDirection K (fun _ => 0)) = c.mixed p d := by
      simpa [c', AllCharacteristics.cubicLinePolynomial,
        Polynomial.coeff_C_mul, hMbase, hMdir] using hcoeff
    rwa [heq]
  obtain ⟨a, b, ha, hab⟩ :=
    exists_separable_cubic_line_of_normalized_irreducible
      F' hF' c' hc' hirrF' hpoint hsec
  refine ⟨M.mulVec a, M.mulVec b, ?_, ?_⟩
  · simpa [c', Cubic.eval_compLinear] using ha
  · rw [← cubicLinePolynomial_compLinear]
    exact hab

end PfaffianDescent
